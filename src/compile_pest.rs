use log::{debug, error, info, log_enabled, warn, Level};

use inkwell::context::Context;
use inkwell::intrinsics::Intrinsic;
use inkwell::llvm_sys::prelude::LLVMValueRef;
use inkwell::module::{Linkage, Module};
use inkwell::passes::PassManager;
use inkwell::{
    passes::PassBuilderOptions,
    targets::{CodeModel, InitializationConfig, RelocMode, Target, TargetMachine},
};
use inkwell::{AddressSpace, OptimizationLevel};

use inkwell::builder::Builder;
use inkwell::types::{
    BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FunctionType, PointerType, StructType,
};
use inkwell::values::{
    AsValueRef, BasicMetadataValueEnum, BasicValue, BasicValueEnum, FloatValue, FunctionValue,
    InstructionOpcode, InstructionValue, PointerValue, StructValue,
};
use inkwell::FloatPredicate;

use itertools::Itertools;
use pest::iterators::{Pair, Pairs};
use pest::Parser;

use std::collections::{HashMap, VecDeque};
use std::hint::unreachable_unchecked;

use super::{Codegen, Type};
use crate::parse::{parse_expr, parse_literal, simple_expr_str, Expr, FCParser, Rule, PRATT_PARSER};
use crate::{print_pair, print_pairs};

impl<'a, 'ctx> Codegen<'a, 'ctx>
where
    'ctx: 'a,
{
    pub(crate) fn compile_pest_output(&mut self, pair: Pair<Rule>) {
        //println!("compile_pest_output({})",pair.to_string());
        use Rule as R;
        let rule = pair.as_rule();
        info!("compiling rule {rule}");
        match rule {
            R::expr => {
                let exp = parse_expr(pair.into_inner());
                self.compile_expr(exp);
            }
            R::whlstmt => {
                let mut i = pair.into_inner();
                let cur_func = self
                    .builder
                    .get_insert_block()
                    .unwrap()
                    .get_parent()
                    .unwrap();
                //let checkblock = self.context.append_basic_block(cur_func, "check");
                let contblock = self.context.append_basic_block(cur_func, "contblock");
                let body = self.context.append_basic_block(cur_func, "whileblock");
                let expr = parse_expr(i.next().unwrap().into_inner());
                let compiled_expr = self.compile_expr(expr.clone()).unwrap().into_int_value();
                //self.builder.build_unconditional_branch(checkblock);
                //self.builder.position_at_end(checkblock);
                self.builder
                    .build_conditional_branch(compiled_expr, body, contblock);
                self.builder.position_at_end(body);
                self.compile_pest_output(i.next().unwrap());
                let compiled_expr = self.compile_expr(expr).unwrap().into_int_value();
                self.builder
                    .build_conditional_branch(compiled_expr, body, contblock);
                self.builder.position_at_end(contblock);
            }
            R::ifstmt => {
                let mut i = pair.into_inner();
                let cur_func = self
                    .builder
                    .get_insert_block()
                    .unwrap()
                    .get_parent()
                    .unwrap();
                let contblock = self.context.append_basic_block(cur_func, "contblock");
                loop {
                    match (i.next(), i.next()) {
                        (Some(ifthat), Some(dothis)) => {
                            //println!("if {ifthat:#?} then {dothis:#?}");
                            let mut thenblock =
                                self.context.append_basic_block(cur_func, "thenblock");
                            let mut elseblock =
                                self.context.append_basic_block(cur_func, "elseblock");
                            let cond = parse_expr(ifthat.into_inner());
                            let cond = self.compile_expr(cond).unwrap().into_int_value();
                            self.builder
                                .build_conditional_branch(cond, thenblock, elseblock);
                            self.builder.position_at_end(thenblock);
                            self.compile_pest_output(dothis);
                            // if thenblock has return statement, then the line below adds br after
                            // ret... this will cause error
                            if self
                                .builder
                                .get_insert_block()
                                .unwrap()
                                .get_terminator()
                                .is_none()
                            {
                                self.builder.build_unconditional_branch(contblock);
                            }
                            self.builder.position_at_end(elseblock);
                        }
                        (Some(dothis), None) => {
                            //println!("else");
                            self.compile_pest_output(dothis);
                            break;
                        }
                        _ => break,
                    }
                }
                //
                // if elseblock has return statement, then the line below adds br after
                // ret... this will cause error
                if self
                    .builder
                    .get_insert_block()
                    .unwrap()
                    .get_terminator()
                    .is_none()
                {
                    self.builder.build_unconditional_branch(contblock);
                }
                self.builder.position_at_end(contblock);
            }
            R::asgnstmt => {
                let mut i = pair.into_inner();
                let next = i.next().unwrap();
                let expr = parse_expr(i.next().unwrap().into_inner());
                let etyp = self.expr_type(&expr);
                let compiled_expr = self.compile_expr(expr).expect("void assignment");
                let func = self
                    .builder
                    .get_insert_block()
                    .unwrap()
                    .get_parent()
                    .unwrap();

                let (var_ptr, var_typ) = match next.as_rule() {
                    // R::dot_arg => {
                    //     let mut inner = next.into_inner();
                    //     let name = inner.next().unwrap().as_str().to_string();
                    //     let (ptr, typ): (PointerValue<'ctx>, Type) =
                    //         self.locals.get(&(func, name)).unwrap().clone();
                    //     let index = parse_expr(inner.next().unwrap().into_inner());
                    //     let index = self
                    //         .compile_expr(index)
                    //         .expect("index cannot be void/nil")
                    //         .into_int_value();
                    //     let (inner_typ, fields, struct_name) = match &typ {
                    //         //Type::Array(one, size, body) => body.as_ref().clone(),
                    //         Type::StructType(implementation_level, struct_name, _) => {
                    //             let (styp, field_names) = self.struct_defs.get(&(struct_name.clone(), *implementation_level)).unwrap();
                    //             (styp, field_names, struct_name.clone())
                    //         }
                    //         _ => unreachable!(),
                    //     };
                    //     let elm_ptr = unsafe {
                    //         self.builder
                    //             .build_struct_gep(
                    //                 inner_typ.clone(),
                    //                 ptr,
                    //                 fields.iter().fold_while(0, |a, (s, t)|{
                    //                     use itertools::FoldWhile::{Done, Continue};
                    //                     if (s==&struct_name){
                    //                         Done(a)
                    //                     } else {
                    //                         Continue(a+1)
                    //                     }
                    //                 }).into_inner(),
                    //                 "getelementptr",
                    //             )
                    //             .unwrap()
                    //     };
                    //     (elm_ptr, typ)
                    // }
                    // R::ident => self
                    //     .locals
                    //     .get(&(func, next.as_str().to_string()))
                    //     .unwrap()
                    //     .clone(),
                    R::linear_expr => {
                        let mut i = next.into_inner();
                        let first = i.next().unwrap();
                        let mut expr = match first.as_rule(){
                            R::expr => parse_expr(first.into_inner()),
                            R::ident => Expr::Ident(first.as_str().to_string()),

                            // TODO: this, the statement hereunder, is not enforced correctly...
                            // at this point, 'other' should ONLY be literal
                            other => {
                                parse_literal(first)
                            }
                        }; 
                        while let Some(pair) = i.next(){
                            expr = match pair.as_rule(){
                                R::dot_arg => Expr::Pathident(Box::new(expr), pair.into_inner().next().unwrap().as_str().to_string()),
                                R::square_brackets_args => todo!("square bracket args (e.g.: this[thing]) is not yet implemented"),
                                R::round_brackets_args => {
                                    let j = pair.into_inner();
                                    Expr::RoundArgs(Box::new(expr), j.map(|x|parse_expr(x.into_inner())).collect())
                                },

                                other => unimplemented!("{other} is incorrect in this stage: parsing linear expression after the first element")
                            }
                        }
                        self.compile_lvalue_expr(expr, self.builder.get_insert_block().unwrap().get_parent().unwrap())
                    }
                    other => unreachable!("reached {other}"),
                };
                if let (Type::Ptr(_), Type::Int) = (var_typ.clone(), etyp) {
                    todo!("implement assign int to ptr")
                } else {
                    let load_instr = self
                        .builder
                        .build_store(var_ptr.clone(), compiled_expr)
                        .unwrap();
                    // load_instr
                    //     .set_alignment(var_typ.correct_alignment(self.struct_defs))
                    //     .unwrap();
                }
            }
            R::retstmt => {
                let exp = pair.into_inner();
                let exp = parse_expr(exp);
                if exp.is_nil() {
                    todo!("NIL return is not supported yet")
                }
                let ibl = self.builder.get_insert_block().unwrap();
                let bname = ibl.get_name().to_str();
                if bname.unwrap() == "mainf_entry" {
                    let etyp = Self::raw_expr_type(
                        self.context,
                        self.locals,
                        self.functions,
                        self.struct_defs,
                        &self
                            .builder
                            .get_insert_block()
                            .unwrap()
                            .get_parent()
                            .unwrap(),
                        &exp,
                    );
                    if etyp != Type::Int {
                        panic!("main return should be int, but type {etyp:#?} was found instead")
                    }
                }
                // self.builder.build_return(self.compile_expr(exp).map(|x|&x)); <-- WHY DOESNT THIS WORK!??!?
                if let Some(compiled_exp) = self.compile_expr(exp) {
                    self.builder.build_return(Some(&compiled_exp));
                } else {
                    self.builder.build_return(None);
                }
            }
            R::typealias => todo!(),
            R::procedure_def => {
                let mut i = pair.into_inner();
                let name = i.next().unwrap().as_str(); //
                let func = self.module.get_function(name).unwrap();
                self.builder
                    .position_at_end(func.get_first_basic_block().unwrap());
                while let Some(x) = i.next() {
                    match x.as_rule() {
                        R::algoritma => self.compile_pest_output(x),
                        R::integer_type
                        | R::konstanta
                        | R::kamus
                        | R::real_type
                        | R::char_type
                        | R::void_type
                        | R::bool_type
                        | R::pointer_type
                        | R::user_type
                        | R::parameter
                        | R::string_type
                        | R::array_type => continue,
                        _ => unreachable!(),
                    }
                }
                self.builder.build_return(None);
            }
            R::function_def => {
                let mut i = pair.into_inner();
                let name = i.next().unwrap().as_str(); //
                assert!(name != "main", "non-main function cannot be named main, too");
                let func = self.module.get_function(name).unwrap();
                self.builder
                    .position_at_end(func.get_first_basic_block().unwrap());
                while let Some(x) = i.next() {
                    match x.as_rule() {
                        R::algoritma => self.compile_pest_output(x),
                        R::integer_type
                        | R::konstanta
                        | R::kamus
                        | R::real_type
                        | R::char_type
                        | R::void_type
                        | R::bool_type
                        | R::pointer_type
                        | R::user_type
                        | R::parameter
                        | R::string_type
                        | R::array_type => continue,
                        _ => unreachable!("{:?} is not an acceptable type", x.as_rule()),
                    }
                }
                self.builder.build_return(None);
            }
            R::mainprogram => {
                let main_fn = self.module.get_function("main").unwrap();
                let entry = main_fn.get_first_basic_block().unwrap();
                self.builder.position_at_end(entry);
                let mut i = pair.into_inner();
                let program_name = i.next().unwrap().as_str().to_string();
                let _ = i.map(|p| self.compile_pest_output(p)).collect::<Vec<()>>();
            }
            R::konstanta | R::kamus => return,
            R::algoritma | R::stmt0 | R::stmt1 => {
                let _ = pair
                    .into_inner()
                    .map(|p| self.compile_pest_output(p))
                    .collect::<Vec<()>>();
            }
            R::type_def => {
                return //wot!?
            }
            _ => unreachable!("reached rule {}", pair.as_rule().to_string()),
        }
    }
}
