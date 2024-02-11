//
//
//
//
// TODO
// use phi nodes cuz apparently it's important
//
//
//
//
//
//
use inkwell::context::Context;
use inkwell::intrinsics::Intrinsic;
use inkwell::llvm_sys::prelude::LLVMValueRef;
use inkwell::module::{Module, Linkage};
use inkwell::passes::PassManager;
use inkwell::{OptimizationLevel, AddressSpace};
use inkwell::{
    passes::PassBuilderOptions,
    targets::{CodeModel, InitializationConfig, RelocMode, Target, TargetMachine},
};

use inkwell::builder::Builder;
use inkwell::types::{BasicMetadataTypeEnum, FunctionType, BasicTypeEnum, BasicType};
use inkwell::values::{BasicMetadataValueEnum, BasicValueEnum, FloatValue, FunctionValue, PointerValue, BasicValue, InstructionOpcode, AsValueRef, InstructionValue};
use inkwell::FloatPredicate;

use pest::Parser;
use pest::iterators::{Pairs, Pair};
use itertools::Itertools;

use std::collections::{HashMap, VecDeque};
use std::hint::unreachable_unchecked;

use crate::parse::{PRATT_PARSER, FCParser, Rule, parse_expr, Expr};
use crate::{print_pairs, print_pair};

#[derive(Debug)]
pub struct Codegen<'a, 'ctx> {
    pub context: &'ctx Context,
    pub module: &'a Module<'ctx>,
    pub builder: &'a Builder<'ctx>,
    pub functions: &'a mut HashMap<String, Vec<FunctionValue<'ctx>>>,
    pub locals: &'a mut HashMap<(FunctionValue<'ctx>,String), (PointerValue<'ctx>,BasicTypeEnum<'ctx>)>,
    pub paramstack: &'a mut HashMap<String, BasicValueEnum<'ctx>>,
    // pub program_name: String,
}

impl<'a, 'ctx> Codegen<'a, 'ctx> where 'ctx:'a{
    fn add_function(&self, name: &'ctx str, ftype: FunctionType<'ctx>, linkage: Option<Linkage>)->FunctionValue<'ctx>{
        let f = self.module.add_function(name, ftype, linkage);
        //self.functions.insert(name, f);    
        return f;
    }
    fn find_function(&self, name: &str, argtypes: &[BasicTypeEnum]) -> Option<FunctionValue<'ctx>>{
        let mut funcs = self.functions.get(&name.to_string())?.clone();
        funcs.sort_by(|a,b|{
            b.get_params().len().cmp(&a.get_params().len())
        });
        let func = funcs.iter().find(|&e|{
            let fargtypes = e.get_params().iter()
                .map(|p|
                    p.get_type()
                ).collect::<Vec<_>>();
            //println!("matching >>>\n{fargtypes:?}\nwith >>>\n{argtypes:?}\n >>>");
            if fargtypes.len()>argtypes.len(){ return false }
            if (!e.get_type().is_var_arg()) && fargtypes.len()!=argtypes.len(){ return false }
            if &fargtypes == &argtypes[..fargtypes.len()]{
                //println!("matched!");
                return true
            }
            return false
        }).unwrap();
        Some(*func)
    }
    #[inline]
    fn pair_to_type(context: &'ctx Context, pair: Pair<Rule>) -> BasicTypeEnum<'ctx>{
        match pair.as_rule(){
            Rule::integer_type => context.i64_type().into(),
            Rule::real_type => context.f64_type().into(),
            Rule::bool_type => context.bool_type().into(),
            Rule::pointer_type => Self::pair_to_type(context, pair.into_inner().next().unwrap()).ptr_type(AddressSpace::default()).into(),
            _ => unreachable!()
        }
    }
    fn pair_to_value(&self, pair:Pair<Rule>) -> BasicValueEnum{
        match pair.as_rule(){
            Rule::float => self.context.f64_type().const_float(pair.into_inner().next().unwrap().as_str().parse().unwrap()).into(),
            Rule::int => self.context.i64_type().const_int(
                pair.into_inner().next().unwrap().as_str().parse::<i64>().unwrap() as u64, false).into(),
            Rule::bool => self.context.bool_type().const_int(
                pair.into_inner().next().unwrap().as_str().parse::<bool>().unwrap() as u64, false).into(),
            _ => unreachable!(),
        }
    }
    pub fn compile_program(&mut self, source_filename: &str){
        let code = std::fs::read_to_string(source_filename).unwrap();
        let parsed = FCParser::parse(Rule::program, &code).unwrap();
        print_pairs(parsed.clone(), 0);
        let main_type = self.context.i64_type().fn_type(&[], false);
        let main_fn = self.add_function("main", main_type, None);
        self.context.append_basic_block(main_fn, "mainf_entry");

        self.add_printf();
        self.add_output();
        // self.add_powi();
        // self.add_powf();
        let _ = parsed.clone().map(|p|self.declare_funcs(p)).collect::<Vec<()>>();
        println!("done declare_funcs(...)... now, locals is:");
        println!("{:#?}",self.locals);
        let _ = parsed.map(|p|self.compile_pest_output(p)).collect::<Vec<()>>();
    }
    
    fn process_parameter(context: &'ctx Context, pair:Pair<Rule>)->(bool,bool,Vec<String>,BasicTypeEnum<'ctx>){
        if pair.as_rule()!=Rule::parameter{
            unreachable!()
        }
        let mut i = pair.into_inner();
        let mut invar = false;
        let mut outvar = false;
        let mut vars: Vec<_> = vec![];
        let mut partype = context.i8_type().as_basic_type_enum();
        while let Some(x) = i.next(){
            match x.as_rule(){
                Rule::param_io => {
                    let s = x.as_str();
                    invar=s.starts_with("in");
                    outvar=s.ends_with("out");
                },
                Rule::type_field => {
                    let mut k = x.into_inner().rev();
                    partype = Self::pair_to_type(&context, k.next().unwrap());
                    let var_ptrs: Vec<_> = k.map(|j|j.as_str().to_string()).collect();
                    vars.extend(var_ptrs);
                },
                _ => unreachable!()
            }
        }
        return (invar,outvar,vars,partype)
    }
    fn compile_bexpr(&self, bexpr: &Box<Expr>) -> Option<BasicValueEnum<'ctx>>{
        self.compile_expr((*bexpr).as_ref().clone())
    }
    fn compile_beexpr(&self, beexpr: &Box<(Expr,Expr)>) -> (Option<BasicValueEnum<'ctx>>,Option<BasicValueEnum<'ctx>>){
        let (a,b)=beexpr.as_ref();
        let a = self.compile_expr(a.clone());
        let b = self.compile_expr(b.clone());
        return (a,b)
    }
    fn expr_type(
        context: &'ctx Context, 
        locals: &HashMap<(FunctionValue<'ctx>,String), (PointerValue<'ctx>,BasicTypeEnum<'ctx>)>, 
        paramstack: &HashMap<String, BasicValueEnum<'ctx>>, 
        functions: &HashMap<String, Vec<FunctionValue<'ctx>>>,
        cur_func: &FunctionValue<'ctx>,
        expr: &Expr
    ) -> BasicTypeEnum<'ctx> {
        use Expr as E;
        match expr{
            E::Equ(_)| 
            E::Neq(_)| 
            E:: Gt(_)| 
            E:: Lt(_)| 
            E:: Ge(_)| 
            E:: Le(_) => context.bool_type().as_basic_type_enum(),
            E::Add(bee)| 
            E::Sub(bee)| 
            E::Mul(bee) => Self::expr_type(context, locals, paramstack, functions, cur_func, &bee.as_ref().clone().0),
            E::Div(bee) => {
                todo!("unimplemented: im confused whether Div should handle Idv's job as wel?")
            },
            E::Idv(bee) => context.i64_type().as_basic_type_enum(),
            E::Pow(bee) => context.f64_type().as_basic_type_enum(),
            E::Neg(be) => Self::expr_type(context, locals, paramstack, functions, cur_func, be.as_ref()),
            E::Pathident(s) => paramstack
                .get(&s.clone())
                .map(|x|x.get_type())
                .unwrap_or(
                    locals.get(&(*cur_func,s.clone())).unwrap().1),
            E::Call(s, ve) => {
                let argtypes: Vec<_> = ve.iter().map(|e|Self::expr_type(context, locals, paramstack, functions, cur_func, &e)).collect();
                // the piece of code below is beautifully ugly
                functions.get(&s.clone()).unwrap().iter()
                    .find(|&e|{
                        let fargtypes = e.get_params().iter()
                            .map(|p|
                                p.get_type()
                            ).collect::<Vec<_>>();
                        fargtypes == argtypes
                    }
                    ).unwrap().get_type().get_return_type().unwrap()
            }
            E::Int(i) => context.i64_type().as_basic_type_enum(),
            E::Float(f) => context.f64_type().as_basic_type_enum(),
            E::Bool(b) => context.bool_type().as_basic_type_enum(),
            E::Nil => todo!("NIL type is not supported"),
        }
    }
    fn compile_expr(&self, expr: Expr) -> Option<BasicValueEnum<'ctx>> {
        //println!("compile_expr({expr:?})");
        match expr{
            Expr::Equ(bee) => {
                let (a,b) = self.compile_beexpr(&bee);
                let a = a.expect("void operand");
                let b = b.expect("void operand");
                Some(match a.get_type(){
                    BasicTypeEnum::IntType(v) => {
                        self.builder.build_int_compare(
                            inkwell::IntPredicate::EQ, 
                            a.into_int_value(), 
                            b.into_int_value(), 
                            "inteq").unwrap().into()
                    },
                    BasicTypeEnum::FloatType(v) => {
                        self.builder.build_float_compare(
                            inkwell::FloatPredicate::OEQ, 
                            a.into_float_value(), 
                            b.into_float_value(), 
                            "floateq").unwrap().into()
                    },
                    _ => unimplemented!()
                })
            },
            Expr::Neq(bee) => {
                let (a,b) = self.compile_beexpr(&bee);
                let a = a.expect("void operand");
                let b = b.expect("void operand");
                Some(match a.get_type(){
                    BasicTypeEnum::IntType(v) => {
                        self.builder.build_int_compare(
                            inkwell::IntPredicate::NE, 
                            a.into_int_value(), 
                            b.into_int_value(), 
                            "intneq").unwrap().into()
                    },
                    BasicTypeEnum::FloatType(v) => {
                        self.builder.build_float_compare(
                            inkwell::FloatPredicate::ONE, 
                            a.into_float_value(), 
                            b.into_float_value(), 
                            "floatneq").unwrap().into()
                    },
                    _ => unimplemented!()
                })
            },
            Expr ::Gt(bee) => {
                let (a,b) = self.compile_beexpr(&bee);
                let a = a.expect("void operand");
                let b = b.expect("void operand");
                Some(match a.get_type(){
                    BasicTypeEnum::IntType(v) => {
                        self.builder.build_int_compare(
                            inkwell::IntPredicate::SGT, 
                            a.into_int_value(), 
                            b.into_int_value(), 
                            "intgt").unwrap().into()
                    },
                    BasicTypeEnum::FloatType(v) => {
                        self.builder.build_float_compare(
                            inkwell::FloatPredicate::OGT, 
                            a.into_float_value(), 
                            b.into_float_value(), 
                            "floatgt").unwrap().into()
                    },
                    _ => unimplemented!()
                })
            },
            Expr ::Lt(bee) => {
                let (a,b) = self.compile_beexpr(&bee);
                let a = a.expect("void operand");
                let b = b.expect("void operand");
                Some(match a.get_type(){
                    BasicTypeEnum::IntType(v) => {
                        self.builder.build_int_compare(
                            inkwell::IntPredicate::SLT, 
                            a.into_int_value(), 
                            b.into_int_value(), 
                            "intlt").unwrap().into()
                    },
                    BasicTypeEnum::FloatType(v) => {
                        self.builder.build_float_compare(
                            inkwell::FloatPredicate::OLT, 
                            a.into_float_value(), 
                            b.into_float_value(), 
                            "floatlt").unwrap().into()
                    },
                    _ => unimplemented!()
                })
            },
            Expr ::Ge(bee) => {
                let (a,b) = self.compile_beexpr(&bee);
                let a = a.expect("void operand");
                let b = b.expect("void operand");
                Some(match a.get_type(){
                    BasicTypeEnum::IntType(v) => {
                        self.builder.build_int_compare(
                            inkwell::IntPredicate::SGE, 
                            a.into_int_value(), 
                            b.into_int_value(), 
                            "intge").unwrap().into()
                    },
                    BasicTypeEnum::FloatType(v) => {
                        self.builder.build_float_compare(
                            inkwell::FloatPredicate::OGE, 
                            a.into_float_value(), 
                            b.into_float_value(), 
                            "floatge").unwrap().into()
                    },
                    _ => unimplemented!()
                })
            },
            Expr ::Le(bee) => {
                let (a,b) = self.compile_beexpr(&bee);
                let a = a.expect("void operand");
                let b = b.expect("void operand");
                Some(match a.get_type(){
                    BasicTypeEnum::IntType(v) => {
                        self.builder.build_int_compare(
                            inkwell::IntPredicate::SLE, 
                            a.into_int_value(), 
                            b.into_int_value(), 
                            "intle").unwrap().into()
                    },
                    BasicTypeEnum::FloatType(v) => {
                        self.builder.build_float_compare(
                            inkwell::FloatPredicate::OLE, 
                            a.into_float_value(), 
                            b.into_float_value(), 
                            "floatle").unwrap().into()
                    },
                    _ => unimplemented!()
                })
            },
            Expr::Add(bee) => {
                let (a,b) = self.compile_beexpr(&bee);
                let a = a.expect("void operand");
                let b = b.expect("void operand");
                Some(match a.get_type(){
                    BasicTypeEnum::IntType(v) => {
                        self.builder.build_int_add(a.into_int_value(), b.into_int_value(), "intadd").unwrap().into()
                    },
                    BasicTypeEnum::FloatType(v) => {
                        self.builder.build_float_add(a.into_float_value(), b.into_float_value(), "floatadd").unwrap().into()
                    },
                    _ => unimplemented!()
                })
            },
            Expr::Sub(bee) => {
                let (a,b) = self.compile_beexpr(&bee);
                let a = a.expect("void operand");
                let b = b.expect("void operand");
                Some(match a.get_type(){
                    BasicTypeEnum::IntType(v) => {
                        self.builder.build_int_sub(a.into_int_value(), b.into_int_value(), "intsub").unwrap().into()
                    },
                    BasicTypeEnum::FloatType(v) => {
                        self.builder.build_float_sub(a.into_float_value(), b.into_float_value(), "floatsub").unwrap().into()
                    },
                    _ => unimplemented!()
                })
            },
            Expr::Mul(bee) => {
                let (a,b) = self.compile_beexpr(&bee);
                let a = a.expect("void operand");
                let b = b.expect("void operand");
                Some(match a.get_type(){
                    BasicTypeEnum::IntType(v) => {
                        self.builder.build_int_mul(a.into_int_value(), b.into_int_value(), "intmul").unwrap().into()
                    },
                    BasicTypeEnum::FloatType(v) => {
                        self.builder.build_float_mul(a.into_float_value(), b.into_float_value(), "floatmul").unwrap().into()
                    },
                    _ => unimplemented!()
                })
            },
            Expr::Div(bee) => {
                let (a,b) = self.compile_beexpr(&bee);
                let a = a.expect("void operand");
                let b = b.expect("void operand");
                Some(match a.get_type(){
                    BasicTypeEnum::IntType(v) => {
                        self.builder.build_int_signed_div(a.into_int_value(), b.into_int_value(), "intdiv").unwrap().into()
                    },
                    BasicTypeEnum::FloatType(v) => {
                        self.builder.build_float_div(a.into_float_value(), b.into_float_value(), "floatdiv").unwrap().into()
                    },
                    _ => unimplemented!()
                })
            },
            Expr::Idv(bee) => {
                let (a,b) = self.compile_beexpr(&bee);
                let a = a.expect("void operand");
                let b = b.expect("void operand");
                return Some(self.builder.build_int_signed_div(a.into_int_value(), b.into_int_value(), "intdiv").unwrap().into())
            },
            Expr::Pow(bee) => {
                let (a,b) = self.compile_beexpr(&bee);
                let a = a.expect("void operand");
                let b = b.expect("void operand");
                if b.get_type().is_int_type(){
                    let a = self.builder.build_cast(InstructionOpcode::SIToFP, a, self.context.f32_type(), "sitofp").unwrap();

                    let b = self.builder.build_int_cast(b.into_int_value(), self.context.i32_type(), "cast").unwrap();
                    let retf32 = self.builder.build_direct_call(
                        self.fpowi(), 
                        &[
                            a.into(),
                            b.into()
                        ], 
                        "powi").unwrap().try_as_basic_value().left().unwrap();
                    let ret = self.builder.build_float_cast(retf32.into_float_value(), self.context.f64_type(), "cast").unwrap();
                    return Some(ret.as_basic_value_enum());
                }
                return Some(self.builder.build_direct_call(
                    self.fpowf(), 
                    &[
                        a.into(),
                        b.into()
                    ], 
                    "powf").unwrap().try_as_basic_value().left().unwrap())
            },
            Expr::Neg(x) => {
                let inner = self.compile_bexpr(&x).expect("void operand");
                Some(match inner.get_type(){
                    BasicTypeEnum::IntType(v) => {
                        self.builder.build_int_neg(inner.into_int_value(),"intneg").unwrap().into()
                    },
                    BasicTypeEnum::FloatType(v) => {
                        self.builder.build_float_neg(inner.into_float_value(),"floatneg").unwrap().into()
                    },
                    _ => unimplemented!()
                })
            },
            Expr::Pathident(path) => {
                if let Some(x)=self.paramstack.get(&path){
                    //println!("found {path} in paramstack");
                    Some(*x)
                }else{ 
                    let (var_ptr, var_typ) = self.locals.get(
                        &(self.builder.get_insert_block().unwrap().get_parent().unwrap(),path.clone())
                        ).expect(&format!("did not find {path}"));
                    //println!("found {path} in locals");
                    use BasicTypeEnum as BTE;
                    Some(match var_typ{
                        BTE::ArrayType(_)   => todo!(),
                        BTE::FloatType(t)   => self.builder.build_load(var_typ.into_float_type(), *var_ptr, "loadpath").unwrap(),
                        BTE::IntType(t)     => self.builder.build_load(var_typ.into_int_type(), *var_ptr, "loadpath").unwrap(),
                        BTE::PointerType(t) => self.builder.build_load(var_typ.into_pointer_type(), *var_ptr, "loadpath").unwrap(),
                        BTE::StructType(_)  => todo!(),
                        BTE::VectorType(_)  => todo!(),
                    })
                }
            },

            Expr::Call(name, args) => {
                if &name=="output"{
                    for arg in &args{
                        let argtype = Self::expr_type(
                            self.context, self.locals, self.paramstack, self.functions,
                            &self.builder.get_insert_block().unwrap().get_parent().unwrap(), &arg);
                        let func = self.find_function(&name, &[argtype.into()]).unwrap();
                        let call = self.builder.build_direct_call(func, 
                            &[self.compile_expr(arg.clone()).unwrap().into()], 
                            "print");
                        let call = call.unwrap().try_as_basic_value();
                    }
                    let func = self.find_function(&name, &[]).unwrap();
                    let call = self.builder.build_direct_call(func, &[], "printnewline");
                    let call = call.unwrap().try_as_basic_value();

                    return None
                }
                let argtypes: Vec<_> = args.iter().map(|e|
                    Self::expr_type(
                        self.context, 
                        self.locals, 
                        self.paramstack, 
                        self.functions, 
                        &self.builder.get_insert_block().unwrap().get_parent().unwrap(),
                        &e)).collect();
                let func = self.find_function(&name, &argtypes).expect(&format!("could not find function with name {name} with {} arguments",argtypes.len()));
                //(&name).unwrap();
                let tmp = self.builder.build_direct_call(func, 
                    &args.iter().map(|e|self.compile_expr(e.clone()).unwrap().into()).collect::<Vec<_>>(), 
                    "call");
                let tmp = tmp.unwrap().try_as_basic_value();
                return tmp.left();
            },
            Expr::Int(i) => Some(self.context.i64_type().const_int(i as u64, false).into()),
            Expr::Float(i) => Some(self.context.f64_type().const_float(i).into()),
            Expr::Bool(i) => Some(self.context.i8_type().const_int(i as u64, false).into()),
            Expr::Nil => unimplemented!(),
        }
    }
    fn bte_to_fstr(bte: &BasicTypeEnum) -> &'static str{
        match bte{
            BasicTypeEnum::ArrayType(_) => unimplemented!(),
            BasicTypeEnum::FloatType(_) => "%ld",
            BasicTypeEnum::IntType(_) => "%lli",
            BasicTypeEnum::PointerType(_) => "%p",
            BasicTypeEnum::StructType(_) => todo!(),
            BasicTypeEnum::VectorType(_) => unimplemented!(),
        }
    }
    fn declare_funcs(&mut self, pair: Pair<Rule>){
        //println!("declare_funcs({pair:?})");
        use Rule as R;
        match pair.as_rule(){
            R::typealias => todo!(),
            R::procedure_def => {
                let mut i = pair.into_inner();
                let name = i.next().unwrap().as_str();//
                let mut intype_blueprint: Vec<(bool,bool,String,BasicTypeEnum)> = vec![];
                let mut intypes: Vec<BasicMetadataTypeEnum> = vec![];
                let mut outtype = self.context.i8_type().as_basic_type_enum();
                let parameters: Vec<_> = i.clone().filter(|x|x.as_rule()==R::parameter)
                    .map(|x|Self::process_parameter(&self.context,x)).collect();
                for (inv,outv, vars, typ) in parameters{
                    for var in vars{
                        intype_blueprint.push((inv,outv,var.clone(),typ));
                        intypes.push(typ.into());
                    }
                }
                let context = self.context;
                let module = self.module;
                let functype = context.void_type().clone().fn_type(&intypes, false).clone();
                let func = self.module.add_function(name, functype, None);
                match self.functions.get_mut(&name.to_string()){
                    None => {self.functions.insert(name.to_string(), vec![func.clone()]);},
                    Some(x) => x.push(func.clone())
                };
                let funcblock = self.context.append_basic_block(func, "entry");
                self.builder.position_at_end(funcblock);
                while let Some(x) = i.next(){
                    match x.as_rule(){
                        R::konstanta | R::kamus => self.declare_funcs(x),
                        _ => continue
                    }
                }
            },
            R::function_def => {
                let mut i = pair.into_inner();
                let name = i.next().unwrap().as_str();//
                assert!(name!="main");
                let mut intype_blueprint: Vec<(bool,bool,String,BasicTypeEnum)> = vec![];
                let mut intypes: Vec<BasicMetadataTypeEnum> = vec![];
                let mut outtype = self.context.i8_type().as_basic_type_enum();
                let parameters: Vec<_> = i.clone().filter(|x|x.as_rule()==R::parameter)
                    .map(|x|Self::process_parameter(&self.context,x)).collect();
                for (inv,outv, vars, typ) in parameters.clone(){
                    for var in vars{
                        intype_blueprint.push((inv,outv,var.clone(),typ));
                        intypes.push(typ.into());
                    }
                }


                let typename = i.clone().find(|x|{
                    match x.as_rule(){
                        R::integer_type|R::real_type|R::bool_type
                        |R::pointer_type|R::user_type => true,
                        _ => false
                    }
                }).unwrap();
                let context = self.context;
                let module = self.module;
                let outtyp = Self::pair_to_type(&context, typename);
                let functype = outtyp.clone().fn_type(&intypes, false).clone();
                let func = self.module.add_function(name, functype, None);
                match self.functions.get_mut(&name.to_string()){
                    None => {self.functions.insert(name.to_string(), vec![func.clone()]);},
                    Some(x) => x.push(func.clone())
                };
                let funcblock = self.context.append_basic_block(func, "entry");
                self.builder.position_at_end(funcblock);
                let mut parami = 0;
                for (inv,outv, vars, typ) in parameters.iter(){
                    for var in vars.iter().rev(){
                        let p = func.get_nth_param(parami).unwrap();
                        let ptr = self.builder.build_alloca(*typ, &var).unwrap();
                        self.locals.insert((func,var.clone()), (ptr,*typ));
                        self.builder.build_store(ptr, p).unwrap();
                        parami+=1;
                    }
                }

                while let Some(x) = i.next(){
                    match x.as_rule(){
                        R::konstanta | R::kamus => self.declare_funcs(x),
                        _ => continue
                    }
                }

            },
            R::mainprogram => {
                let main_fn = self.module.get_function("main").unwrap();
                let entry =main_fn.get_first_basic_block().unwrap();
                self.builder.position_at_end(entry);
                let mut i = pair.into_inner(); 
                let _ = i.map(|p|self.declare_funcs(p)).collect::<Vec<()>>();
            },
            R::konstanta => {
                let j = pair.into_inner();
                //ctf = const type field
                for ctf in j{
                    let mut k = ctf.into_inner();
                    let ident = k.next().unwrap().as_str();
                    let module = self.module;
                    let context = self.context;
                    let ty = Self::pair_to_type(&context, k.next().unwrap());
                    //let ftype = ty.fn_type(&[], false);
                    //let func = module.add_function("name", ftype, None);
                    let var_ptr = self.builder.build_alloca(ty.clone(), ident).unwrap();
                    let func = self.builder.get_insert_block().unwrap().get_parent().unwrap();
                    let val = k.next().unwrap();
                    self.locals.insert((func,ident.clone().to_string()), (var_ptr.clone(),ty.clone()));
                    self.builder.build_store(var_ptr.into(), self.pair_to_value(val)).unwrap();
                }
            },
            R::kamus => {
                let j = pair.into_inner();
                let func = self.builder.get_insert_block().unwrap().get_parent().unwrap();
                for type_decl in j{
                    let mut k = type_decl.into_inner().rev();
                    let context = self.context;
                    let ty = Self::pair_to_type(&context, k.next().unwrap());
                    let var_ptrs: Vec<_> = k.map(|x|{
                        let name = x.as_str();
                        println!("kamus for {name}");
                        let var_ptr = self.builder.build_alloca(ty, x.as_str()).unwrap();
                        self.locals.insert((func,name.clone().to_string()), (var_ptr.clone(),ty.clone()));
                    }).collect();
                }

            },
            _ => return
        }

    }

    fn compile_pest_output(&mut self, pair: Pair<Rule>){
        //println!("compile_pest_output({})",pair.to_string());
        use Rule as R;
        match pair.as_rule(){
            R::expr => {
                let exp = parse_expr(pair.into_inner());
                self.compile_expr(exp);
            }
            R::whlstmt => {
                let mut i = pair.into_inner();
                let cur_func = self.builder.get_insert_block().unwrap().get_parent().unwrap();
                let checkblock = self.context.append_basic_block(cur_func, "check");
                let contblock = self.context.append_basic_block(cur_func, "contblock");
                let body = self.context.append_basic_block(cur_func, "whileblock");
                let expr = parse_expr(i.next().unwrap().into_inner());
                let compiled_expr = self.compile_expr(expr.clone()).unwrap().into_int_value();
                self.builder.build_unconditional_branch(checkblock);
                self.builder.position_at_end(checkblock);
                self.builder.build_conditional_branch(compiled_expr, body, contblock);
                self.builder.position_at_end(body);
                self.compile_pest_output(i.next().unwrap());
                let compiled_expr = self.compile_expr(expr).unwrap().into_int_value();
                self.builder.build_conditional_branch(compiled_expr, body, contblock);
                self.builder.position_at_end(contblock);
            }
            R::ifstmt => {
                let mut i = pair.into_inner();
                let cur_func = self.builder.get_insert_block().unwrap().get_parent().unwrap();
                let contblock = self.context.append_basic_block(cur_func, "contblock");
                loop {
                    match (i.next(),i.next()){
                        (Some(ifthat), Some(dothis)) => {
                            //println!("if {ifthat:#?} then {dothis:#?}");
                            let mut thenblock = self.context.append_basic_block(cur_func, "thenblock");
                            let mut elseblock = self.context.append_basic_block(cur_func, "elseblock");
                            let cond = parse_expr(ifthat.into_inner());
                            let cond = self.compile_expr(cond).unwrap().into_int_value();
                            self.builder.build_conditional_branch(cond, thenblock, elseblock);
                            self.builder.position_at_end(thenblock);
                            self.compile_pest_output(dothis);
                            self.builder.build_unconditional_branch(contblock);
                            self.builder.position_at_end(elseblock);
                        },
                        (Some(dothis), None) => {
                            //println!("else");
                            self.compile_pest_output(dothis);
                            break;
                        },
                        _ => break
                    }
                }
                self.builder.build_unconditional_branch(contblock);
                self.builder.position_at_end(contblock);
            }
            R::asgnstmt => {
                let mut i = pair.into_inner();
                let path = i.next().unwrap().as_str();
                let expr = parse_expr(i.next().unwrap().into_inner());
                let compiled_expr = self.compile_expr(expr).expect("void assignment");
                let func = self.builder.get_insert_block().unwrap().get_parent().unwrap();
                let (var_ptr,var_typ) = self.locals.get(&(func,path.to_string())).unwrap();
                self.builder.build_store(var_ptr.clone(), compiled_expr);
            }
            R::retstmt => {
                let exp = pair.into_inner();
                let exp = parse_expr(exp);
                if exp.is_nil(){
                    todo!("NIL return is not supported yet")
                }
                let ibl = self.builder.get_insert_block().unwrap();
                let bname = ibl.get_name().to_str();
                if bname.unwrap() == "mainf_entry"{
                    let etyp=Self::expr_type(self.context, self.locals, self.paramstack, self.functions,
                        &self.builder.get_insert_block().unwrap().get_parent().unwrap(),&exp);
                    if etyp.is_int_type()==false{
                        panic!("main return should be int")
                    }
                }
                // self.builder.build_return(self.compile_expr(exp).map(|x|&x)); <-- WHY DOESNT THIS WORK!??!?
                if let Some(compiled_exp) = self.compile_expr(exp){
                    self.builder.build_return(Some(&compiled_exp));
                } else {
                    self.builder.build_return(None);
                }
            }
            R::typealias => todo!(),
            R::procedure_def => {
                let mut i = pair.into_inner();
                let name = i.next().unwrap().as_str();//
                let func = self.module.get_function(name).unwrap();
                self.builder.position_at_end(func.get_first_basic_block().unwrap());
                while let Some(x) = i.next(){
                    match x.as_rule(){
                        R::algoritma => self.compile_pest_output(x),
                        _ => unreachable!()
                    }
                }
            },
            R::function_def => {
                let mut i = pair.into_inner();
                let name = i.next().unwrap().as_str();//
                assert!(name!="main");
                let func = self.module.get_function(name).unwrap();
                self.builder.position_at_end(func.get_first_basic_block().unwrap());
                while let Some(x) = i.next(){
                    match x.as_rule(){
                        R::algoritma => self.compile_pest_output(x),
                        R::integer_type|R::konstanta|R::kamus|R::real_type
                        |R::bool_type|R::pointer_type|R::user_type|R::parameter => continue,
                        _ => unreachable!("{:?}",x.as_rule())
                    }
                }
                self.builder.build_return(None);

            },
            R::mainprogram => {
                let main_fn = self.module.get_function("main").unwrap();
                let entry =main_fn.get_first_basic_block().unwrap();
                self.builder.position_at_end(entry);
                let mut i = pair.into_inner(); 
                let program_name = i.next().unwrap().as_str().to_string();
                let _ = i.map(|p|self.compile_pest_output(p)).collect::<Vec<()>>();
            },
            R::konstanta|R::kamus => return,
            R::algoritma|R::stmt0|R::stmt1 => {
                let _ = pair.into_inner().map(|p|self.compile_pest_output(p)).collect::<Vec<()>>();
            }
            _ => unreachable!("reached rule {}",pair.as_rule().to_string())
        }
    }
    pub fn add_printf(&mut self){
        let int32 = self.context.i32_type();
        let int8ptr = self.context.i8_type().ptr_type(AddressSpace::default());
        let printf_types = int32.fn_type(&[int8ptr.into()], true);
        let func = self.module.add_function("printf", printf_types, Some(Linkage::External));
        let name = "printf".to_string();
        match self.functions.get_mut(&name){
            None => {self.functions.insert(name, vec![func.clone()]);},
            Some(x) => x.push(func.clone())
        };
    }
    pub fn add_output(&mut self){
        let main_fn = self.module.get_function("main").unwrap();
        let entry =main_fn.get_first_basic_block().unwrap();
        self.builder.position_at_end(entry);

        let newline_fstr = self.builder.build_global_string_ptr("\n", "fstrld").unwrap();
        let i64_fstr = self.builder.build_global_string_ptr("%ld ", "fstrld").unwrap();
        let f64_fstr = self.builder.build_global_string_ptr("%f ", "fstrld").unwrap();
        let bool_fstr = self.builder.build_global_string_ptr("%b ", "fstrld").unwrap();
        let printf = self.module.get_function("printf").unwrap();
        let name = "output".to_string();
        //
        let ftype = self.context.void_type().fn_type(&[], false);
        let func = self.module.add_function("output", ftype, None);
        match self.functions.get_mut(&name){
            None => {self.functions.insert(name.clone(), vec![func.clone()]);},
            Some(x) => x.push(func.clone())
        };
        let fblock = self.context.append_basic_block(func, "outputentryempty");
        self.builder.position_at_end(fblock);
        let pcall = self.builder.build_direct_call(
            printf, 
            &[
                newline_fstr.as_pointer_value().into(), 
            ], 
            "printi64").unwrap();
        self.builder.build_return(None);
        //
        let ftype = self.context.void_type().fn_type(&[self.context.i64_type().into()], false);
        let func = self.module.add_function("output", ftype, None);
        match self.functions.get_mut(&name){
            None => {self.functions.insert(name.clone(), vec![func.clone()]);},
            Some(x) => x.push(func.clone())
        };
        let fblock = self.context.append_basic_block(func, "outputentryi64");
        self.builder.position_at_end(fblock);
        let param= func.get_first_param().unwrap();
        let pcall = self.builder.build_direct_call(
            printf, 
            &[
                i64_fstr.as_pointer_value().into(), 
                param.into()
            ], 
            "printi64").unwrap();
        self.builder.build_return(None);
        //
        let ftype = self.context.void_type().fn_type(&[self.context.f64_type().into()], false);
        let func = self.module.add_function("output", ftype, None);
        match self.functions.get_mut(&name){
            None => {self.functions.insert(name.clone(), vec![func.clone()]);},
            Some(x) => x.push(func.clone())
        };
        let fblock = self.context.append_basic_block(func, "outputentryf64");
        self.builder.position_at_end(fblock);
        let param= func.get_first_param().unwrap();
        let pcall = self.builder.build_direct_call(
            printf, 
            &[
                f64_fstr.as_pointer_value().into(), 
                param.into()
            ], 
            "printf64").unwrap();
        self.builder.build_return(None);
        //
        let ftype = self.context.void_type().fn_type(&[self.context.bool_type().into()], false);
        let func = self.module.add_function("output", ftype, None);
        match self.functions.get_mut(&name){
            None => {self.functions.insert(name.clone(), vec![func.clone()]);},
            Some(x) => x.push(func.clone())
        };
        let fblock = self.context.append_basic_block(func, "outputentrybool");
        self.builder.position_at_end(fblock);
        let param= func.get_first_param().unwrap();
        let pcall = self.builder.build_direct_call(
            printf, 
            &[
                bool_fstr.as_pointer_value().into(), 
                param.into()
            ], 
            "printfbool").unwrap();
        self.builder.build_return(None);

    }
    // pub fn add_powi(&self){
    //     let f32t = self.context.f32_type().into();
    //     let i32t = self.context.i32_type().into();
    //     let f32tout = self.context.f32_type();
    //     let ftype = f32tout.fn_type(&[f32t,i32t], false);
    //     self.module.add_function("powi", ftype, None);
    // }
    // pub fn add_powf(&self){
    //     let f64t = self.context.f64_type().into();
    //     let f64tout = self.context.f64_type();
    //     let ftype = f64tout.fn_type(&[f64t,f64t], false);
    //     self.module.add_function("powf", ftype, None);
    // }
    pub fn fpowf(&self) -> FunctionValue<'ctx>{
        let powf = Intrinsic::find("llvm.pow.f64").expect("couldnt find powf64");
        powf.get_declaration(
            &self.module, 
            &[
                self.context.f64_type().as_basic_type_enum(),
                self.context.f64_type().as_basic_type_enum()
            ]
        ).unwrap()
    }
    pub fn fpowi(&self) -> FunctionValue<'ctx>{
        let powi = Intrinsic::find("llvm.powi.f32.i32").unwrap();
        powi.get_declaration(
            &self.module, 
            &[
                self.context.f32_type().as_basic_type_enum(),
                self.context.i32_type().as_basic_type_enum()
            ]
        ).unwrap()
    }
}
