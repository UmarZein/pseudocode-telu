use super::{Type, Codegen};
use log::{debug, error, info, log_enabled, warn, Level};

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
use inkwell::types::{BasicMetadataTypeEnum, FunctionType, BasicTypeEnum, BasicType, PointerType, StructType};
use inkwell::values::{BasicMetadataValueEnum, BasicValueEnum, FloatValue, FunctionValue, StructValue, PointerValue, BasicValue, InstructionOpcode, AsValueRef, InstructionValue};
use inkwell::FloatPredicate;

use pest::Parser;
use pest::iterators::{Pairs, Pair};
use itertools::Itertools;

use std::collections::{HashMap, VecDeque};
use std::hint::unreachable_unchecked;
use std::ops::Deref;

use crate::parse::{PRATT_PARSER, FCParser, Rule, parse_expr, Expr, simple_expr_str};
use crate::{print_pair, print_pairs};

impl<'a, 'ctx> Codegen<'a, 'ctx> where 'ctx:'a{
    fn compile_bexpr(&self, bexpr: &Box<Expr>) -> (Option<BasicValueEnum<'ctx>>, Type){
        let x = bexpr.as_ref();
        return (self.compile_expr(x.clone()), self.expr_type(x))
    }
    fn compile_beexpr(&self, beexpr: &Box<(Expr,Expr)>) -> (Option<BasicValueEnum<'ctx>>,Option<BasicValueEnum<'ctx>>,Type,Type){
        let (a,b)=beexpr.as_ref();
        let typea = self.expr_type(a);
        let typeb = self.expr_type(b);
        let a = self.compile_expr(a.clone());
        let b = self.compile_expr(b.clone());
        return (a,b,typea,typeb)
    }
    pub(crate) fn expr_type(&self, expr: &Expr)->Type{
        Self::raw_expr_type(self.context, self.locals, self.functions, self.struct_defs, &self.builder.get_insert_block().unwrap().get_parent().unwrap(), &expr)
    }
    pub(crate) fn raw_expr_type(
        context: &'ctx Context, 
        locals: &HashMap<(FunctionValue<'ctx>,String), (PointerValue<'ctx>,Type)>, 
        functions: &HashMap<String, Vec<(FunctionValue<'ctx>, Type, Vec<(bool,bool,String,Type)>)>>,
        struct_defs: &HashMap<String, (StructType<'ctx>, Vec<(String,Type)>)>,
        cur_func: &FunctionValue<'ctx>,
        expr: &Expr
    ) -> Type {
        use Expr as E;
        match expr{
            E::Equ(_)| 
            E::Neq(_)| 
            E::Not(_)| 
            E::Lor(_)| 
            E::Land(_)| 
            E:: Gt(_)| 
            E:: Lt(_)| 
            E:: Ge(_)| 
            E:: Le(_) => Type::Bool,
            E::Add(bee)| 
            E::Sub(bee)| 
            E::Mul(bee) => Self::raw_expr_type(context, locals, functions, struct_defs, cur_func, &bee.as_ref().clone().0),
            E::Div(bee) => {
                todo!("unimplemented: im confused whether Div should handle Idv's job as wel?")
            },
            E::Idv(bee)|E::Mod(bee) => Type::Int,
            E::Pow(bee) => Type::Float,
            E::Neg(be) => Self::raw_expr_type(context, locals, functions, struct_defs, cur_func, be.as_ref()),
            E::Pathident(be, arg) => {
                let left_side_type = Self::raw_expr_type(context, locals, functions, struct_defs, cur_func, be.deref());
                match left_side_type{
                    Type::StructType(name, fields) => {
                        return fields.iter().find(|(s,typ)|s==arg).unwrap().1.clone()
                    },
                    other => unimplemented!("member access must be of a struct")
                }
            }
            E::Ident(s) => locals.get(&(*cur_func,s.clone())).expect(&format!("could not find {s}")).1.clone(),
            E::SquareArgs(_, _) => todo!(),
            E::RoundArgs(s, ve) => {
                // RoundArgs is either aFunctionCall(arg1,arg2,[...]) or MemberGet(instance*)
                // member accesses (called GEP, get-element-pointer, well, more correctly get-struct-element-pointer) must have only 1 argument and the
                // outer identifier must match a member name of the struct-type of the instance
                // (which is the inner element or the only argument)
                let argtypes: Vec<_> = ve.iter().map(|e|Self::raw_expr_type(context, locals, functions, struct_defs, cur_func, &e)).collect();
                if argtypes.len()==1{
                    let inner_type = Self::raw_expr_type(context, locals, functions, struct_defs, cur_func, &{unsafe{ve.get_unchecked(0)}}.deref().clone());

                    
                   if let Type::Ptr(be) = inner_type{
                        if let Type::StructType(name, fields) = be.deref().clone(){
                            if let E::Ident(memberName) = s.deref(){
                                return fields
                                    .iter()
                                    .find(
                                        |(s, bt)|{ s==memberName }
                                    ).expect(&format!("{memberName} not found as property of struct {name}")).1.clone()
                            }
                        }
                        // Type::StructType(impl_level, name, fields) => {
                        //     if let E::Ident(memberName) = s.deref(){
                        //         return fields
                        //             .iter()
                        //             .find(
                        //                 |(s, bt)|{ s==memberName }
                        //             ).expect(&format!("{memberName} not found as property of struct {name}")).1.clone()
                        //     }
                        // },
                    }
                }
                // else if s is ident...
                // this code is beautifully ugly
                if let E::Ident(ident) = s.deref() {
                    functions.get(&ident.clone()).unwrap().iter()
                        .find(|&(e,t,v)|{
                            let fargtypes = v.iter()
                                .map(|x|x.3.clone())
                                .collect::<Vec<_>>();
                            fargtypes == argtypes
                        }
                        ).expect(&format!("could not find function-implementation. identifier: {ident}")).1.clone()
                } else {
                    todo!("only named, non-closure, functions are currently supported")
                }
            }
            E::Int(i)   => Type::Int,
            E::Float(f) => Type::Float,
            E::Bool(b)  => Type::Bool,
            E::Land(bee) => Type::Bool,
            E::Lor(bee) => Type::Bool,
            E::Char(c)  => Type::Char,
            E::Str(s)   => Type::String ,
            E::Nil      => todo!("NIL type is not supported"),
            
        }
    }
    pub(crate) fn compile_lvalue_expr(&self, expr: Expr, func: FunctionValue<'ctx>) -> (PointerValue<'ctx>, Type){
        let mut ptr = self.context.i8_type().ptr_type(AddressSpace::default()).const_null();
        let mut typ = Type::Void;
        match expr{
            Expr::Ident(path) => {
                (ptr, typ) =
                    self.locals.get(&(func, path)).unwrap().clone();
            },
            Expr::RoundArgs(be, ve) => {
                if let Expr::Ident(memberName) = be.deref().clone(){
                    if ve.len()==1{
                        if let Type::Ptr(p) = self.expr_type(&ve[0]){
                            if let Type::StructType(name, named_fields) = p.deref().clone(){
                                let (styp, _) = self.struct_defs.get(&name).unwrap();
                                (ptr, typ) = self.compile_lvalue_expr(ve[0].clone(), func);
                                let index= named_fields.iter().fold_while(0, |a, (s, t)|{
                                        use itertools::FoldWhile::{Done, Continue};
                                        if (s==&name){
                                            typ = t.clone();
                                            Done(a)
                                        } else {
                                            Continue(a+1)
                                        }
                                    }).into_inner();
                                ptr = self.builder.build_struct_gep(styp.as_basic_type_enum(), ptr, index, "struct_gep").unwrap();
                            }
                        }

                    }
                }
                panic!("RoundArgs, in compiling lvalue expr, can only be member access: {{memberName: ident}}({{arg: pointer to structType}})")
            },
            Expr::SquareArgs(be, ve) => todo!(),
            Expr::Pathident(be, s) => {
                (ptr, typ) = self.compile_lvalue_expr(be.deref().clone(), func);
                let (struct_type, index, struct_name) = if let Type::StructType(name, fields) = typ.clone(){
                    let (styp, _) = self.struct_defs.get(&name).unwrap();
                    let index= fields.iter().fold_while(0, |a, (field_name, field_type)|{
                            use itertools::FoldWhile::{Done, Continue};
                            info!("at index={a}, comparing {field_name} and {s}");
                            if (field_name==&s){
                                typ = field_type.clone();
                                Done(a)
                            } else {
                                Continue(a+1)
                            }
                        }).into_inner();
                    (styp,index, name)
                } else {panic!("Pathident be.{s} but be is not a struct type")};
                info!("struct={struct_name}");
                info!("index={index}");
                ptr = self.builder.build_struct_gep(struct_type.as_basic_type_enum(), ptr, index, "struct_gep").unwrap();
                
            },
            other => unreachable!("{other:?} is supposed to be unreachable when compiling lvalue")
        };
        (ptr, typ)
    }
    pub(crate) fn compile_expr(&self, expr: Expr) -> Option<BasicValueEnum<'ctx>> {
        use BasicTypeEnum as BTE;
        info!("compiling expression {}",simple_expr_str(&expr));
        //println!("compile_expr({expr:?})");
        match expr{
            Expr::Equ(bee) => {
                let (a,b,typea,typeb) = self.compile_beexpr(&bee);
                let a = a.expect("void operand");
                let b = b.expect("void operand");
                Some(match typea{
                    Type::Int|Type::Char => {
                        self.builder.build_int_compare(
                            inkwell::IntPredicate::EQ, 
                            a.into_int_value(), 
                            b.into_int_value(), 
                            "inteq").unwrap().into()
                    },
                    Type::Float => {
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
                let (a,b,typea,typeb) = self.compile_beexpr(&bee);
                let a = a.expect("void operand");
                let b = b.expect("void operand");
                Some(match typea{
                    Type::Int => {
                        self.builder.build_int_compare(
                            inkwell::IntPredicate::NE, 
                            a.into_int_value(), 
                            b.into_int_value(), 
                            "intneq").unwrap().into()
                    },
                    Type::Float => {
                        self.builder.build_float_compare(
                            inkwell::FloatPredicate::ONE, 
                            a.into_float_value(), 
                            b.into_float_value(), 
                            "floatneq").unwrap().into()
                    },
                    _ => unimplemented!()
                })
            },
            Expr::Gt(bee) => {
                let (a,b,typea,typeb) = self.compile_beexpr(&bee);
                let a = a.expect("void operand");
                let b = b.expect("void operand");
                Some(match typea{
                    Type::Int => {
                        self.builder.build_int_compare(
                            inkwell::IntPredicate::SGT, 
                            a.into_int_value(), 
                            b.into_int_value(), 
                            "intgt").unwrap().into()
                    },
                    Type::Float => {
                        self.builder.build_float_compare(
                            inkwell::FloatPredicate::OGT, 
                            a.into_float_value(), 
                            b.into_float_value(), 
                            "floatgt").unwrap().into()
                    },
                    _ => unimplemented!()
                })
            },
            Expr::Lt(bee) => {
                let (a,b,typea,typeb) = self.compile_beexpr(&bee);
                let a = a.expect("void operand");
                let b = b.expect("void operand");
                Some(match typea{
                    Type::Int => {
                        self.builder.build_int_compare(
                            inkwell::IntPredicate::SLT, 
                            a.into_int_value(), 
                            b.into_int_value(), 
                            "intlt").unwrap().into()
                    },
                    Type::Float => {
                        self.builder.build_float_compare(
                            inkwell::FloatPredicate::OLT, 
                            a.into_float_value(), 
                            b.into_float_value(), 
                            "floatlt").unwrap().into()
                    },
                    _ => unimplemented!()
                })
            },
            Expr::Ge(bee) => {
                let (a,b,typea,typeb) = self.compile_beexpr(&bee);
                let a = a.expect("void operand");
                let b = b.expect("void operand");
                Some(match typea{
                    Type::Int => {
                        self.builder.build_int_compare(
                            inkwell::IntPredicate::SGE, 
                            a.into_int_value(), 
                            b.into_int_value(), 
                            "intge").unwrap().into()
                    },
                    Type::Float => {
                        self.builder.build_float_compare(
                            inkwell::FloatPredicate::OGE, 
                            a.into_float_value(), 
                            b.into_float_value(), 
                            "floatge").unwrap().into()
                    },
                    _ => unimplemented!()
                })
            },
            Expr::Le(bee) => {
                let (a,b,typea,typeb) = self.compile_beexpr(&bee);
                let a = a.expect("void operand");
                let b = b.expect("void operand");
                Some(match typea{
                    Type::Int => {
                        self.builder.build_int_compare(
                            inkwell::IntPredicate::SLE, 
                            a.into_int_value(), 
                            b.into_int_value(), 
                            "intle").unwrap().into()
                    },
                    Type::Float => {
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
                let (a,b,typea,typeb) = self.compile_beexpr(&bee);
                let a = a.expect("void operand");
                let b = b.expect("void operand");
                Some(match (typea.clone(),typeb.clone()){
                    (Type::Ptr(i),Type::Int)  => {
                        let t = i.as_ref().into_bte(self.context, self.struct_defs).into_pointer_type();
                        let aaddr = self.builder.build_ptr_to_int(a.into_pointer_value(), self.context.i64_type(), "ptrtoint").unwrap();
                        let res = self.builder.build_int_add(aaddr, b.into_int_value(), "intadd").unwrap();
                        self.builder.build_int_to_ptr(res, t, "inttoptr").unwrap().into()
                    },
                    (Type::Int,Type::Ptr(i)) => {
                        let t = i.as_ref().into_bte(self.context, self.struct_defs).into_pointer_type();
                        let baddr = self.builder.build_ptr_to_int(b.into_pointer_value(), self.context.i64_type(), "ptrtoint").unwrap();
                        let res = self.builder.build_int_add(a.into_int_value(), baddr, "intadd").unwrap();
                        self.builder.build_int_to_ptr(res, t, "inttoptr").unwrap().into()
                    },
                    (Type::Int,Type::Int)  => {
                        self.builder.build_int_add(a.into_int_value(), b.into_int_value(), "intadd").unwrap().into()
                    },
                    (Type::Float,Type::Float)  => {
                        self.builder.build_float_add(a.into_float_value(), b.into_float_value(), "floatadd").unwrap().into()
                    },
                    _ => unimplemented!("unimplemented for {typea:?} and {typeb:?}")
                })
            },
            Expr::Sub(bee) => {
                let (a,b,typea,typeb) = self.compile_beexpr(&bee);
                let a = a.expect("void operand");
                let b = b.expect("void operand");
                Some(match (typea,typeb){
                    (Type::Ptr(i),Type::Int)  => {
                        let t = i.as_ref().into_bte(self.context, self.struct_defs).into_pointer_type();
                        let aaddr = self.builder.build_ptr_to_int(a.into_pointer_value(), self.context.i64_type(), "ptrtoint").unwrap();
                        let res = self.builder.build_int_sub(aaddr, b.into_int_value(), "intsub").unwrap();
                        self.builder.build_int_to_ptr(res, t, "inttoptr").unwrap().into()
                    },
                    (Type::Int,Type::Ptr(i)) => {
                        let t = i.as_ref().into_bte(self.context, self.struct_defs).into_pointer_type();
                        let baddr = self.builder.build_ptr_to_int(b.into_pointer_value(), self.context.i64_type(), "ptrtoint").unwrap();
                        let res = self.builder.build_int_sub(a.into_int_value(), baddr, "intsub").unwrap();
                        self.builder.build_int_to_ptr(res, t, "inttoptr").unwrap().into()
                    },
                    (Type::Int,Type::Int)  => {
                        self.builder.build_int_sub(a.into_int_value(), b.into_int_value(), "intsub").unwrap().into()
                    },
                    (Type::Float, Type::Float)  => {
                        self.builder.build_float_sub(a.into_float_value(), b.into_float_value(), "floatsub").unwrap().into()
                    },
                    _ => unimplemented!()
                })
            },
            Expr::Mul(bee) => {
                let (a,b,typea,typeb) = self.compile_beexpr(&bee);
                let a = a.expect("void operand");
                let b = b.expect("void operand");
                Some(match typea{
                    Type::Int => {
                        self.builder.build_int_mul(a.into_int_value(), b.into_int_value(), "intmul").unwrap().into()
                    },
                    Type::Float => {
                        self.builder.build_float_mul(a.into_float_value(), b.into_float_value(), "floatmul").unwrap().into()
                    },
                    _ => unimplemented!()
                })
            },
            Expr::Div(bee) => {
                let (a,b,typea,typeb) = self.compile_beexpr(&bee);
                let a = a.expect("void operand");
                let b = b.expect("void operand");
                Some(match typea{
                    Type::Int => {
                        self.builder.build_int_signed_div(a.into_int_value(), b.into_int_value(), "intdiv").unwrap().into()
                    },
                    Type::Float => {
                        self.builder.build_float_div(a.into_float_value(), b.into_float_value(), "floatdiv").unwrap().into()
                    },
                    _ => unimplemented!()
                })
            },
            Expr::Land(bee) => {
                let (a,b,typea,typeb) = self.compile_beexpr(&bee);
                let a = a.expect("void operand");
                let b = b.expect("void operand");
                Some(match typea{
                    Type::Bool => {
                        match typeb{
                            Type::Bool => {
                                self.builder.build_and(a.into_int_value(), b.into_int_value(), "logicaland").unwrap().into()
                            }
                            _ => panic!("logical and only accepts boolean operands")
                        }
                    },
                    _ => panic!("logical and only accepts boolean operands")
                })
            }
            Expr::Lor(bee) => {
                let (a,b,typea,typeb) = self.compile_beexpr(&bee);
                let a = a.expect("void operand");
                let b = b.expect("void operand");
                Some(match typea{
                    Type::Bool => {
                        match typeb{
                            Type::Bool => {
                                self.builder.build_or(a.into_int_value(), b.into_int_value(), "logicaland").unwrap().into()
                            }
                            _ => panic!("logical and only accepts boolean operands")
                        }
                    },
                    _ => panic!("logical and only accepts boolean operands")
                })
            }
            Expr::Idv(bee) => {
                let (a,b,typea,typeb) = self.compile_beexpr(&bee);
                let a = a.expect("void operand");
                let b = b.expect("void operand");
                return Some(self.builder.build_int_signed_div(a.into_int_value(), b.into_int_value(), "intdiv").unwrap().into())
            },
            Expr::Mod(bee) => {
                let (a,b,typea,typeb) = self.compile_beexpr(&bee);
                let a = a.expect("void operand");
                let b = b.expect("void operand");
                let c = (self.builder.build_int_signed_rem(
                    a.into_int_value(), 
                    b.into_int_value(), 
                    "srem").unwrap());
                let d = self.builder.build_int_add(c, b.into_int_value(), "intadd").unwrap();
                Some(self.builder.build_int_signed_rem(
                    d, 
                    b.into_int_value(), 
                    "srem").unwrap().into()
                )

            },
            Expr::Pow(bee) => {
                let (a,b,typea,typeb) = self.compile_beexpr(&bee);
                let a = a.expect("void operand");
                let b = b.expect("void operand");
                if typeb==Type::Int{
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
            Expr::Not(x) => {
                let (inner,inner_type) = self.compile_bexpr(&x);
                let inner = inner.expect("void operand");
                let i64type = self.context.i64_type();
                let one_const = i64type.const_int(1, false);
                Some(match inner_type{
                    Type::Bool => {
                        self.builder.build_xor(inner.into_int_value(),one_const,"not").unwrap().into()
                    },
                    c => unreachable!("Not only accepts bool, but got {c:?}")
                })
            }
            Expr::Neg(x) => {
                let (inner,inner_type) = self.compile_bexpr(&x);
                let inner = inner.expect("void operand");
                Some(match inner_type{
                    Type::Int => {
                        self.builder.build_int_neg(inner.into_int_value(),"intneg").unwrap().into()
                    },
                    Type::Float => {
                        self.builder.build_float_neg(inner.into_float_value(),"floatneg").unwrap().into()
                    },
                    _ => unimplemented!()
                })
            },
            Expr::Ident(path) => {
                // let (inner,inner_type) = self.compile_bexpr(&be);
                // let inner = inner.expect("void operand");
                let (ptr,typ): (PointerValue<'ctx>, Type) = self.locals.get(
                    &(self.builder.get_insert_block().unwrap().get_parent().unwrap(),path.clone())
                    ).expect(&format!("did not find {path}")).clone();
                //println!("found {path} in locals");
                if let Type::Void = typ{
                    return None
                }
                let btetyp = typ.into_bte(self.context, self.struct_defs);
                let x = (match typ.clone(){
                    Type::Void => todo!(),
                    Type::VoidPtr => todo!(),
                    Type::StructType(name, fields) => self.builder.build_load(btetyp.into_struct_type(), ptr, "loadstructpath").unwrap(),
                    Type::Int => self.builder.build_load(btetyp.into_int_type(), ptr, "loadintpath").unwrap(),
                    Type::Float => self.builder.build_load(btetyp.into_float_type(), ptr, "loadfloatpath").unwrap(),
                    Type::Char => self.builder.build_load(btetyp.into_int_type(), ptr, "loadcharpath").unwrap(),
                    Type::Bool => self.builder.build_load(btetyp.into_int_type(), ptr, "loadboolpath").unwrap(),
                    Type::String => self.builder.build_load(btetyp.into_pointer_type(), ptr, "loadstringpath").unwrap(),
                    Type::Array(one, s, i) => self.builder.build_load(btetyp.into_array_type(), ptr, "loadarraypath").unwrap(),
                    Type::Ptr(_) => self.builder.build_load(btetyp.into_pointer_type(), ptr, "loadptrpath").unwrap(),
                    Type::FnType(implementation_level, _, _, vec) => todo!(), 
                });
                //x.as_instruction_value().unwrap().set_alignment(typ.correct_alignment()).unwrap();
                Some(x)
            },

            Expr::RoundArgs(be, ve) => {
                let name = if let Expr::Ident(path)=be.deref(){
                    path
                } else {
                    todo!("only function calls and memberAccess-es are currently supported")
                };
                if name=="output"{
                    for (i,arg) in ve.iter().enumerate(){
                        let argtype = Self::raw_expr_type(
                            self.context, self.locals, self.functions,
                            self.struct_defs,
                            &self.builder.get_insert_block().unwrap().get_parent().unwrap(), &arg);
                        let (func, otyp, ityp) = self.find_function(&name, None, &[argtype.into()]);
                        if i>0{
                            let (func, otyp, ityp) = self.find_function("output_space", None, &[]);
                            let call = self.builder.build_direct_call(func, &[], "printnewline");
                            let call = call.unwrap().try_as_basic_value();
                        }
                        let call = self.builder.build_direct_call(func, 
                            &[self.compile_expr(arg.clone()).unwrap().into()], 
                            "print");
                        let call = call.unwrap().try_as_basic_value();
                    }
                    let (func,otyp,ityp) = self.find_function(&name, None, &[]);
                    let call = self.builder.build_direct_call(func, &[], "printnewline");
                    let call = call.unwrap().try_as_basic_value();

                    return None
                } else if name=="input"{
                    let func = self.builder.get_insert_block().unwrap().get_parent().unwrap();
                    for (i,arg) in ve.iter().enumerate(){
                        let varident = match &arg{
                            Expr::Ident(name) => name.clone(),
                            _ => panic!("args in function 'input' should be variable identifiers"),
                        };
                        let (var_ptr, innertype) = self.locals.get(&(func, varident)).unwrap();
                        let (func, otyp, ityp) = self.find_function(&name, None, &[Type::Ptr(Box::new(innertype.clone())).into()]);
                        let call = self.builder.build_direct_call(func, 
                            &[(*var_ptr).into()], 
                            "input");
                        let call = call.unwrap().try_as_basic_value();
                    }
                    return None
                }
                let argtypes: Vec<_> = ve.iter().map(|e|
                    Self::raw_expr_type(
                        self.context, 
                        self.locals, 
                        self.functions, 
                        self.struct_defs,
                        &self.builder.get_insert_block().unwrap().get_parent().unwrap(),
                        &e)).collect();
                let (func,otyp,ityp) = self.find_function(&name, None, &argtypes);
                // check that for every out-type param, it's a pathident 
                // remember that out-type param are writeable
                for (ot,at) in ityp.iter().map(|(i,o,n,t)|*o).zip(ve.iter()){
                    let at_is_ptr = match at{Expr::Ident(_)=>true,_=>false};
                    assert!(!ot||at_is_ptr)
                }
                let input: Vec<BasicMetadataValueEnum> = ve.iter().zip(ityp.iter()).map(
                    |(e, (i, o, n, t))|{
                        if *o{
                            let (ptr,typ): (PointerValue<'ctx>, Type) = self.locals.get(
                                &(self.builder.get_insert_block().unwrap().get_parent().unwrap(),n.clone())
                                ).expect(&format!("did not find {n}")).clone();
                            ptr.into()
                        } else {
                            self.compile_expr(e.clone()).unwrap().into()
                        }
                    }
                ).collect();
                let tmp = self.builder.build_direct_call(func, 
                    &input,//&args.iter().map(|e|self.compile_expr(e.clone()).unwrap().into()).collect::<Vec<_>>(), 
                    "call");
                let tmp = tmp.unwrap().try_as_basic_value();
                return tmp.left();
            },
            Expr::Int(i) => Some(self.context.i64_type().const_int(i as u64, false).into()),
            Expr::Float(i) => Some(self.context.f64_type().const_float(i).into()),
            Expr::Bool(i) => Some(self.context.i8_type().const_int(i as u64, false).into()),
            Expr::Char(i) => Some(self.context.i8_type().const_int(i as u64, false).into()),
            Expr::Str(i) => {
                // landmark
                let int64 = self.context.i64_type();
                let int8 = self.context.i8_type();
                let i8ptr = self.context.i8_type().ptr_type(AddressSpace::default());

                let global_value = self.builder.build_global_string_ptr(&String::from_utf8(i).unwrap(), "globalstring").unwrap();
                // global_value.set_alignment(4);
                Some(global_value.as_pointer_value().into())
                // let len = i.len();
                // let name = String::from("malloc");
                // let argtypes = &[Type::Int];
                // let args = &[int64.const_int((1i64*len as i64) as u64, false).into()];
                // let (malloc,_,_) = self.find_function(&name, argtypes);
                // let call = self.builder.build_call(malloc, args, "stringmalloc");
                // let cptr = call.unwrap().try_as_basic_value().left().unwrap().into_pointer_value();
                // for offset in 0..=len{
                //     let addr = self.builder.build_ptr_to_int(cptr, self.context.i64_type(), "ptrtoint").unwrap();
                //     let res = self.builder.build_int_add(addr, self.context.i64_type().const_int(offset as u64, false), "addone").unwrap();
                //     let offsetptr=self.builder.build_int_to_ptr(res, i8ptr, "inttoptr").unwrap().into();

                //     if offset!=len{
                //         self.builder.build_store(offsetptr, self.context.i8_type().const_int(i[offset] as u64, false));
                //     } else {
                //         self.builder.build_store(offsetptr, self.context.i8_type().const_int(b'\0' as u64, false));
                //     }
                // }
                // Some(cptr.as_basic_value_enum())
            },
            Expr::Nil => unimplemented!(),
            Expr::Pathident(expr, arg) => {
                let (ptr, typ) = self.compile_lvalue_expr(expr.deref().clone(), self.builder.get_insert_block().unwrap().get_parent().unwrap());
                let (styp, index, member_type) = if let Type::StructType(name, named_fields) = typ{
                    let (styp, field) = self.struct_defs.get(&name).unwrap();
                    let (index, mtype)= named_fields.iter().fold_while((0, self.context.i8_type().as_basic_type_enum()), |(idx, mtype), (field_name, field_type)|{
                            use itertools::FoldWhile::{Done, Continue};
                            if (field_name==&arg){
                                Done((idx, field_type.into_bte(self.context, self.struct_defs)))
                            } else {
                                Continue((idx+1, mtype))
                            }
                        }).into_inner();
                    (styp, index, mtype)
                } else {panic!("Pathident must be {{expr: ident (structType)}}.{{memberName: ident}}")};
                let member_ptr = self.builder.build_struct_gep(styp.as_basic_type_enum(), ptr, index, "struct_gep").unwrap();
                Some(self.builder.build_load(member_type, member_ptr, "load").unwrap())
            },
            Expr::SquareArgs(expr, vec) => todo!(),
        }
    }
}
