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
use inkwell::types::{BasicMetadataTypeEnum, FunctionType, BasicTypeEnum, BasicType, PointerType};
use inkwell::values::{BasicMetadataValueEnum, BasicValueEnum, FloatValue, FunctionValue, PointerValue, BasicValue, InstructionOpcode, AsValueRef, InstructionValue};
use inkwell::FloatPredicate;

use pest::Parser;
use pest::iterators::{Pairs, Pair};
use itertools::Itertools;

use std::collections::{HashMap, VecDeque};
use std::hint::unreachable_unchecked;

use crate::parse::{PRATT_PARSER, FCParser, Rule, parse_expr, Expr, simple_expr_str};
use crate::{print_pairs, print_pair};

#[derive(Debug)]
pub struct Codegen<'a, 'ctx> {
    pub context: &'ctx Context,
    pub module: &'a Module<'ctx>,
    pub builder: &'a Builder<'ctx>,
    pub functions: &'a mut HashMap<String, Vec<(FunctionValue<'ctx>, Type, Vec<(bool,bool,String,Type)>)>>,
    pub locals: &'a mut HashMap<(FunctionValue<'ctx>,String), (PointerValue<'ctx>,Type)>,
    // pub program_name: String,
}


#[derive(Debug,Clone,PartialEq,Eq)]
pub enum Type{
    Int,
    Float,
    Char,
    Bool,
    String,
    Void,
    VoidPtr,
    Array(bool,u32,Box<Type>),
    Ptr(Box<Type>),
}

impl<'ctx> Type{
    pub fn correct_alignment(&self) -> u32 {
        let tmp = (match self{
            Type::Int => std::mem::size_of::<usize>(),
            Type::Float => std::mem::size_of::<usize>(),
            Type::Char => 1,
            Type::Bool => 1, // because look at fn into_bte (it is i8)
            Type::String => std::mem::size_of::<usize>(),
            Type::Void => std::mem::size_of::<usize>(),
            Type::VoidPtr => std::mem::size_of::<usize>(),
            Type::Array(_, _, _) => todo!(),
            Type::Ptr(_) => std::mem::size_of::<usize>(),
        }) as u32;
        info!("{self:?}'s alignment is {tmp}");
        tmp
    }
    pub fn into_bte(&self, context: &'ctx Context) -> BasicTypeEnum<'ctx>{
        match self{
            Type::Int     => context.i64_type().into(),
            Type::Float   => context.f64_type().into(),
            Type::Char    => context.i8_type().into(),
            Type::Bool    => context.i8_type().into(),
            Type::String  => context.i8_type().ptr_type(AddressSpace::default()).into(),
            Type::VoidPtr => context.i8_type().ptr_type(AddressSpace::default()).into(),
            Type::Array(one,s,i)  => i.as_ref().into_bte(context).array_type(*s).into(),
            Type::Ptr(i)  => i.as_ref().into_bte(context).ptr_type(AddressSpace::default()).into(),
            Type::Void => panic!("Void type should not be turned into BasicTypeEnum"),
        }
    }
    pub fn ptr_type(&self, context: &'ctx Context, addressspace: AddressSpace) -> PointerType<'ctx> {
        match self{
            Type::Int     => context.i64_type().ptr_type(addressspace),
            Type::Float   => context.f64_type().ptr_type(addressspace),
            Type::Char    => context.i8_type().ptr_type(addressspace),
            Type::Bool    => context.bool_type().ptr_type(addressspace),
            Type::String  => context.i8_type().ptr_type(AddressSpace::default()).ptr_type(addressspace),
            Type::VoidPtr => context.i8_type().ptr_type(AddressSpace::default()).ptr_type(addressspace),
            Type::Array(one,s,i)  => i.as_ref().into_bte(context).array_type(*s).ptr_type(addressspace),
            Type::Ptr(i)  => i.as_ref().into_bte(context).ptr_type(AddressSpace::default()).ptr_type(addressspace),
            Type::Void => panic!("Void type should not be turned into ptr type"),
        }
    }
    pub fn fn_type(&self, context: &'ctx Context, itype: &Vec<Type>, is_var_args: bool) -> FunctionType<'ctx> {
        let itype = itype.iter().map(|x|x.into_bte(context).into()).collect::<Vec<_>>();
        match self{
            Type::Int     => context.i64_type().fn_type(&itype, is_var_args),
            Type::Float   => context.f64_type().fn_type(&itype, is_var_args),
            Type::Char    => context.i8_type().fn_type(&itype, is_var_args),
            Type::Bool    => context.bool_type().fn_type(&itype, is_var_args),
            Type::String  => context.i8_type().ptr_type(AddressSpace::default()).fn_type(&itype, is_var_args),
            Type::VoidPtr => context.i8_type().ptr_type(AddressSpace::default()).fn_type(&itype, is_var_args),
            Type::Array(one,s,i)  => i.as_ref().into_bte(context).array_type(*s).fn_type(&itype, is_var_args),
            Type::Ptr(i)  => i.as_ref().into_bte(context).ptr_type(AddressSpace::default()).fn_type(&itype, is_var_args),
            Type::Void => context.void_type().fn_type(&itype, is_var_args),
        }
    }
}

impl<'a, 'ctx> Codegen<'a, 'ctx> where 'ctx:'a{
    fn add_function(&self, name: &'ctx str, ftype: FunctionType<'ctx>, linkage: Option<Linkage>)->FunctionValue<'ctx>{
        let f = self.module.add_function(name, ftype, linkage);
        //self.functions.insert(name, f);    
        return f;
    }
    fn find_function(&self, name: &str, itype: &[Type]) -> (FunctionValue<'ctx>,Type,Vec<(bool,bool,String,Type)>){
        info!("trying to find function {name} with {} argtypes",itype.len());
        info!("argtypes: {itype:#?}");
        let mut funcs = self.functions.get(&name.to_string()).unwrap_or_else(||panic!("{name} not found!")).clone();
        funcs.sort_by(|a, b|{
            b.0.get_params().len().cmp(&a.0.get_params().len())
        });
        if name=="input"{
            info!("printing funcs...");
            info!("{funcs:#?}");
        }
        let func = funcs.iter().find(|&e|{
            let fargtypes: Vec<_> = e.2.iter().map(|(a,b,c,d)|d.clone()).collect();
            if fargtypes.len()>itype.len(){ return false }
            if (!e.0.get_type().is_var_arg()) && fargtypes.len()!=itype.len(){ return false }
            
            // match all types f(int,int)==f(int,int)
            // but also, we want voidptr polymorphism...
            // such that f(*void)==f(*float)
            return fargtypes.iter().zip(&itype[..fargtypes.len()])
                .all(|(candidate,key)|{
                    info!("checking {candidate:?} and {key:?}");
                    match candidate.clone(){
                        Type::VoidPtr => {
                            match key{
                                Type::Ptr(_) => true,
                                _ => candidate==key,
                            }
                        },
                        _ => candidate==key,
                    }
                });
        }).expect(&format!("could not find function named {name} with {} arguments",itype.len()));
        func.clone()
    }
    #[inline]
    fn pair_to_type(context: &'ctx Context, pair: Pair<Rule>) -> Type{
        match pair.as_rule(){
            Rule::integer_type => Type::Int,
            Rule::real_type => Type::Float,
            Rule::bool_type => Type::Bool,
            Rule::char_type => Type::Char,
            Rule::string_type => Type::String,
            Rule::void_type => Type::Void,
            Rule::array_type => {
                let mut i = pair.into_inner();
                let mut array_dim = i.next().unwrap().into_inner();
                let one_indexed = array_dim.next().unwrap().as_str()=="1";
                let size = array_dim.next().unwrap().as_str().parse().unwrap();
                let inner_type = Self::pair_to_type(context, i.next().unwrap());
                Type::Array(one_indexed, size, Box::new(inner_type))
            },
            Rule::pointer_type => Type::Ptr(Box::new(Self::pair_to_type(context, pair.into_inner().next().unwrap()))),
            _ => unreachable!("pair = {pair:#?}")
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
        let code = std::fs::read_to_string(source_filename).unwrap_or_else(|e|panic!("stdio error: {e}\nfilename = {source_filename}"));
        let parsed = FCParser::parse(Rule::program, &code).unwrap();
        info!("done parsing {source_filename}");
        println!("printing pairs...");
        print_pairs(parsed.clone(), 0);
        println!("done printing pairs...");
        info!("done printing pairs");
        let main_fn = self.register_func_unnamed_params("main", Type::Int, vec![]);
        self.context.append_basic_block(main_fn, "mainf_entry");
        //TODO uncomment this: self.add_alloc();
        self.add_printf();
        self.add_scanf();
        self.add_output();
        self.add_time();
        self.add_rand();
        // self.add_powi();
        // self.add_powf();
        let _ = parsed.clone().map(|p|self.declare_funcs(p)).collect::<Vec<()>>();
        info!("done declaring functions");
        debug!("after debugging, locals[{}]={:#?}",self.locals.len(),self.locals);
        let _ = parsed.map(|p|self.compile_pest_output(p)).collect::<Vec<()>>();
    }
    
    fn process_parameter(context: &'ctx Context, pair:Pair<Rule>)->(bool,bool,Vec<String>,Type){
        if pair.as_rule()!=Rule::parameter{
            unreachable!()
        }
        let mut i = pair.into_inner();
        let mut invar = false;
        let mut outvar = false;
        let mut vars: Vec<_> = vec![];
        let mut partype = Type::Int; // WARNING: Int as default type...good idea?
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
    fn expr_type(&self, expr: &Expr)->Type{
        Self::raw_expr_type(self.context, self.locals, self.functions, &self.builder.get_insert_block().unwrap().get_parent().unwrap(), &expr)
    }
    fn raw_expr_type(
        context: &'ctx Context, 
        locals: &HashMap<(FunctionValue<'ctx>,String), (PointerValue<'ctx>,Type)>, 
        functions: &HashMap<String, Vec<(FunctionValue<'ctx>, Type, Vec<(bool,bool,String,Type)>)>>,
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
            E::Mul(bee) => Self::raw_expr_type(context, locals, functions, cur_func, &bee.as_ref().clone().0),
            E::Div(bee) => {
                todo!("unimplemented: im confused whether Div should handle Idv's job as wel?")
            },
            E::Idv(bee)|E::Mod(bee) => Type::Int,
            E::Pow(bee) => Type::Float,
            E::Neg(be) => Self::raw_expr_type(context, locals, functions, cur_func, be.as_ref()),
            E::Pathident(s) => locals.get(&(*cur_func,s.clone())).expect(&format!("could not find {s}")).1.clone(),
            E::Call(s, ve) => {
                let argtypes: Vec<_> = ve.iter().map(|e|Self::raw_expr_type(context, locals, functions, cur_func, &e)).collect();
                // this code is beautifully ugly
                functions.get(&s.clone()).unwrap().iter()
                    .find(|&(e,t,v)|{
                        let fargtypes = v.iter()
                            .map(|x|x.3.clone())
                            .collect::<Vec<_>>();
                        fargtypes == argtypes
                    }
                    ).unwrap().1.clone()
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
    fn compile_expr(&self, expr: Expr) -> Option<BasicValueEnum<'ctx>> {
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
            Expr ::Gt(bee) => {
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
            Expr ::Lt(bee) => {
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
            Expr ::Ge(bee) => {
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
            Expr ::Le(bee) => {
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
                        let t = i.as_ref().into_bte(self.context).into_pointer_type();
                        let aaddr = self.builder.build_ptr_to_int(a.into_pointer_value(), self.context.i64_type(), "ptrtoint").unwrap();
                        let res = self.builder.build_int_add(aaddr, b.into_int_value(), "intadd").unwrap();
                        self.builder.build_int_to_ptr(res, t, "inttoptr").unwrap().into()
                    },
                    (Type::Int,Type::Ptr(i)) => {
                        let t = i.as_ref().into_bte(self.context).into_pointer_type();
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
                        let t = i.as_ref().into_bte(self.context).into_pointer_type();
                        let aaddr = self.builder.build_ptr_to_int(a.into_pointer_value(), self.context.i64_type(), "ptrtoint").unwrap();
                        let res = self.builder.build_int_sub(aaddr, b.into_int_value(), "intsub").unwrap();
                        self.builder.build_int_to_ptr(res, t, "inttoptr").unwrap().into()
                    },
                    (Type::Int,Type::Ptr(i)) => {
                        let t = i.as_ref().into_bte(self.context).into_pointer_type();
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
            Expr::Pathident(path) => {
                let (ptr,typ): (PointerValue<'ctx>, Type) = self.locals.get(
                    &(self.builder.get_insert_block().unwrap().get_parent().unwrap(),path.clone())
                    ).expect(&format!("did not find {path}")).clone();
                //println!("found {path} in locals");
                if let Type::Void = typ{
                    return None
                }
                let btetyp = typ.into_bte(self.context);
                let x = (match typ.clone(){
                    Type::Void => todo!(),
                    Type::VoidPtr => todo!(),
                    Type::Int => self.builder.build_load(btetyp.into_int_type(), ptr, "loadintpath").unwrap(),
                    Type::Float => self.builder.build_load(btetyp.into_float_type(), ptr, "loadfloatpath").unwrap(),
                    Type::Char => self.builder.build_load(btetyp.into_int_type(), ptr, "loadcharpath").unwrap(),
                    Type::Bool => self.builder.build_load(btetyp.into_int_type(), ptr, "loadboolpath").unwrap(),
                    Type::String => self.builder.build_load(btetyp.into_pointer_type(), ptr, "loadstringpath").unwrap(),
                    Type::Array(one, s, i) => self.builder.build_load(btetyp.into_array_type(), ptr, "loadarraypath").unwrap(),
                    Type::Ptr(_) => self.builder.build_load(btetyp.into_pointer_type(), ptr, "loadptrpath").unwrap(), 
                });
                x.as_instruction_value().unwrap().set_alignment(typ.correct_alignment()).unwrap();
                Some(x)
            },

            Expr::Call(name, args) => {
                if &name=="output"{
                    for (i,arg) in args.iter().enumerate(){
                        let argtype = Self::raw_expr_type(
                            self.context, self.locals, self.functions,
                            &self.builder.get_insert_block().unwrap().get_parent().unwrap(), &arg);
                        let (func, otyp, ityp) = self.find_function(&name, &[argtype.into()]);
                        if i>0{
                            let (func, otyp, ityp) = self.find_function("output_space", &[]);
                            let call = self.builder.build_direct_call(func, &[], "printnewline");
                            let call = call.unwrap().try_as_basic_value();
                        }
                        let call = self.builder.build_direct_call(func, 
                            &[self.compile_expr(arg.clone()).unwrap().into()], 
                            "print");
                        let call = call.unwrap().try_as_basic_value();
                    }
                    let (func,otyp,ityp) = self.find_function(&name, &[]);
                    let call = self.builder.build_direct_call(func, &[], "printnewline");
                    let call = call.unwrap().try_as_basic_value();

                    return None
                } else if &name=="input"{
                    let func = self.builder.get_insert_block().unwrap().get_parent().unwrap();
                    for (i,arg) in args.iter().enumerate(){
                        let varident = match &arg{
                            Expr::Pathident(name) => name.clone(),
                            _ => panic!("args in function 'input' should be variable identifiers"),
                        };
                        let (var_ptr, innertype) = self.locals.get(&(func, varident)).unwrap();
                        let (func, otyp, ityp) = self.find_function(&name, &[Type::Ptr(Box::new(innertype.clone())).into()]);
                        let call = self.builder.build_direct_call(func, 
                            &[(*var_ptr).into()], 
                            "input");
                        let call = call.unwrap().try_as_basic_value();
                    }
                    return None
                }
                let argtypes: Vec<_> = args.iter().map(|e|
                    Self::raw_expr_type(
                        self.context, 
                        self.locals, 
                        self.functions, 
                        &self.builder.get_insert_block().unwrap().get_parent().unwrap(),
                        &e)).collect();
                let (func,otyp,ityp) = self.find_function(&name, &argtypes);
                // check that for every out-type param, it's a pathident 
                // remember that out-type param are writeable
                for (ot,at) in ityp.iter().map(|(i,o,n,t)|*o).zip(args.iter()){
                    let at_is_ptr = match at{Expr::Pathident(_)=>true,_=>false};
                    assert!(!ot||at_is_ptr)
                }
                let input: Vec<BasicMetadataValueEnum> = args.iter().zip(ityp.iter()).map(
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
                global_value.set_alignment(4);
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
                let mut intype_blueprint: Vec<(bool,bool,String,Type)> = vec![];
                let mut outtype = Type::Int;
                let parameters: Vec<_> = i.clone().filter(|x|x.as_rule()==R::parameter)
                    .map(|x|Self::process_parameter(&self.context,x)).collect();
                for (inv,outv, vars, typ) in &parameters{
                    for var in vars{
                        intype_blueprint.push((*inv,*outv,var.clone(),typ.clone()));
                    }
                }
                let func = self.register_proc(name, outtype, intype_blueprint);
                let funcblock = self.context.append_basic_block(func, "entry");
                self.builder.position_at_end(funcblock);

                let mut parami = 0;
                for (inv, outv, vars, typ) in &parameters{
                    if *outv{
                        for var in vars.iter().rev(){
                            let p = func.get_nth_param(parami).unwrap();
                            self.locals.insert((func,var.clone()), (p.into_pointer_value(),typ.clone()));
                        }
                    }
                    else{
                        for var in vars.iter().rev(){
                            let p = func.get_nth_param(parami).unwrap();
                            let ptr = self.builder.build_alloca(typ.into_bte(self.context), &var).unwrap();
                            self.locals.insert((func,var.clone()), (ptr,typ.clone()));
                            let load_instr = self.builder.build_store(ptr, p).unwrap();
                            load_instr.set_alignment(typ.correct_alignment()).unwrap();
                        }
                    }
                    parami+=1;
                }


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
                let mut intype_blueprint: Vec<(String,Type)> = vec![];
                let mut intypes: Vec<Type> = vec![];
                let mut outtype = self.context.i8_type().as_basic_type_enum();
                let parameters: Vec<_> = i.clone().filter(|x|x.as_rule()==R::parameter)
                    .map(|x|Self::process_parameter(&self.context,x)).collect();
                for (inv,outv, vars, typ) in parameters.clone(){
                    for var in vars{
                        intype_blueprint.push((var.clone(),typ.clone()));
                        intypes.push(typ.clone().into());
                    }
                }


                let typename = i.clone().find(|x|{
                    match x.as_rule(){
                        R::integer_type|R::real_type|R::bool_type|R::string_type
                        |R::pointer_type|R::char_type|R::user_type|R::void_type|R::array_type => true,
                        _ => false
                    }
                }).unwrap();
                let outtyp = Self::pair_to_type(self.context, typename);
                let func = self.register_func(name, outtyp, intype_blueprint);
                //
                let funcblock = self.context.append_basic_block(func, "entry");
                self.builder.position_at_end(funcblock);
                let mut parami = 0;
                for (inv,outv, vars, typ) in parameters.iter(){
                    for var in vars.iter().rev(){
                        let p = func.get_nth_param(parami).unwrap();
                        let ptr = self.builder.build_alloca(typ.into_bte(self.context), &var).unwrap();
                        self.locals.insert((func,var.clone()), (ptr,typ.clone()));
                        let load_instr = self.builder.build_store(ptr, p).unwrap();
                        load_instr.set_alignment(typ.correct_alignment()).unwrap();
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
                    let var_ptr = self.builder.build_alloca(ty.into_bte(self.context), ident).unwrap();
                    let func = self.builder.get_insert_block().unwrap().get_parent().unwrap();
                    let val = k.next().unwrap();
                    self.locals.insert((func,ident.clone().to_string()), (var_ptr.clone(),ty.clone()));
                    let load_instr = self.builder.build_store(var_ptr.into(), self.pair_to_value(val)).unwrap();
                    load_instr.set_alignment(ty.correct_alignment()).unwrap();
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
                        let var_ptr = self.builder.build_alloca(ty.into_bte(self.context), x.as_str()).unwrap();
                        self.locals.insert((func,name.clone().to_string()), (var_ptr.clone(),ty.clone()));
                    }).collect();
                }

            },
            R::type_def => {
                todo!()
            }
            _ => return // to many cases just catch em all
        }

    }

    fn compile_pest_output(&mut self, pair: Pair<Rule>){
        //println!("compile_pest_output({})",pair.to_string());
        use Rule as R;
        let rule = pair.as_rule();
        info!("compiling rule {rule}");
        match rule{
            R::expr => {
                let exp = parse_expr(pair.into_inner());
                self.compile_expr(exp);
            }
            R::whlstmt => {
                let mut i = pair.into_inner();
                let cur_func = self.builder.get_insert_block().unwrap().get_parent().unwrap();
                //let checkblock = self.context.append_basic_block(cur_func, "check");
                let contblock = self.context.append_basic_block(cur_func, "contblock");
                let body = self.context.append_basic_block(cur_func, "whileblock");
                let expr = parse_expr(i.next().unwrap().into_inner());
                let compiled_expr = self.compile_expr(expr.clone()).unwrap().into_int_value();
                //self.builder.build_unconditional_branch(checkblock);
                //self.builder.position_at_end(checkblock);
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
                            // if thenblock has return statement, then the line below adds br after
                            // ret... this will cause error
                            if self.builder.get_insert_block().unwrap().get_terminator().is_none(){
                                self.builder.build_unconditional_branch(contblock);
                            }
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
                //
                // if elseblock has return statement, then the line below adds br after
                // ret... this will cause error
                if self.builder.get_insert_block().unwrap().get_terminator().is_none(){
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
                let func = self.builder.get_insert_block().unwrap().get_parent().unwrap();

                let (var_ptr, var_typ) = match next.as_rule(){
                    R::gep => {
                        let mut inner = next.into_inner();
                        let name = inner.next().unwrap().as_str().to_string();
                        let (ptr,typ): (PointerValue<'ctx>,Type) = self.locals.get(&(func, name)).unwrap().clone();
                        let index = parse_expr(inner.next().unwrap().into_inner());
                        let index = self.compile_expr(index).expect("index cannot be void/nil")
                                        .into_int_value();
                        let inner_typ = match typ{
                            Type::Array(one, size, body) => body.as_ref().clone(),
                            _ => unreachable!()
                        };
                        let elm_ptr = unsafe {
                            self.builder.build_gep(inner_typ.into_bte(self.context), ptr, &[index], "getelementptr").unwrap()
                        };
                        (elm_ptr, inner_typ)
                    },
                    R::pathident => self.locals.get(&(func, next.as_str().to_string())).unwrap().clone(),
                    _ => unreachable!(),
                };
                if let (Type::Ptr(_), Type::Int) = (var_typ.clone(),etyp){
                    todo!("implement assign int to ptr")
                } else {
                    let load_instr = self.builder.build_store(var_ptr.clone(), compiled_expr).unwrap();
                    load_instr.set_alignment(var_typ.correct_alignment()).unwrap();
                }
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
                    let etyp=Self::raw_expr_type(self.context, self.locals, self.functions,
                        &self.builder.get_insert_block().unwrap().get_parent().unwrap(),&exp);
                    if etyp!=Type::Int{
                        panic!("main return should be int, but type {etyp:#?} was found instead")
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
                        R::integer_type|R::konstanta|R::kamus|R::real_type|R::char_type|R::void_type
                        |R::bool_type|R::pointer_type|R::user_type|R::parameter|R::string_type|R::array_type => continue,
                        _ => unreachable!()
                    }
                }
                self.builder.build_return(None);
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
                        R::integer_type|R::konstanta|R::kamus|R::real_type|R::char_type|R::void_type
                        |R::bool_type|R::pointer_type|R::user_type|R::parameter|R::array_type|R::string_type => continue,
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
    pub fn register_proc(&mut self, name: &str, otype: Type, itype: Vec<(bool, bool, String,Type)>) -> FunctionValue<'ctx>{
        self._register_function(name, otype, itype, false, None)
    }
    pub fn register_func_unnamed_params(&mut self, name: &str, otype: Type, itype: Vec<(Type)>) -> FunctionValue<'ctx>{
        self._register_function(name, otype, 
            itype.iter().map(|t|(false,false,String::new(),t.clone())).collect(), 
            false, None)
    }
    pub fn register_func(&mut self, name: &str, otype: Type, itype: Vec<(String,Type)>) -> FunctionValue<'ctx>{
        self._register_function(name, otype, 
            itype.iter().map(|(s,t)|(false,false,s.clone(),t.clone())).collect(), 
            false, None)
    }
    pub fn register_libc_func_variadic(&mut self, name: &str, otype: Type, itype: Vec<Type>) -> FunctionValue<'ctx>{
        self._register_function(name, otype, 
            itype.iter().map(|t|(false,false,String::new(),t.clone())).collect(), 
            true, Some(Linkage::External))
    }
    pub fn register_variadic_libc_func(&mut self, name: &str, otype: Type, itype: Vec<Type>) -> FunctionValue<'ctx>{
        self._register_function(name, otype, 
            itype.iter().map(|t|(false,false,String::new(),t.clone())).collect(), 
            true, Some(Linkage::External))
    }
    pub fn register_libc_func(&mut self, name: &str, otype: Type, itype: Vec<Type>) -> FunctionValue<'ctx>{
        self._register_function(name, otype, 
            itype.iter().map(|t|(false,false,String::new(),t.clone())).collect(), 
            false, Some(Linkage::External))
    }
    pub fn _register_function(
        &mut self, 
        name: &str, 
        otype: Type, 
        itype:Vec<(bool,bool,String,Type)>, 
        is_var_args: bool,
        linkage: Option<Linkage>,
    ) -> FunctionValue<'ctx> {
        let func = self.module.add_function(
            &name, 
            otype
                .fn_type(
                    self.context,
                    &itype.iter()
                        .map(|(inv,outv,name,typ)|{
                            if !outv {typ.clone()}
                            else {Type::Ptr(Box::new(typ.clone()))}
                        })
                        .collect::<Vec<_>>(),
                    is_var_args,
                ), 
            linkage,
        );
        match self.functions.get_mut(name){
            None => {self.functions.insert(name.to_string(), vec![(func.clone(),otype,itype)]);},
            Some(x) => x.push((func.clone(),otype.clone(),itype))
        };
        func
    }
    pub fn add_alloc(&mut self){
        // malloc
        self.register_libc_func("malloc", Type::VoidPtr, vec![Type::Int]);
    }
    pub fn add_time(&mut self){
        self.register_libc_func("time", Type::Int, vec![Type::Int]);
    }
    pub fn add_rand(&mut self){
        self.register_libc_func("srand", Type::Void, vec![Type::Int]);
        self.register_libc_func("rand", Type::Int, vec![]);
    }
    pub fn add_printf(&mut self){
        self.register_variadic_libc_func("printf", Type::Int, vec![Type::String]);
    }
    pub fn add_scanf(&mut self){
        self.register_variadic_libc_func("scanf", Type::Int, vec![Type::VoidPtr]);
    }
    pub fn add_output(&mut self){
        let main_fn = self.module.get_function("main").unwrap();
        let entry =main_fn.get_first_basic_block().unwrap();
        self.builder.position_at_end(entry);

        let space = self.builder.build_global_string_ptr(" ", "space").unwrap();
        space.set_alignment(4);
        

        let newline_fstr = self.builder.build_global_string_ptr("\n", "newline").unwrap();
        newline_fstr.set_alignment(4);
        let char_fstr = self.builder.build_global_string_ptr("%c", "char_fstr").unwrap();
        char_fstr.set_alignment(4);
        let string_fstr = self.builder.build_global_string_ptr("%s", "string_fstr").unwrap();
        string_fstr.set_alignment(4);

        // story time: it took my at least 6 hours of the night to figure out that %lld is the
        // correct i64 format specifier rather than %ld
        let i64_fstr = self.builder.build_global_string_ptr("%lld", "long_fstr").unwrap();
        i64_fstr.set_alignment(4);
        let f64_fstr = self.builder.build_global_string_ptr("%f", "double_fstr").unwrap();
        f64_fstr.set_alignment(4);
        let bool_fstr = self.builder.build_global_string_ptr("%hhd", "bool_fstr").unwrap();
        bool_fstr.set_alignment(4);
        let printf = self.module.get_function("printf").unwrap();
        let scanf = self.module.get_function("scanf").unwrap();

        let func = self.register_func_unnamed_params("output_space", Type::Void, vec![]);
        let fblock = self.context.append_basic_block(func, "outputspace");
        self.builder.position_at_end(fblock);
        let pcall = self.builder.build_direct_call(
            printf, 
            &[
                space.as_pointer_value().into(), 
            ], 
            "printspace").unwrap();
        self.builder.build_return(None);

        let func = self.register_func_unnamed_params("output", Type::Void, vec![]);
        let fblock = self.context.append_basic_block(func, "outputentryempty");
        self.builder.position_at_end(fblock);
        let pcall = self.builder.build_direct_call(
            printf, 
            &[
                newline_fstr.as_pointer_value().into(), 
            ], 
            "printnewline").unwrap();
        self.builder.build_return(None);

        let func = self.register_func_unnamed_params("output", Type::Void, vec![Type::Int]);
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

        let func = self.register_func_unnamed_params("output", Type::Void, vec![Type::Float]);
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

        let func = self.register_func_unnamed_params("output", Type::Void, vec![Type::Bool]);
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

        let func = self.register_func_unnamed_params("output", Type::Void, vec![Type::Char]);
        let fblock = self.context.append_basic_block(func, "outputentrychar");
        self.builder.position_at_end(fblock);
        let param= func.get_first_param().unwrap();
        let pcall = self.builder.build_direct_call(
            printf, 
            &[
                char_fstr.as_pointer_value().into(), 
                param.into()
            ], 
            "printfchar").unwrap();
        self.builder.build_return(None);

        let func = self.register_func_unnamed_params("output", Type::Void, vec![Type::String]);
        let fblock = self.context.append_basic_block(func, "outputentrystring");
        self.builder.position_at_end(fblock);
        let param= func.get_first_param().unwrap();
        let pcall = self.builder.build_direct_call(
            printf, 
            &[
                string_fstr.as_pointer_value().into(), 
                param.into()
            ], 
            "printfstring").unwrap();
        self.builder.build_return(None);

        ////// 

        // let func = self.register_func_unnamed_params("input", Type::Void, vec![]);
        // let fblock = self.context.append_basic_block(func, "inputentryempty");
        // self.builder.position_at_end(fblock);
        // self.builder.build_return(None);

        let func = self.register_func_unnamed_params("input", Type::Void, vec![Type::Ptr(Box::new(Type::Int))]);
        let fblock = self.context.append_basic_block(func, "inputentryi64");
        self.builder.position_at_end(fblock);
        let param= func.get_first_param().unwrap();
        let pcall = self.builder.build_direct_call(
            scanf, 
            &[
                i64_fstr.as_pointer_value().into(), 
                param.into()
            ], 
            "scani64").unwrap();
        self.builder.build_return(None);

        let func = self.register_func_unnamed_params("input", Type::Void, vec![Type::Float]);
        let fblock = self.context.append_basic_block(func, "inputentryf64");
        self.builder.position_at_end(fblock);
        let param= func.get_first_param().unwrap();
        let pcall = self.builder.build_direct_call(
            scanf, 
            &[
                f64_fstr.as_pointer_value().into(), 
                param.into()
            ], 
            "scanf64").unwrap();
        self.builder.build_return(None);

        // let func = self.register_func_unnamed_params("input", Type::Void, vec![Type::Bool]);
        // let fblock = self.context.append_basic_block(func, "inputentrybool");
        // self.builder.position_at_end(fblock);
        // let param= func.get_first_param().unwrap();
        // let pcall = self.builder.build_direct_call(
        //     scanf, 
        //     &[
        //         bool_fstr.as_pointer_value().into(), 
        //         param.into()
        //     ], 
        //     "scanfbool").unwrap();
        // self.builder.build_return(None);

        let func = self.register_func_unnamed_params("input", Type::Void, vec![Type::Char]);
        let fblock = self.context.append_basic_block(func, "inputentrychar");
        self.builder.position_at_end(fblock);
        let param= func.get_first_param().unwrap();
        let pcall = self.builder.build_direct_call(
            scanf, 
            &[
                char_fstr.as_pointer_value().into(), 
                param.into()
            ], 
            "scanfchar").unwrap();
        self.builder.build_return(None);

        let func = self.register_func_unnamed_params("input", Type::Void, vec![Type::String]);
        let fblock = self.context.append_basic_block(func, "inputentrystring");
        self.builder.position_at_end(fblock);
        let param= func.get_first_param().unwrap();
        let pcall = self.builder.build_direct_call(
            scanf, 
            &[
                string_fstr.as_pointer_value().into(), 
                param.into()
            ], 
            "scanfstring").unwrap();
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
