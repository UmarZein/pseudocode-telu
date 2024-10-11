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
use inkwell::types::{AnyTypeEnum, BasicMetadataTypeEnum, BasicType, BasicTypeEnum, FunctionType, PointerType, StructType};
use inkwell::values::{BasicMetadataValueEnum, BasicValueEnum, FloatValue, FunctionValue, StructValue, PointerValue, BasicValue, InstructionOpcode, AsValueRef, InstructionValue};
use inkwell::FloatPredicate;

use pest::Parser;
use pest::iterators::{Pairs, Pair};
use itertools::{Either, Itertools};

use std::collections::{HashMap, VecDeque};
use std::hint::unreachable_unchecked;
use std::ops::Deref;

use crate::parse::{PRATT_PARSER, FCParser, Rule, parse_expr, Expr, simple_expr_str};
use crate::{print_pair, print_pairs};
use super::{Type, Codegen};

impl<'ctx> Type{
    // pub fn correct_alignment(&self, struct_defs: &HashMap<(String, ImplementationLevel), (StructType<'ctx>, Vec<(String,Type)>)>) -> u32 {
    //     let tmp = (match self{
    //         Type::Int => std::mem::size_of::<usize>(),
    //         Type::Float => std::mem::size_of::<usize>(),
    //         Type::Char => 1, // 1-byte char impl has been chosen for this language
    //         Type::Bool => 1, // because look at fn into_bte (it is i8)
    //         Type::String => std::mem::size_of::<usize>(),
    //         Type::Void => std::mem::size_of::<usize>(),
    //         Type::VoidPtr => std::mem::size_of::<usize>(),
    //         Type::Array(_, _, _) => todo!(),
    //         Type::Ptr(_) => std::mem::size_of::<usize>(),
    //         Type::StructType(a, name, fields) => {
    //             let (styp, vstyp) = struct_defs.get(&(name.clone(), ImplementationLevel::Usermade)).unwrap();
    //             styp.get_alignment();
    //             // uhh what now? 
    //             panic!();
    //         },
    //         Type::FnType(implementation_level, _, _, vec) => todo!(),
    //     }) as u32;
    //     info!("{self:?}'s alignment is {tmp}");
    //     tmp
    // }
    
    // pub fn get_basic_type(&self, 
    //     context: &'ctx Context,
    //     functions: &HashMap<(String, ImplementationLevel), Vec<(FunctionValue<'ctx>, Type, Vec<(bool,bool,String,Type)>)>>,
    //     struct_defs: &HashMap<(String, ImplementationLevel), (StructType<'ctx>, Vec<(String,Type)>)>) -> BasicTypeEnum<'ctx>{
    //     match self{
    //         Type::Int     => (context.i64_type().into()),
    //         Type::Float   => (context.f64_type().into()),
    //         Type::Char    => (context.i8_type().into()),
    //         Type::Bool    => (context.i8_type().into()),
    //         Type::String  => (context.i8_type().ptr_type(AddressSpace::default()).into()),
    //         Type::VoidPtr => (context.i8_type().ptr_type(AddressSpace::default()).into()),
    //         Type::Array(one,s,i)  => (i.as_ref().into_bte(context, struct_defs).array_type(*s).into()),
    //         Type::Ptr(i)  => (i.as_ref().into_bte(context, struct_defs).ptr_type(AddressSpace::default()).into()),
    //         Type::StructType(impl_level, name, fields) => {
    //             context.const_struct
    //         },
    //         Type::Void => context.void_type().into(),
    //         Type::FnType(implementation_level, name, out_type, in_type) => {
    //             let (ftyp, _, _) = functions.get(&(name.clone(), *implementation_level)).unwrap().first().unwrap();
    //             
    //         },
    //     }
    // }
    pub fn into_bmte(&self, context: &'ctx Context, struct_defs: &HashMap<String, (StructType<'ctx>, Vec<(String,Type)>)>) -> BasicMetadataTypeEnum<'ctx>{
        match self{
            Type::Int     => context.i64_type().into(),
            Type::Float   => context.f64_type().into(),
            Type::Char    => context.i8_type().into(),
            Type::Bool    => context.i8_type().into(),
            Type::String  => context.i8_type().ptr_type(AddressSpace::default()).into(),
            Type::VoidPtr => context.i8_type().ptr_type(AddressSpace::default()).into(),
            Type::Array(one,s,i)  => i.as_ref().into_bte(context, struct_defs).array_type(*s).into(),
            Type::Ptr(i)  => i.as_ref().into_bte(context, struct_defs).ptr_type(AddressSpace::default()).into(),
            Type::StructType(name, fields) => {
                let (styp, vstyp) = struct_defs.get(name).unwrap();
                styp.clone().into()
            },
            Type::Void => panic!("Void type should not be turned into BasicTypeEnum"),
            Type::FnType(implementation_level, _, _, vec) => todo!(),
        }
    }
    pub fn into_ate(&self, context: &'ctx Context, struct_defs: &HashMap<String, (StructType<'ctx>, Vec<(String,Type)>)>) -> AnyTypeEnum<'ctx>{
        match self{
            Type::Int     => context.i64_type().into(),
            Type::Float   => context.f64_type().into(),
            Type::Char    => context.i8_type().into(),
            Type::Bool    => context.i8_type().into(),
            Type::String  => context.i8_type().ptr_type(AddressSpace::default()).into(),
            Type::VoidPtr => context.i8_type().ptr_type(AddressSpace::default()).into(),
            Type::Array(one,s,i)  => i.as_ref().into_bte(context, struct_defs).array_type(*s).into(),
            Type::Ptr(i)  => i.as_ref().into_bte(context, struct_defs).ptr_type(AddressSpace::default()).into(),
            Type::StructType(name, fields) => {
                let (styp, vstyp) = struct_defs.get(name).unwrap();
                styp.clone().into()
            },
            Type::Void => context.void_type().into(),
            Type::FnType(implementation_level, _, _, vec) => todo!(),
        }
    }
    pub fn into_bte(&self, context: &'ctx Context, struct_defs: &HashMap<String, (StructType<'ctx>, Vec<(String,Type)>)>) -> BasicTypeEnum<'ctx>{
        match self{
            Type::Int     => context.i64_type().as_basic_type_enum(),
            Type::Float   => context.f64_type().as_basic_type_enum(),
            Type::Char    => context.i8_type().as_basic_type_enum(),
            Type::Bool    => context.i8_type().as_basic_type_enum(),
            Type::String  => context.i8_type().ptr_type(AddressSpace::default()).as_basic_type_enum(),
            Type::VoidPtr => context.i8_type().ptr_type(AddressSpace::default()).as_basic_type_enum(),
            Type::Array(one,s,i)  => i.as_ref().into_bte(context, struct_defs).array_type(*s).as_basic_type_enum(),
            Type::Ptr(i)  => i.as_ref().into_bte(context, struct_defs).ptr_type(AddressSpace::default()).as_basic_type_enum(),
            Type::StructType(name, fields) => {
                let (styp, vstyp) = struct_defs.get(name).unwrap();
                styp.as_basic_type_enum()
            },
            Type::Void => panic!("Void type should not be turned into BasicTypeEnum"),
            Type::FnType(implementation_level, _, _, vec) => todo!(),
        }
    }
    pub fn ptr_type(self) -> Type {
        Type::Ptr(Box::new(self))
        // match self{
        //     Type::Int     => context.i64_type().ptr_type(addressspace),
        //     Type::Float   => context.f64_type().ptr_type(addressspace),
        //     Type::Char    => context.i8_type().ptr_type(addressspace),
        //     Type::Bool    => context.bool_type().ptr_type(addressspace),
        //     Type::String  => context.i8_type().ptr_type(AddressSpace::default()).ptr_type(addressspace),
        //     Type::VoidPtr => context.i8_type().ptr_type(AddressSpace::default()).ptr_type(addressspace),
        //     Type::Array(one,s,i)  => todo!(),//i.as_ref().into_bte(context, struct_defs).array_type(*s).ptr_type(addressspace),
        //     Type::Ptr(i)  => i.deref().ptr_type(context, addressspace, struct_defs).ptr_type(addressspace),
        //     Type::StructType(a, name, fields) => { struct_defs.get(&(name.clone(), ImplementationLevel::Usermade)).unwrap().0.ptr_type(addressspace) },
        //     Type::Void => panic!("Void type should not be turned into ptr type"),
        // }
    }
    pub fn compile(&self,
        context: &'ctx Context,
        struct_defs: &HashMap<String, (StructType<'ctx>, Vec<(String,Type)>)>,

    ) -> AnyTypeEnum<'ctx>{
        match self{
            Type::Int     => context.i64_type().into(),
            Type::Float   => context.f64_type().into(),
            Type::Char    => context.i8_type().into(),
            Type::Bool    => context.bool_type().into(),
            Type::String  => context.i8_type().ptr_type(AddressSpace::default()).into(),
            Type::VoidPtr => context.i8_type().ptr_type(AddressSpace::default()).into(),
            Type::Array(one,s,i)  => i.as_ref().into_bte(context, struct_defs).array_type(*s).into(),
            Type::Ptr(i)  => i.as_ref().into_bte(context, struct_defs).ptr_type(AddressSpace::default()).into(),
            Type::StructType(name, fields) => { 
                let (styp, vstyp) = struct_defs.get(name).unwrap();
                styp.clone().into()
            },
            Type::Void => context.void_type().into(),
            Type::FnType(implementation_level, name, out_type, itype) => {
                Self::compile_fn(context, struct_defs, out_type.deref().clone(), &itype.iter().map(|(in_,out_,name,typ)|typ.clone()).collect::<Vec<_>>(), false).into()
            },
        }
    }
    fn compile_fn(context: &'ctx Context, struct_defs: &HashMap<String, (StructType<'ctx>, Vec<(String,Type)>)>, out_type: Type, itype: &[Type], is_var_args: bool) -> FunctionType<'ctx>{
        let itype = itype.iter().map(|x|x.into_bte(context, struct_defs).into()).collect::<Vec<_>>();
        match out_type{
            Type::Int     => context.i64_type().fn_type(&itype, is_var_args),
            Type::Float   => context.f64_type().fn_type(&itype, is_var_args),
            Type::Char    => context.i8_type().fn_type(&itype, is_var_args),
            Type::Bool    => context.bool_type().fn_type(&itype, is_var_args),
            Type::String  => context.i8_type().ptr_type(AddressSpace::default()).fn_type(&itype, is_var_args),
            Type::VoidPtr => context.i8_type().ptr_type(AddressSpace::default()).fn_type(&itype, is_var_args),
            Type::Array(one,s,i)  => todo!(),//i.as_ref().into_bte(context, struct_defs).array_type(*s).fn_type(&itype, is_var_args),
            Type::Ptr(i)  => i.as_ref().into_bte(context, struct_defs).ptr_type(AddressSpace::default()).fn_type(&itype, is_var_args),
            Type::StructType(name, fields) => { 
                let (styp, vstyp) = struct_defs.get(&name).unwrap();
                styp.fn_type(&itype, is_var_args)
            },
            Type::Void => context.void_type().fn_type(&itype, is_var_args),
            Type::FnType(linkage, _, _, vec) => todo!(),
        }
    } 
    pub fn fn_type(self, linkage: Option<Linkage>, name: &str, param_types: &[(bool,bool,String,Type)]) -> Type {
        Type::FnType(linkage, name.to_string(), Box::new(self), Vec::from(param_types))
        //let itype = itype.iter().map(|x|x.into_bte(context, struct_defs).into()).collect::<Vec<_>>();
        //match self{
        //    Type::Int     => context.i64_type().fn_type(&itype, is_var_args),
        //    Type::Float   => context.f64_type().fn_type(&itype, is_var_args),
        //    Type::Char    => context.i8_type().fn_type(&itype, is_var_args),
        //    Type::Bool    => context.bool_type().fn_type(&itype, is_var_args),
        //    Type::String  => context.i8_type().ptr_type(AddressSpace::default()).fn_type(&itype, is_var_args),
        //    Type::VoidPtr => context.i8_type().ptr_type(AddressSpace::default()).fn_type(&itype, is_var_args),
        //    Type::Array(one,s,i)  => i.as_ref().into_bte(context, struct_defs).array_type(*s).fn_type(&itype, is_var_args),
        //    Type::Ptr(i)  => i.as_ref().into_bte(context, struct_defs).ptr_type(AddressSpace::default()).fn_type(&itype, is_var_args),
        //    Type::StructType(a, name, fields) => { todo!() },
        //    Type::Void => context.void_type().fn_type(&itype, is_var_args),
        //}
    }
}
