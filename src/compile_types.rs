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
use crate::parse::{parse_expr, simple_expr_str, Expr, FCParser, Rule, PRATT_PARSER};
use crate::{print_pair, print_pairs};

impl<'a, 'ctx> Codegen<'a, 'ctx>
where
    'ctx: 'a,
{
    pub(crate) fn declare_structs(&mut self, pair: Pair<Rule>) {
        use Rule as R;
        match pair.as_rule() {
            R::type_def => {
                let mut j = pair.into_inner();
                let struct_name = j.next().unwrap().as_str().to_string();
                let mut v: Vec<(String, Type)> = vec![];
                for type_field in j.rev() {
                    let mut k = type_field.into_inner().rev();
                    let context = self.context;
                    let ty = Self::pair_to_type_prologue(&context, k.next().unwrap());
                    let var_ptrs: Vec<_> = k
                        .map(|x| {
                            let name = x.as_str();
                            v.push((name.to_string(), ty.clone()));
                        })
                        .collect();
                }
                v.reverse();
                let st_typ = self.context.struct_type(
                    &v.iter()
                        .map(|(name, typ)| typ.into_bte_prologue(self.context, self.aliases, self.struct_defs))
                        .collect::<Vec<_>>(),
                    false,
                );
                self.struct_defs.insert(struct_name, (st_typ, v.clone()));
            }
            other => return,
        }
    }
    pub(crate) fn declare_aliases(&mut self, pair: Pair<Rule>) {
        use Rule as R;
        match pair.as_rule() {
            R::typealias => {
                let mut j = pair.into_inner();
                let alias_name = j.next().unwrap().as_str().to_string();
                let corresponding_type = j.next().unwrap();
                self.aliases.insert(alias_name.clone(), Self::pair_to_type_prologue(self.context, corresponding_type));
            }
            other => return,
        }
    }
    pub(crate) fn pair_to_type_prologue(context: &'ctx Context, pair: Pair<Rule>) -> Type{
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
                let inner_type = Self::pair_to_type_prologue(context, i.next().unwrap());
                Type::Array(one_indexed, size, Box::new(inner_type))
            },
            Rule::pointer_type => Type::Ptr(Box::new(Self::pair_to_type_prologue(context, pair.into_inner().next().unwrap()))),
            Rule::user_type => {
                let struct_name = pair.as_str().to_string();
                Type::OpaqueType(struct_name.clone())
            },
            
            _ => unreachable!("pair = {pair:#?}")
        }
    }
}

impl<'ctx> Type {
    pub(crate) fn translate_opaque(
        self,
        struct_defs: &HashMap<String, (StructType<'ctx>, Vec<(String, Type)>)>,
        aliases: &HashMap<String, Type>,
    ) -> Type {
        let mut cur = self;
        while let Type::OpaqueType(name) = &cur {
            if let Some((styp, fields)) = struct_defs.get(name) {
                //
                // NOTE: StructType's fields may have OpaqueType. This is unavoidable because
                // consider the case:
                //
                // struct S{
                //     m: pointer to S
                // }
                //
                // To avoid infinite recursion, its member `m` must be a pointer to an opaque type
                //
                return Type::StructType(name.clone(), fields.clone());
            }
            if let Some(typ) = aliases.get(name) {
                cur = typ.clone()
            } else {
                panic!("cannot identify opaque type `{name}`")
            }
        }
        cur
    }
}
