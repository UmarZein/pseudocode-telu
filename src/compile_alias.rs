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

use crate::parse::{PRATT_PARSER, FCParser, Rule, parse_expr, Expr, simple_expr_str};
use crate::{print_pair, print_pairs};
use super::{Type, Codegen};

impl<'a, 'ctx> Codegen<'a, 'ctx> where 'ctx:'a{
    pub(crate) fn memorize_alias(&self){

    }
}
