#![allow(warnings)]
// RUST_LOG=info cargo r && clang-17 -lm program.o -o program && ./program
// TODO: 
//  - reserve keywords: template, macro,
//  - implement all primitives: u8,i8,u16,i16,u32,i32,u64,i64,f32,f64,char,boolean,usize,isize
//  - fix boolean type name from bool to boolean
use log::{debug, error, log_enabled, info, Level};


extern crate pest;
#[macro_use]
extern crate pest_derive;
use std::collections::HashMap;
use std::ffi::OsStr;

use inkwell::context::Context;
use inkwell::execution_engine::JitFunction;
use inkwell::module::Linkage;
use inkwell::targets::{Target, InitializationConfig, TargetMachine, RelocMode, CodeModel, FileType};
use parse::FCParser;
use pest::{iterators::*, Parser};

use parse::Rule;
use std::process::{Command, Output, exit};


use crate::parse::{parse_expr, PRATT_PARSER};
mod parse;
mod compile_alias;
mod compile_funcs;
mod type_impl;
mod compile_pest;
mod compile_expr;
mod compile_types;
use inkwell::module::{Module};
use inkwell::types::StructType;

#[derive(Debug)]
pub struct Codegen<'a, 'ctx> {
    pub context: &'ctx Context,
    pub module: &'a Module<'ctx>,
    pub builder: &'a Builder<'ctx>,
    pub aliases: &'a mut HashMap<String, Type>, // TODO: dunno how to do type aliasing
    pub functions: &'a mut HashMap<String, Vec<(FunctionValue<'ctx>, Type, Vec<(bool,bool,String,Type)>)>>,
    // (FunctionScope, varIdent) -> (Ptr, varTyp) # returns the variable under the function scope
    pub locals: &'a mut HashMap<(FunctionValue<'ctx>,String), (PointerValue<'ctx>,Type)>,
    // (StructName, Builtin) -> (Struct, Fields: <Name, FieldTyp>) 
    pub struct_defs: &'a mut HashMap<String, (StructType<'ctx>, Vec<(String,Type)>)>,
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
    StructType(String, Vec<(String, Type)>),
    OpaqueType(String),
    FnType(Option<Linkage>, String, Box<Type>, Vec<(bool, bool, String, Type)>),
    //Tuple(Vec<Type>),
    //Enum(Vec<String>),
    Array(bool,u32,Box<Type>),
    Ptr(Box<Type>),
}


use inkwell::builder::{Builder, self};
use inkwell::types::{BasicMetadataTypeEnum, BasicTypeEnum};
use inkwell::values::{BasicMetadataValueEnum, BasicValueEnum, FloatValue, FunctionValue, PointerValue, BasicValue};
use inkwell::{FloatPredicate, OptimizationLevel, AddressSpace};

use pest::iterators::{Pairs, Pair};
use itertools::Itertools;

fn input<T: From<String>>() -> T{
    let mut s = String::new();
    std::io::stdin().read_line(&mut s).unwrap();    
    return s.into()
}

fn main() {
    println!("please input filename:");
    //let prog_file = &input::<String>();
    let prog_file = "./simple_program.tups";
    env_logger::builder()
        .target(env_logger::Target::Pipe(Box::new(std::fs::File::create("debug.log").unwrap())))
        .filter_level(log::LevelFilter::Debug)
        .init();
    
    Target::initialize_native(&InitializationConfig::default()).expect("Failed to initialize native target");
    info!("TargetMachine = {}",TargetMachine::get_default_triple().as_str().to_str().unwrap());
    info!("current directory = {}",std::env::current_dir().unwrap().display());

    let triple = TargetMachine::get_default_triple();
    let cpu = TargetMachine::get_host_cpu_name().to_string();
    let features = TargetMachine::get_host_cpu_features().to_string();
    let target = Target::from_triple(&triple).unwrap();
    info!("triple: {triple}");
    info!("cpu: {cpu}");
    info!("features: {features}");

    let optlev = OptimizationLevel::None;
    const relocmode: RelocMode = if cfg!(windows) { RelocMode::DynamicNoPic } else {RelocMode::PIC};
    let codemodel = CodeModel::Small;

    info!("optimization level: {optlev:?}");
    info!("relocation mode: {relocmode:?}");
    info!("code model: {codemodel:?}");

    let machine = target
        .create_target_machine(
            &triple,
            &cpu,
            &features,
            optlev,
            relocmode,
            codemodel,//TODO: change to Small but idk if it will break things
        )
        .unwrap();
    info!("initialized target machined");

    let context = Context::create();
    let module = context.create_module("program");
    let builder = context.create_builder();
    let mut cg=Codegen{
        context: &context,
        module: &module,
        builder: &builder,
        aliases: &mut HashMap::new(),
        functions: &mut HashMap::new(),
        locals: &mut HashMap::new(),    
        struct_defs: &mut HashMap::new(),
        // program_name: String::from("program_out")
    };
    cg.compile_program(prog_file);
    info!("compiled program");
    println!("{}",module.print_to_string().to_string());
    let dest = "program.o";
    let dest_asm = "program.asm";
    const program_name: &str = if cfg!(windows){"program.exe"} else {"program"};
    machine.write_to_file(&module, FileType::Object, dest.as_ref()).unwrap();
    machine.write_to_file(&module, FileType::Assembly, dest_asm.as_ref()).unwrap();
    info!("written to file {dest}");
    let clang = get_clang(dest, program_name).unwrap_or_else(|x|{
        info!("{x}");
        panic!("{x}");
    });
    println!("compile with {clang} -lm {dest} -o {program_name}")

}
// const PROGRAM_EX: &str = include_str!("program_ex.txt");
// const EXPR_EX: &str = include_str!("expr_ex.txt");

fn get_clang(ofile: &str, name: &str) -> Result<String, String> {
    let x = &123;
    // Try running clang-17
    if let Ok(output) = Command::new("clang-17").arg("--version").output() {
        if output.status.success() {
            return Ok("clang-17".into())
        }
    }
    
    // If clang-17 is not found, fallback to clang and check version
    if let Ok(output) = Command::new("clang").arg("--version").output() {
        if output.status.success() {
            let version_output = String::from_utf8_lossy(&output.stdout);
            if version_output.contains("clang version 17") {
                return Ok("clang".into())
            }
        }
    }

    Err("Neither clang-17 nor clang version 17 found.".into())
}


impl std::fmt::Display for Rule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Rule::not => write!(f,"not"),
            Rule::land => write!(f,"land"),
            Rule::lor => write!(f,"lor"),
            Rule::zero_or_one => write!(f,"zero_or_one"),
            Rule::array_dim => write!(f,"array_dim"),
            Rule::array_type => write!(f,"array_type"),
            Rule::ident => write!(f,"ident"),
            Rule::WHITESPACE => write!(f,"WHITESPACE"),
            Rule::uint => write!(f,"uint"),
            Rule::zint => write!(f,"zint"),
            Rule::int => write!(f,"int"),
            Rule::float => write!(f,"float"),
            Rule::bool => write!(f,"bool"),
            Rule::char => write!(f,"char"),
            Rule::string => write!(f,"string"),
            Rule::literal_primitives => write!(f,"literal_primitives"),
            Rule::literal => write!(f,"literal"),
            Rule::COMMENT => write!(f,"COMMENT"),
            Rule::keywords => write!(f,"keywords"),
            Rule::primitives => write!(f,"primitives"),
            Rule::pointer_type => write!(f,"pointer_type"),
            Rule::typename => write!(f,"typename"),
            Rule::type_field => write!(f,"type_field"),
            Rule::const_type_field => write!(f,"const_type_field"),
            Rule::type_def => write!(f,"type_def"),
            Rule::kamus => write!(f,"kamus"),
            Rule::konstanta => write!(f,"konstanta"),
            Rule::param_io => write!(f,"param_io"),
            Rule::parameter => write!(f,"parameter"),
            Rule::expr => write!(f,"expr"),
            Rule::infix => write!(f,"infix"),
            Rule::add => write!(f,"add"),
            Rule::sub => write!(f,"sub"),
            Rule::mul => write!(f,"mul"),
            Rule::div => write!(f,"div"),
            Rule::idv => write!(f,"idv"),
            Rule::mdl => write!(f,"mod"),
            Rule::neq => write!(f,"neq"),
            Rule::equ => write!(f,"equ"),
            Rule::pow => write!(f,"pow"),
            Rule::lt => write!(f,"lt"),
            Rule::le => write!(f,"le"),
            Rule::gt => write!(f,"gt"),
            Rule::ge => write!(f,"ge"),
            Rule::prefix => write!(f,"prefix"),
            Rule::neg => write!(f,"neg"),
            Rule::postfix => write!(f,"postfix"),
            //Rule::fac => write!(f,"fac"),
            Rule::primary => write!(f,"primary"),
            Rule::algoritma => write!(f,"algoritma"),
            Rule::procedure_def => write!(f,"procedure_def"),
            Rule::function_def => write!(f,"function_def"),
            Rule::typealias => write!(f,"typealias"),
            Rule::retstmt => write!(f,"retstmt"),
            Rule::asgnstmt => write!(f,"asgnstmt"),
            Rule::ifstmt => write!(f,"ifstmt"),
            Rule::whlstmt => write!(f,"whlstmt"),
            Rule::stmt => write!(f,"stmt"),
            Rule::mainprogram => write!(f,"mainprogram"),
            Rule::program => write!(f,"program"),
            Rule::user_type => write!(f,"user_type"),
            Rule::nil => write!(f,"nil"),
            Rule::integer_type => write!(f,"integer_type"),
            Rule::real_type => write!(f,"real_type"),
            Rule::bool_type => write!(f,"bool_type"),
            Rule::char_type => write!(f,"char_type"),
            Rule::string_type => write!(f,"string_type"),
            Rule::char => write!(f,"char"),
            Rule::charwrapper => write!(f,"charwrapper"),
            Rule::stringwrapper => write!(f,"stringwrapper"),
            Rule::void_type => write!(f,"void_type"),
            Rule::ifcond => write!(f,"ifcond"),
            Rule::stmt0 => write!(f,"stmt0"),
            Rule::stmt1 => write!(f,"stmt1"),
            Rule::round_brackets_args => write!(f, "round_brackets_args"),
            Rule::square_brackets_args => write!(f, "square_brackets_args"),
            Rule::dot_arg => write!(f, "dot_arg"),
            Rule::linear_expr => write!(f, "linear_expr"),
            Rule::enclosed_expr => write!(f, "enclosed_expr"),
        }
    }
}
const DBGIND: &str = "  | ";
fn print_pair(p: Pair<Rule>, i: usize) {
    print!("{}{}", DBGIND.repeat(i), p.as_rule());
    let s = p.as_str().clone();
    let inner = p.into_inner();
    if let None = inner.clone().next(){
        print!(": {s}");
    }
    println!();
    print_pairs(inner, i+1)
}
fn print_pairs(mut ps: Pairs<Rule>, i: usize) {
    while let Some(p) = ps.next() {
        print_pair(p, i);
    }
}

