#![allow(warnings)]
// RUST_LOG=info cargo r && clang-17 -lm program.o -o program && ./program
use log::{debug, error, log_enabled, info, Level};


extern crate pest;
#[macro_use]
extern crate pest_derive;
use std::collections::HashMap;

use inkwell::context::Context;
use inkwell::execution_engine::JitFunction;
use inkwell::module::Linkage;
use inkwell::targets::{Target, InitializationConfig, TargetMachine, RelocMode, CodeModel, FileType};
use parse::FCParser;
use pest::{iterators::*, Parser};

use parse::Rule;

use crate::parse::{parse_expr, PRATT_PARSER};
mod parse;
mod compile;



use inkwell::builder::{Builder, self};
use inkwell::types::{BasicMetadataTypeEnum, BasicTypeEnum};
use inkwell::values::{BasicMetadataValueEnum, BasicValueEnum, FloatValue, FunctionValue, PointerValue, BasicValue};
use inkwell::{FloatPredicate, OptimizationLevel, AddressSpace};

use pest::iterators::{Pairs, Pair};
use itertools::Itertools;


fn main() {
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

    let optlev = OptimizationLevel::Aggressive;
    let relocmode = RelocMode::PIC;
    let codemodel = CodeModel::Medium;

    info!("optimization level: {optlev:?}");
    info!("relocation mode: {relocmode:?}");
    info!("code model: {codemodel:?}");

    let machine = target
        .create_target_machine(
            &triple,
            &cpu,
            &features,
            OptimizationLevel::Aggressive,
            RelocMode::PIC,
            CodeModel::Medium,//TODO: change to Small but idk if it will break things
        )
        .unwrap();
    info!("initialized target machined");

    let context = Context::create();
    let module = context.create_module("program");
    let builder = context.create_builder();
    let mut cg=compile::Codegen{
        context: &context,
        module: &module,
        builder: &builder,
        functions: &mut HashMap::new(),
        locals: &mut HashMap::new(),    
        // program_name: String::from("program_out")
    };
    cg.compile_program("./simple_program.tups");
    info!("compiled program");
    println!("{}",module.print_to_string().to_string());
    let dest = "program.o";
    machine.write_to_file(&module, FileType::Object, dest.as_ref()).unwrap();
    info!("written to file {dest}");
    println!("important: please link with math library (e.x: clang -lm program.o -o program)");

}
const PROGRAM_EX: &str = include_str!("program_ex.txt");
const EXPR_EX: &str = include_str!("expr_ex.txt");


impl std::fmt::Display for Rule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Rule::gep => write!(f,"gep"),
            Rule::not => write!(f,"not"),
            Rule::land => write!(f,"land"),
            Rule::lor => write!(f,"lor"),
            Rule::index => write!(f,"index"),
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
            Rule::pathident => write!(f,"pathident"),
            Rule::nil => write!(f,"nil"),
            Rule::call => write!(f,"call"),
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

