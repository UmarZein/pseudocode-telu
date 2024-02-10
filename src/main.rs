#![allow(warnings)]
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

impl std::fmt::Display for Rule {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Rule::ident => write!(f,"ident"),
            Rule::WHITESPACE => write!(f,"WHITESPACE"),
            Rule::uint => write!(f,"uint"),
            Rule::zint => write!(f,"zint"),
            Rule::int => write!(f,"int"),
            Rule::float => write!(f,"float"),
            Rule::bool => write!(f,"bool"),
            Rule::char => write!(f,"char"),
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
        }
    }
}
const DBGIND: &str = "  | ";
fn print_pair(p: Pair<Rule>, i: usize) {
    print!("{}{}",DBGIND.repeat(i), p.as_rule());
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


use inkwell::builder::{Builder, self};
use inkwell::types::{BasicMetadataTypeEnum, BasicTypeEnum};
use inkwell::values::{BasicMetadataValueEnum, BasicValueEnum, FloatValue, FunctionValue, PointerValue, BasicValue};
use inkwell::{FloatPredicate, OptimizationLevel, AddressSpace};

use pest::iterators::{Pairs, Pair};
use itertools::Itertools;



type FuncSign = unsafe extern "C" fn() -> i32;
//cargo r && clang++-17 exm.o -o exmar; ./exmar; echo $?
fn main() {
    Target::initialize_native(&InitializationConfig::default()).expect("Failed to initialize native target");
    println!("{}",TargetMachine::get_default_triple().as_str().to_str().unwrap());
    println!("cur dir = {}", std::env::current_dir().unwrap().display()    );

    // let context = Context::create();
    // let module = context.create_module("my_module");
    // let builder = context.create_builder();
    // //let execution_engine = module.create_jit_execution_engine(OptimizationLevel::Default).unwrap();


    // let int32 = context.i32_type();
    // let int8ptr = context.i8_type().ptr_type(AddressSpace::default());
    // let printf_types = int32.fn_type(&[int8ptr.into()], true);
    // let printf = module.add_function("printf", printf_types, Some(Linkage::External));
    // 

    // let func_out = context.i32_type();
    // let func_types = func_out.fn_type(&[], false);
    // let func = module.add_function("main", func_types, None);
    // let func_block = context.append_basic_block(func, "main");
    // builder.position_at_end(func_block);


    // let helloworld = builder.build_global_string_ptr("Hello, %lli!", "hey").unwrap();
    // println!("true={0}",true as u64);
    // println!("false={0}",false as u64);
    // let twoval: BasicValueEnum = context.i64_type().const_int({
    //     let x:i64 = 123123123456789;
    //     println!("{x:0b},{x}"); 
    //     println!("{0:0b} {0}",(x as u64)); 
    //     println!("{:0b}",(x as u64).wrapping_add(u64::MAX/2 + 1)); 
    //     (x as u64)
    // }, false).into();
    // let twovar = builder.build_alloca(context.i64_type(), "twotwo").unwrap();
    // builder.build_store(twovar, twoval).unwrap();    
    // let test123 = builder.build_load(context.i64_type(), twovar, "test123").unwrap();

    // let pcall = builder.build_direct_call(
    //     printf, 
    //     &[
    //         helloworld.as_pointer_value().into(), 
    //         test123.into()
    //     ], 
    //     "pcall1").unwrap()
    // .try_as_basic_value()
    // .left()
    // .unwrap();
    // 
    // if let BasicValueEnum::IntValue(x) = pcall{
    //     println!("pcall = intvalue {}",x.to_string());
    // } else {
    //     println!("error here!");
    // }

    // let x = builder.build_return(Some(&func_out.const_int(0,true)));

    //let f= unsafe{execution_engine.get_function("main").unwrap()}; 
    //unsafe{
    //    println!("{}",f.call())
    //}
    let triple = TargetMachine::get_default_triple();
    let cpu = TargetMachine::get_host_cpu_name().to_string();
    let features = TargetMachine::get_host_cpu_features().to_string();

    let target = Target::from_triple(&triple).unwrap();
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

    // println!("AYE");
    // println!("{}",module.print_to_string().to_string());
    // println!("HO");

    // machine.write_to_file(&module, FileType::Object, "exm.o".as_ref()).unwrap();
    // machine.write_to_file(&module, FileType::Assembly, "exm.asm".as_ref()).unwrap();
    // std::process::Command::new("clang-17")
    //     .args(["exm.o","-o","output_program"])
    //     .spawn().unwrap()
    //     .wait().unwrap();
    // std::process::Command::new("./output_program").spawn().unwrap().wait().unwrap();
    // std::process::Command::new("rm")
    //     .arg("./output_program").spawn().unwrap();

    // let p = PROGRAM_EX.clone();
    // let e = EXPR_EX.clone();
    // let prog = FCParser::parse(Rule::program, p.clone()).unwrap();
    // let exp = FCParser::parse(Rule::expr, e.clone()).unwrap();
    // print_pairs(prog,0);
    // print_pairs(exp.clone(),0);
    // let parsed = parse_expr(exp);
    // println!("{parsed:#?}")


    
    let context = Context::create();
    let module = context.create_module("program");
    let builder = context.create_builder();
    let mut cg=compile::Codegen{
        context: &context,
        module: &module,
        builder: &builder,
        functions: &mut HashMap::new(),
        stackmap: &mut HashMap::new(),    
        paramstack: &mut HashMap::new(),    
        // program_name: String::from("program_out")
    };
    cg.compile_program("./simple_program.tups");
    println!("{}",module.print_to_string().to_string());
    machine.write_to_file(&module, FileType::Object, "program.o".as_ref()).unwrap();
    println!("important: please link with math library (e.x: clang-17 -lm program.o -o program)");

}
const PROGRAM_EX: &str = include_str!("program_ex.txt");
const EXPR_EX: &str = include_str!("expr_ex.txt");
