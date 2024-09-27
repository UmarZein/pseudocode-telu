fn main(){
    println!("cargo:rustc-link-arg=-lffi");
    println!("cargo:rustc-link-lib=static=pthread");
}
