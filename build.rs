fn main(){
    if cfg!(unix) {
        // nothing to do...
    } else if cfg!(windows) {
        println!("cargo:rustc-link-arg=-lffi");
        println!("cargo:rustc-link-lib=static=pthread");
    } else {
        // i don't use mac
    };

}
