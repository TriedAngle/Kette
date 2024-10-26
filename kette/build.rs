fn main() {
    let mut b = cc::Build::new();
    (if option_env!("CC") == Some("clang") {
        b.flag("-flto")
    } else {
        &mut b
    })
    .file("alloca.c")
    .opt_level(2)
    .compile("alloca");
}
