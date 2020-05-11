fn main() {
    let kremlin_home = std::env::var("KREMLIN_HOME")
    .expect("$KREMLIN_HOME is not defined");

    cc::Build::new()
        .warnings(true)
        .file("../src/out/Main.c")
        .file("../src/utils.c")
        .include("../src/out")
        .include(kremlin_home + "/include")
        .compile("libmqtt.a");
}