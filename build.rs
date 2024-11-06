use std::process::Command;

fn main() {
    println!("cargo::rustc-check-cfg=cfg(nightly)");
    
    let output = Command::new("rustc")
        .args(["--version"])
        .output()
        .expect("unable to get rustc version")
        .stdout;
    let version = String::from_utf8_lossy(&output);

    if version.contains("nightly") {
        println!("cargo:rustc-cfg=nightly")
    }
}
