use std::process::Command;

fn main() {
    let output = Command::new("rustc")
        .args(["--version"])
        .output()
        .expect("unable to get rustc version")
        .stdout;
    let version = String::from_utf8_lossy(&output);
    if version.contains("nightly") {
        println!("cargo:rustc-cfg=NIGHTLY")
    }
}
