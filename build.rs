// build.rs
use std::path::Path;
use std::process::Command;

fn main() {
    // 定义路径变量
    let npn_dir = "NPN";
    let abc_dir = format!("{}/abc", npn_dir);
    let wrapper_file = format!("{}/npn_wrapper.cpp", npn_dir);
    let lib_path = format!("{}/libabc.a", abc_dir);

    // -------------------------------------------------------
    // 0. 自动检测并编译 ABC 静态库
    // -------------------------------------------------------
    if !Path::new(&lib_path).exists() {
        println!(
            "cargo:warning=ABC library not found. Compiling libabc.a automatically (this may take a while)..."
        );

        // 调用 make libabc.a -j4 ABC_USE_NO_READLINE=1
        let status = Command::new("make")
            .arg("libabc.a")
            .arg("-j4")
            // 显式告诉 ABC 的 Makefile 不要用 readline
            // 跳过 mainUtils.c 里的报错头文件, 让 GitHub Actions 能通过
            .arg("ABC_USE_NO_READLINE=1")
            .current_dir(&abc_dir)
            .status()
            .expect("Failed to execute make command");

        if !status.success() {
            panic!("Failed to build ABC library! Make sure you have 'make' and 'gcc' installed.");
        }
    }

    // -------------------------------------------------------
    // 1. 编译 C++ Wrapper
    // -------------------------------------------------------
    cc::Build::new()
        .cpp(true)
        .file(&wrapper_file)
        .include(format!("{}/src", abc_dir))
        .define("LIN64", None)
        // 确保 wrapper 编译时也没开启 readline
        .define("ABC_NO_USE_READLINE", None)
        .flag_if_supported("-Wno-deprecated-declarations")
        .flag_if_supported("-Wno-unused-parameter")
        .compile("npn_wrapper");

    // -------------------------------------------------------
    // 2. 链接 ABC 静态库 (libabc.a)
    // -------------------------------------------------------
    println!("cargo:rustc-link-search=native={}", abc_dir);
    println!("cargo:rustc-link-lib=static=abc");

    // -------------------------------------------------------
    // 3. 链接系统标准库
    // -------------------------------------------------------
    #[cfg(target_os = "linux")]
    println!("cargo:rustc-link-lib=dylib=stdc++");

    #[cfg(target_os = "macos")]
    println!("cargo:rustc-link-lib=dylib=c++");

    println!("cargo:rustc-link-lib=dylib=m");
    println!("cargo:rustc-link-lib=dylib=dl");
    println!("cargo:rustc-link-lib=dylib=pthread");

    // -------------------------------------------------------
    // 4. 重建触发条件
    // -------------------------------------------------------
    println!("cargo:rerun-if-changed={}", wrapper_file);
    println!("cargo:rerun-if-changed={}", lib_path);
}
