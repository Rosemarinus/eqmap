// build.rs
fn main() {
    // 定义路径变量
    let npn_dir = "NPN";
    let abc_dir = format!("{}/abc", npn_dir);
    let wrapper_file = format!("{}/npn_wrapper.cpp", npn_dir);

    // -------------------------------------------------------
    // 1. 编译 C++ Wrapper
    // -------------------------------------------------------
    cc::Build::new()
        .cpp(true) // 启用 C++ 模式
        .file(&wrapper_file) // 你的 wrapper源文件
        .include(format!("{}/src", abc_dir)) // 包含 ABC 头文件路径
        // === 关键修复开始 ===
        // ABC 需要这个宏来识别 64位 环境 (Linux/macOS 64-bit 都通用这个)
        // 如果没有它，abc_global.h 就会报 unknown platform
        .define("LIN64", None)
        // 可选：禁用 Readline，防止后续链接时报 readline 相关的错
        .define("ABC_NO_USE_READLINE", None)
        // === 关键修复结束 ===
        // 屏蔽一些来自 ABC 头文件的陈旧警告 (sprintf deprecated 等)，让输出干净点
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
    println!("cargo:rustc-link-lib=dylib=c++"); // Mac 上通常是 libc++

    // ABC 依赖的其他系统库
    println!("cargo:rustc-link-lib=dylib=m");
    println!("cargo:rustc-link-lib=dylib=dl");
    println!("cargo:rustc-link-lib=dylib=pthread");

    // -------------------------------------------------------
    // 4. 重建触发条件
    // -------------------------------------------------------
    println!("cargo:rerun-if-changed={}", wrapper_file);
    println!("cargo:rerun-if-changed={}/libabc.a", abc_dir);
}
