#include <cstdint>
#include <cstring>
#include <algorithm> // for std::min

// 引入 ABC 头文件
extern "C"
{
#include "misc/util/abc_global.h"
#include "bool/kit/kit.h"
}

// 定义用于与 Rust 交互的结构体
// 必须与 Rust 端定义的 #[repr(C)] 结构体内存布局一致
struct NpnTransformC
{
    uint64_t canon_prog;  // 规范化后的真值表
    int8_t perm[6];       // 输入置换数组
    uint8_t input_phase;  // 输入取反掩码 (位 0 对应输入 0)
    uint8_t output_phase; // 输出取反 (0 或 1)
};

extern "C"
{

    // 辅助函数：拆包 u64 到 unsigned[2]
    static void Unpack64(uint64_t in, unsigned *out)
    {
        out[0] = (unsigned)(in & 0xFFFFFFFF);
        out[1] = (unsigned)((in >> 32) & 0xFFFFFFFF);
    }

    // 辅助函数：打包 unsigned[2] 到 u64
    static uint64_t Pack64(unsigned *in)
    {
        return ((uint64_t)in[1] << 32) | in[0];
    }

    // 辅助函数：拉伸真值表
    static uint64_t StretchTruthTable(uint64_t tt, int nVars)
    {
        if (nVars >= 6)
            return tt;

        uint64_t mask = (1ULL << (1 << nVars)) - 1;
        uint64_t stretched = tt & mask;

        int current_bits = (1 << nVars);
        while (current_bits < 64)
        {
            stretched |= (stretched << current_bits);
            current_bits *= 2;
        }
        return stretched;
    }

    /**
     * 计算 NPN 变换配方
     * @param uTruth 原始真值表
     * @param nVars  原始变量数
     * @param result 输出参数，指向 Rust 分配的结构体
     */
    void Npn_GetTransform(uint64_t uTruth, int nVars, NpnTransformC *result)
    {
        // 1. 拉伸真值表
        uint64_t fullTruth = StretchTruthTable(uTruth, nVars);

        // 准备 ABC 缓冲区
        // unsigned pInOut[2];
        unsigned pAux[2];

        // 我们需要分别尝试 F 和 ~F，所以需要两套缓冲区来保存结果
        unsigned pInOutF[2];
        char pPermF[6];

        unsigned pInOutNotF[2];
        char pPermNotF[6];

        // -----------------------------------------------------
        // 路径 A: 计算 F 的 NP 规范形
        // -----------------------------------------------------
        Unpack64(fullTruth, pInOutF);
        // Kit_TruthSemiCanonicize 会修改 pInOutF 并填充 pPermF
        unsigned phaseF = Kit_TruthSemiCanonicize(pInOutF, pAux, 6, pPermF);
        uint64_t canonF = Pack64(pInOutF);

        // -----------------------------------------------------
        // 路径 B: 计算 ~F 的 NP 规范形 (处理输出取反)
        // -----------------------------------------------------
        Unpack64(~fullTruth, pInOutNotF);
        unsigned phaseNotF = Kit_TruthSemiCanonicize(pInOutNotF, pAux, 6, pPermNotF);
        uint64_t canonNotF = Pack64(pInOutNotF);

        // -----------------------------------------------------
        // 决策：选择字典序较小的那个作为最终 NPN 代表
        // -----------------------------------------------------
        if (canonF <= canonNotF)
        {
            // F 更小，说明不需要输出取反
            result->canon_prog = canonF;
            result->output_phase = 0;
            result->input_phase = (uint8_t)phaseF;
            for (int i = 0; i < 6; ++i)
                result->perm[i] = pPermF[i];
        }
        else
        {
            // ~F 更小，说明需要输出取反
            result->canon_prog = canonNotF;
            result->output_phase = 1;
            result->input_phase = (uint8_t)phaseNotF;
            for (int i = 0; i < 6; ++i)
                result->perm[i] = pPermNotF[i];
        }
    }
}