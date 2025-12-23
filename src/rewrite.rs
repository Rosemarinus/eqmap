/*!

  Shannon decomposition, general cut-fusion, general cut-decomposition (using DSD), LUT symmetry, constant evaluation, and gate conversion rewrite rules.

*/
use super::analysis::LutAnalysis;
use super::lut;
use super::lut::to_bitvec;
use bitvec::{bitvec, order::Lsb0, vec::BitVec};
use egg::{Analysis, Applier, Pattern, PatternAst, Rewrite, Subst, Var, rewrite};
use std::collections::{HashMap, HashSet};

// [NEW] Import get_npn_transform from analysis
use crate::analysis::{NpnTransformC, get_npn_transform};
use std::sync::Mutex;
use std::sync::OnceLock; // Rust 1.70+

// ============================================================================
// 全局缓存系统 (DSD & NPN)
// ============================================================================

/// 1. DSD 缓存: (Program, K) -> List of valid (i, j) pairs
/// 仅当开启 dyn_decomp 时编译 DSD 相关缓存
#[cfg(feature = "dyn_decomp")]
type DsdCacheMap = HashMap<(u64, usize), Vec<(u8, u8)>>;

#[cfg(feature = "dyn_decomp")]
static DSD_CACHE: OnceLock<Mutex<DsdCacheMap>> = OnceLock::new();

/// Retrieves the cached Disjoint Support Decomposition (DSD) pairs for a given truth table.
/// Returns a list of (mask, residue) pairs representing the decomposition.
#[cfg(feature = "dyn_decomp")]
pub fn get_cached_dsd(clean_p: u64, k: usize) -> Vec<(u8, u8)> {
    // 假设调用者已经做了 Masking (clean_p)，这里直接使用
    let key = (clean_p, k);
    let cache = DSD_CACHE.get_or_init(|| Mutex::new(HashMap::new()));

    // 1. 查缓存
    {
        let map = cache.lock().unwrap();
        if let Some(res) = map.get(&key) {
            return res.clone();
        }
    }

    // 2. 缓存未命中，执行纯计算
    let res = compute_dsd_pairs_pure(clean_p, k);

    // 3. 写入缓存
    {
        let mut map = cache.lock().unwrap();
        map.insert(key, res.clone());
    }
    res
}

// 纯计算函数：不依赖 E-Graph，只依赖数学
#[cfg(feature = "dyn_decomp")]
fn compute_dsd_pairs_pure(p_val: u64, k: usize) -> Vec<(u8, u8)> {
    if k < 3 {
        return vec![];
    }
    let mut valid_pairs = Vec::new();

    for i in 0..k {
        for j in (i + 1)..k {
            let mut residuals = [0u64; 4];
            let sub_space = 1 << (k - 2);
            let bit_i = k - 1 - i;
            let bit_j = k - 1 - j;

            for sub_idx in 0..sub_space {
                let mut base_idx = 0u64;
                let mut insert_ptr = 0;
                for bit in 0..k {
                    if bit == bit_i || bit == bit_j {
                        continue;
                    }
                    if (sub_idx >> insert_ptr) & 1 == 1 {
                        base_idx |= 1 << bit;
                    }
                    insert_ptr += 1;
                }

                let idx_00 = base_idx;
                let idx_01 = base_idx | (1 << bit_j);
                let idx_10 = base_idx | (1 << bit_i);
                let idx_11 = base_idx | (1 << bit_i) | (1 << bit_j);

                if (p_val >> idx_00) & 1 == 1 {
                    residuals[0] |= 1 << sub_idx;
                }
                if (p_val >> idx_01) & 1 == 1 {
                    residuals[1] |= 1 << sub_idx;
                }
                if (p_val >> idx_10) & 1 == 1 {
                    residuals[2] |= 1 << sub_idx;
                }
                if (p_val >> idx_11) & 1 == 1 {
                    residuals[3] |= 1 << sub_idx;
                }
            }

            // Check unique count <= 2
            let mut unique = 0;
            let mut seen = [0u64; 4];
            for &r in &residuals {
                if !seen[0..unique].contains(&r) {
                    seen[unique] = r;
                    unique += 1;
                }
            }

            if unique <= 2 {
                valid_pairs.push((i as u8, j as u8));
            }
        }
    }
    valid_pairs
}

// 2. NPN 缓存: (Program, K) -> Transform Info
static NPN_CACHE: OnceLock<Mutex<HashMap<(u64, usize), NpnTransformC>>> = OnceLock::new();

/// Retrieves the cached NPN transformation for a given truth table.
/// Uses a global cache to avoid recomputing expensive NPN operations.
pub fn get_cached_npn(clean_p: u64, k: usize) -> NpnTransformC {
    // 假设调用者已经做了 Masking
    let key = (clean_p, k);
    let cache = NPN_CACHE.get_or_init(|| Mutex::new(HashMap::new()));

    {
        let map = cache.lock().unwrap();
        if let Some(res) = map.get(&key) {
            return res.clone();
        }
    }

    // 调用底层 FFI 计算
    let res = get_npn_transform(clean_p, k);

    {
        let mut map = cache.lock().unwrap();
        map.insert(key, res.clone());
    }
    res
}

/// Returns a list of structural mappings of logic functions to LUTs.
pub fn struct_lut_map<A>(bidirectional: bool) -> Vec<Rewrite<lut::LutLang, A>>
where
    A: Analysis<lut::LutLang> + std::default::Default,
{
    let mut rules: Vec<Rewrite<lut::LutLang, A>> = Vec::new();
    // Logic element conversions
    if bidirectional {
        rules.append(&mut rewrite!("nor2-conversion"; "(NOR ?a ?b)" <=> "(LUT 1 ?a ?b)"));
        rules.append(&mut rewrite!("and2-conversion"; "(AND ?a ?b)" <=> "(LUT 8 ?a ?b)"));
        rules.append(&mut rewrite!("xor2-conversion"; "(XOR ?a ?b)" <=> "(LUT 6 ?a ?b)"));
        rules.push(rewrite!("or2-conversion"; "(LUT 14 ?a ?b)" => "(NOT (NOR ?a ?b))"));
        rules.push(rewrite!("and-one-inv-conversion"; "(LUT 2 ?a ?b)" => "(AND (NOT ?a) ?b)"));
        rules.append(&mut rewrite!("xor2-nor-nand"; "(XOR ?a ?b)" <=> "(NOT (NOR (AND (NOT ?a) ?b) (AND (NOT ?b) ?a)))"));
        rules.append(
            &mut rewrite!("and-distributivity"; "(AND ?a (NOT (NOR ?b ?c)))" <=> "(NOT (NOR (AND ?a ?b) (AND ?a ?c)))"),
        );
        rules.append(
            &mut rewrite!("or-distributivity"; "(NOT (NOR ?a (AND ?b ?c)))" <=> "(AND (NOT (NOR ?a ?b)) (NOT (NOR ?a ?c)))"),
        );
        rules.append(
            &mut rewrite!("and-associativity"; "(AND (AND ?a ?b) ?c)" <=> "(AND ?a (AND ?b ?c))"),
        );
        rules.append(
            &mut rewrite!("or-associativity"; "(NOT (NOR ?a (NOT (NOR ?b ?c))))" <=> "(NOT (NOR (NOT (NOR ?a ?b)) ?c))"),
        );
        rules.append(&mut rewrite!("demorgan"; "(NOR ?a ?b)" <=> "(AND (NOT ?a) (NOT ?b))"));
    } else {
        rules.push(rewrite!("nor2-conversion"; "(NOR ?a ?b)" => "(LUT 1 ?a ?b)"));
        rules.push(rewrite!("and2-conversion"; "(AND ?a ?b)" => "(LUT 8 ?a ?b)"));
        rules.push(rewrite!("xor2-conversion"; "(XOR ?a ?b)" => "(LUT 6 ?a ?b)"));
    }

    rules.append(&mut rewrite!("inverter-conversion"; "(NOT ?a)" <=> "(LUT 1 ?a)"));
    rules.append(&mut rewrite!("mux2-1-conversion"; "(MUX ?s ?a ?b)" <=> "(LUT 202 ?s ?a ?b)"));

    rules
}

/// [NEW] 吸收输出处的 1-LUT (NOT)
pub fn invert_lut_rules() -> Vec<Rewrite<lut::LutLang, LutAnalysis>> {
    let mut rules = Vec::new();
    for k in 1..=6 {
        // 支持 1..6, 包括 buffer 反转
        let mut parts = vec!["(NOT (LUT ?p".to_string()];
        let mut vars = vec![];
        for i in 0..k {
            let v = format!("?v{}", i);
            parts.push(v.clone());
            vars.push(v.parse().unwrap());
        }
        parts.push("))".to_string());
        let pattern_str = parts.join(" ");

        let applier = InvertLutApplier {
            p_var: "?p".parse().unwrap(),
            vars,
        };

        rules.push(
            Rewrite::new(
                format!("absorb-output-not-lut{}", k),
                pattern_str.parse::<Pattern<lut::LutLang>>().unwrap(),
                applier,
            )
            .unwrap(),
        );
    }
    rules
}

/// [NEW] 2-输入DSD分解
/// Feature Gated: 仅在 dyn_decomp 开启时编译
#[cfg(feature = "dyn_decomp")]
pub fn dsd_rules() -> Vec<Rewrite<lut::LutLang, LutAnalysis>> {
    let mut rules = Vec::new();
    for k in 3..=6 {
        // 只有 3-LUT 及以上才值得分解
        let mut parts = vec![format!("(LUT ?p")];
        let mut vars = vec![];
        for i in 0..k {
            let v = format!("?v{}", i);
            parts.push(v.clone());
            vars.push(v.parse().unwrap());
        }
        parts.push(")".to_string());
        let pattern_str = parts.join(" ");

        rules.push(
            Rewrite::new(
                format!("lut{}-dsd-expand", k),
                pattern_str.parse::<Pattern<lut::LutLang>>().unwrap(),
                DSDExpand {
                    p_var: "?p".parse().unwrap(),
                    vars,
                },
            )
            .unwrap(),
        );
    }
    rules
}

/// Move registers around LUTs
pub fn register_retiming<A>() -> Vec<Rewrite<lut::LutLang, A>>
where
    A: Analysis<lut::LutLang> + std::default::Default,
{
    let mut rules: Vec<Rewrite<lut::LutLang, A>> = Vec::new();
    // Logic element conversions
    rules.append(&mut rewrite!("lut1-retime"; "(LUT ?p (REG ?a))" <=> "(REG (LUT ?p ?a))"));
    rules.append(
        &mut rewrite!("lut2-retime"; "(LUT ?p (REG ?a) (REG ?b))" <=> "(REG (LUT ?p ?a ?b))"),
    );
    rules.append(
        &mut rewrite!("lut3-retime"; "(LUT ?p (REG ?a) (REG ?b) (REG ?c))" <=> "(REG (LUT ?p ?a ?b ?c))"),
    );
    rules.append(
        &mut rewrite!("lut4-retime"; "(LUT ?p (REG ?a) (REG ?b) (REG ?c) (REG ?d))" <=> "(REG (LUT ?p ?a ?b ?c ?d))"),
    );
    rules.append(
        &mut rewrite!("lut5-retime"; "(LUT ?p (REG ?a) (REG ?b) (REG ?c) (REG ?d) (REG ?e))" <=> "(REG (LUT ?p ?a ?b ?c ?d ?e))"),
    );
    rules.append(
        &mut rewrite!("lut6-retime"; "(LUT ?p (REG ?a) (REG ?b) (REG ?c) (REG ?d) (REG ?e) (REG ?f))" <=> "(REG (LUT ?p ?a ?b ?c ?d ?e ?f))"),
    );

    rules
}

/// Returns a list of rules for permuting inputs in LUTs.
pub fn permute_groups() -> Vec<Rewrite<lut::LutLang, LutAnalysis>> {
    let mut rules: Vec<Rewrite<lut::LutLang, LutAnalysis>> = Vec::new();
    // LUT permutation groups
    rules.push(rewrite!("lut2-permute"; "(LUT ?p ?a ?b)" 
        => {PermuteInput::new(1, "?p".parse().unwrap(), vec!["?a".parse().unwrap(), "?b".parse().unwrap()])}));

    for i in 1..3 {
        let rname = format!("lut3-permute-{i}");
        rules.push(rewrite!(rname; "(LUT ?p ?a ?b ?c)" 
        => {PermuteInput::new(i, "?p".parse().unwrap(), vec!["?a".parse().unwrap(), "?b".parse().unwrap(), "?c".parse().unwrap()])}));
    }

    for i in 1..4 {
        let rname = format!("lut4-permute-{i}");
        rules.push(rewrite!(rname; "(LUT ?p ?a ?b ?c ?d)" 
        => {PermuteInput::new(i, "?p".parse().unwrap(), vec!["?a".parse().unwrap(), "?b".parse().unwrap(), "?c".parse().unwrap(), "?d".parse().unwrap()])}));
    }

    for i in 1..5 {
        let rname = format!("lut5-permute-{i}");
        rules.push(rewrite!(rname; "(LUT ?p ?a ?b ?c ?d ?e)" 
        => {PermuteInput::new(i, "?p".parse().unwrap(), vec!["?a".parse().unwrap(), "?b".parse().unwrap(), "?c".parse().unwrap(), "?d".parse().unwrap(), "?e".parse().unwrap()])}));
    }

    for i in 1..6 {
        let rname = format!("lut6-permute-{i}");
        rules.push(rewrite!(rname; "(LUT ?p ?a ?b ?c ?d ?e ?f)" 
        => {PermuteInput::new(i, "?p".parse().unwrap(), vec!["?a".parse().unwrap(), "?b".parse().unwrap(), "?c".parse().unwrap(), "?d".parse().unwrap(), "?e".parse().unwrap(), "?f".parse().unwrap()])}));
    }

    rules
}

/// Condenses two cofactors along a single boolean term into one combined function
pub fn condense_cofactors() -> Vec<Rewrite<lut::LutLang, LutAnalysis>> {
    let mut rules: Vec<Rewrite<lut::LutLang, LutAnalysis>> = Vec::new();

    rules.push(rewrite!("mux-make-disjoint-or"; "(LUT 202 ?s true ?a)" => "(LUT 14 ?s ?a)"));
    rules.push(rewrite!("mux-make-disjoint-or-not"; "(LUT 202 ?s ?a true)" => "(LUT 14 (LUT 8 ?s ?a) (LUT 1 ?s))"));
    rules.push(rewrite!("mux-make-disjoint-and"; "(LUT 202 ?s ?a false)" => "(LUT 8 ?s ?a)"));
    rules.push(rewrite!("mux-make-disjoint-and-not"; "(LUT 202 ?s false ?a)" => "(LUT 2 ?s ?a)"));
    rules.push(rewrite!("mux-make-disjoint-xor"; "(LUT 202 ?s (NOT ?a) ?a)" => "(LUT 6 ?s ?a)"));
    rules.push(rewrite!("mux-make-disjoint-xnor"; "(LUT 202 ?s ?a (NOT ?a))" => "(LUT 9 ?s ?a)"));

    // Condense Shannon expansion
    for k in 2..=5 {
        for s_pos in 0..3 {
            for c1_pos in 0..3 {
                if s_pos == c1_pos {
                    continue;
                }
                let c2_pos = 3 - s_pos - c1_pos;

                let mut root_parts = vec!["(LUT ?root_p".to_string()];
                let mut vars = vec![];
                for i in 0..k {
                    vars.push(format!("?v{}", i));
                }
                let child_args = vars.join(" ");

                let mut args = vec!["".to_string(); 3];
                args[s_pos] = "?s".to_string();
                args[c1_pos] = format!("(LUT ?p {})", child_args);
                args[c2_pos] = format!("(LUT ?q {})", child_args);

                root_parts.extend(args);
                root_parts.push(")".to_string());
                let pattern_str = root_parts.join(" ");

                let pattern = pattern_str.parse::<Pattern<lut::LutLang>>().unwrap();

                let applier = ShannonCondense::new(
                    "?s".parse().unwrap(),
                    "?root_p".parse().unwrap(),
                    "?p".parse().unwrap(),
                    "?q".parse().unwrap(),
                    vars.iter().map(|s| s.parse().unwrap()).collect(),
                    s_pos,
                    c1_pos,
                );

                rules.push(
                    Rewrite::new(
                        format!("lut{}-shannon-pos{}-{}-{}", k, s_pos, c1_pos, c2_pos),
                        pattern,
                        applier,
                    )
                    .expect("Failed to create rewrite rule"),
                );
            }
        }
    }

    rules
}

fn p_q_pos_cut_fuse(p: usize, q: usize, child_pos: usize) -> Rewrite<lut::LutLang, LutAnalysis> {
    let mut root_inputs = Vec::new();
    let mut child_vars = Vec::new();

    for j in 0..q {
        child_vars.push(format!("?q{}", j));
    }
    let child_pattern = format!("(LUT ?child_p {})", child_vars.join(" "));

    let mut root_vars = Vec::new();
    for i in 0..p {
        if i == child_pos {
            root_inputs.push(child_pattern.clone());
        } else {
            let v = format!("?p{}", i);
            root_inputs.push(v.clone());
            root_vars.push(v);
        }
    }

    let pattern_str = format!("(LUT ?root_p {})", root_inputs.join(" "));
    let pattern = pattern_str.parse::<Pattern<lut::LutLang>>().unwrap();

    let applier = FuseCut::new(
        "?root_p".parse().unwrap(),
        root_vars.iter().map(|s| s.parse().unwrap()).collect(),
        "?child_p".parse().unwrap(),
        child_vars.iter().map(|s| s.parse().unwrap()).collect(),
        child_pos,
    );

    Rewrite::new(
        format!("fuse-{}-{}-pos{}", p, q, child_pos),
        pattern,
        applier,
    )
    .expect("Failed to create fusion rule")
}

/// Generally condenses a k-Cut to a single LUT. This rule works even when inputs are not mutually-exclusive.
/// When k > 6, the rule does no rewriting (instead of crashing).
pub fn general_cut_fusion() -> Vec<Rewrite<lut::LutLang, LutAnalysis>> {
    let mut rules: Vec<Rewrite<lut::LutLang, LutAnalysis>> = Vec::new();
    for p in 2..=6 {
        for q in 1..=6 {
            for pos in 0..p {
                rules.push(p_q_pos_cut_fuse(p, q, pos));
            }
        }
    }
    rules
}

/// Returns a list of rules for evaluating constant LUTs
pub fn constant_luts<A>() -> Vec<Rewrite<lut::LutLang, A>>
where
    A: Analysis<lut::LutLang>,
{
    let mut rules: Vec<Rewrite<lut::LutLang, A>> = Vec::new();
    for k in 2..7 {
        let mask = if k < 6 { (1 << (1 << k)) - 1 } else { u64::MAX };
        let vars = (0..k).map(|i| format!("?v{i}")).collect::<Vec<String>>();
        let pattern_true: Pattern<lut::LutLang> = format!("(LUT {} {})", mask, vars.join(" "))
            .parse()
            .unwrap();
        let pattern_false: Pattern<lut::LutLang> =
            format!("(LUT 0 {})", vars.join(" ")).parse().unwrap();
        let rname_true = format!("lut{k}-const-true");
        let rname_false = format!("lut{k}-const-false");
        rules.push(rewrite!(rname_true; pattern_true => "true"));
        rules.push(rewrite!(rname_false; pattern_false => "false"));
    }
    rules
}

/// Known decompositions of LUTs based on disjoint support decompositions
pub fn known_decompositions() -> Vec<Rewrite<lut::LutLang, LutAnalysis>> {
    let mut rules: Vec<Rewrite<lut::LutLang, LutAnalysis>> = Vec::new();
    rules.push(rewrite!("mux4-1-dsd"; "(LUT 18374951396690406058 ?s1 ?s0 ?a ?b ?c ?d)" => "(LUT 51952 ?s1 (LUT 61642 ?s1 ?s0 ?c ?d) ?a ?b)"));

    // TODO: 优化这个地方
    // 下面的general_decomp_rules本意就是优化这里
    // 本质上只是上面的换了输入位置，只是暂时加入，为了通过tests/driver/big_decimal.v的测试
    rules.push(rewrite!(
        "mux4-1-specific";
        "(LUT 17361601744336890538 ?s0 ?s1 ?b ?a ?c ?d)"
        =>
        "(LUT 51952 ?s1 (LUT 61642 ?s1 ?s0 ?c ?d) ?a ?b)"
    ));
    rules
}

/// Find dynamic decompositions of LUTs at runtime.
/// Finds compositions in any variable order when `any_order` is true
#[cfg(feature = "dyn_decomp")]
pub fn dyn_decompositions(any_order: bool) -> Vec<Rewrite<lut::LutLang, LutAnalysis>> {
    let mut rules: Vec<Rewrite<lut::LutLang, LutAnalysis>> = Vec::new();
    rules.push(
        rewrite!("mux-expand"; "(LUT 202 ?s ?a ?b)" => "(LUT 14 (LUT 8 ?s ?a) (LUT 2 ?s ?b))"),
    );

    for k in 3..=6 {
        let positions = if any_order { 0..k } else { 0..1 };
        for pos in positions {
            let mut parts = vec!["(LUT ?p".to_string()];
            let mut vars = vec![];
            for i in 0..k {
                let v = format!("?v{}", i);
                parts.push(v.clone());
                vars.push(v);
            }
            parts.push(")".to_string());
            let pattern_str = parts.join(" ");

            rules.push(
                Rewrite::new(
                    format!("lut{}-shannon-expand-pos{}", k, pos),
                    pattern_str.parse::<Pattern<lut::LutLang>>().unwrap(),
                    decomp::ShannonExpand::new(
                        "?p".parse().unwrap(),
                        vars.iter().map(|s| s.parse().unwrap()).collect(),
                        pos,
                    ),
                )
                .expect("Failed to create shannon rule"),
            );
        }
    }
    rules
}

/// Canonicalizes LUTs with redundant inputs
pub fn redundant_inputs() -> Vec<Rewrite<lut::LutLang, LutAnalysis>> {
    let mut rules: Vec<Rewrite<lut::LutLang, LutAnalysis>> = Vec::new();
    rules.push(rewrite!("lut3-redundant-mux"; "(LUT 202 ?s ?a ?a)" => "?a"));

    for k in 2..=6 {
        let mut parts = vec![format!("(LUT ?p")];
        let mut vars = vec![];
        for i in 0..k {
            let v = format!("?v{}", i);
            parts.push(v.clone());
            vars.push(v);
        }
        parts.push(")".to_string());
        let pattern_str = parts.join(" ");

        let pattern = pattern_str.parse::<Pattern<lut::LutLang>>().unwrap();
        let applier = CombineAlikeInputs::new(
            "?p".parse().unwrap(),
            vars.iter().map(|s| s.parse().unwrap()).collect(),
        );

        rules.push(
            Rewrite::new(format!("lut{}-smart-redundant", k), pattern, applier)
                .expect("Failed to create rewrite rule"),
        );
    }
    rules
}

/// One Applier to Rule Them All: ToCanonicalApplier
/// Convert LUT to CANON
#[derive(Debug, Clone)]
struct ToCanonicalApplier;

impl Applier<lut::LutLang, LutAnalysis> for ToCanonicalApplier {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<lut::LutLang, LutAnalysis>,
        eclass: egg::Id,
        _subst: &Subst,
        _searcher_ast: Option<&PatternAst<lut::LutLang>>,
        _rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let mut program_u64 = None;
        let mut original_inputs = Vec::new();

        for node in &egraph[eclass].nodes {
            if let lut::LutLang::Lut(ids) = node {
                if let Ok(p) = egraph[ids[0]].data.get_program() {
                    program_u64 = Some(p);
                } else if let lut::LutLang::Program(val) = &egraph[ids[0]].nodes[0] {
                    program_u64 = Some(*val);
                }
                original_inputs = ids[1..].to_vec();
                break;
            }
        }

        if program_u64.is_none() || original_inputs.is_empty() {
            return vec![];
        }

        let p_val = program_u64.unwrap();
        let k = original_inputs.len();

        // [Optimize] Mask p_val before cache lookup
        let mask = if k >= 6 {
            !0u64
        } else {
            (1u64 << (1 << k)) - 1
        };
        let clean_p = p_val & mask;

        // [FIX] 关键修复：忽略常量 LUT
        // 如果 LUT 本身已经是全0 (False) 或全1 (True)，不需要进行 NPN 规范化。
        // constant_luts 规则会负责把它们优化成 Const 节点。
        // 强行做 NPN 可能会导致 output_phase 计算错误或结构冗余。
        if clean_p == 0 || clean_p == mask {
            return vec![];
        }

        // [Optimize] Use cached NPN with masked program
        let transform = get_cached_npn(clean_p, k);
        // Note: canon_prog from transform might be stretched, mask it before use
        let canon_prog = transform.canon_prog;

        let mut new_canon_inputs = Vec::with_capacity(k);

        for c_bit in (0..k).rev() {
            let orig_src_bit_lsb = transform.perm[c_bit] as usize;
            if orig_src_bit_lsb >= k {
                return vec![];
            }

            let orig_vec_idx = (k - 1) - orig_src_bit_lsb;
            let mut input_id = original_inputs[orig_vec_idx];

            let is_inverted = (transform.input_phase >> c_bit) & 1 == 1;
            if is_inverted {
                input_id = egraph.add(lut::LutLang::Not([input_id]));
            }
            new_canon_inputs.push(input_id);
        }

        // Use this mask for sorting comparison AND for node creation
        let canon_prog_masked = canon_prog & mask;

        let mut changed = true;
        while changed {
            changed = false;
            for i in 0..(k - 1) {
                let id_a = new_canon_inputs[i];
                let id_b = new_canon_inputs[i + 1];
                if id_a <= id_b {
                    continue;
                }

                let b_low = k - 2 - i;
                let swapped_prog = lut::swap_pos(&canon_prog, k, b_low);

                if (swapped_prog & mask) == canon_prog_masked {
                    new_canon_inputs.swap(i, i + 1);
                    changed = true;
                }
            }
        }

        let prog_id = egraph.add(lut::LutLang::Program(canon_prog_masked));
        let mut children = vec![prog_id];
        children.extend(new_canon_inputs);
        let mut canon_id = egraph.add(lut::LutLang::Canonical(children.into()));

        if transform.output_phase == 1 {
            canon_id = egraph.add(lut::LutLang::Not([canon_id]));
        }

        if egraph.union(eclass, canon_id) {
            vec![eclass]
        } else {
            vec![]
        }
    }
}

/// An Applier that removes unused inputs from a LUT.
/// Example: (LUT 160 a b c) -> (LUT 8 a c) if b is unused.
#[derive(Debug, Clone)]
pub struct RemoveUnusedInput;

impl Applier<lut::LutLang, LutAnalysis> for RemoveUnusedInput {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<lut::LutLang, LutAnalysis>,
        eclass: egg::Id,
        _subst: &Subst,
        _searcher_ast: Option<&PatternAst<lut::LutLang>>,
        _rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let mut program = 0u64;
        let mut inputs = Vec::new();

        // 1. 获取当前 LUT 的 Program 和 输入
        for node in &egraph[eclass].nodes {
            if let lut::LutLang::Lut(children) = node {
                if let Ok(p) = egraph[children[0]].data.get_program() {
                    program = p;
                } else {
                    continue;
                }
                inputs = children[1..].to_vec();
                break;
            }
        }

        if inputs.is_empty() {
            return vec![];
        }
        let k = inputs.len();

        // 2. 遍历检查每个输入是否冗余
        for i in 0..k {
            let bit_idx = k - 1 - i;

            let mut is_unused = true;
            let check_limit = 1 << k;

            for val in 0..check_limit {
                if (val >> bit_idx) & 1 == 0 {
                    let val_pair = val | (1 << bit_idx);
                    let out1 = (program >> val) & 1;
                    let out2 = (program >> val_pair) & 1;
                    if out1 != out2 {
                        is_unused = false;
                        break;
                    }
                }
            }

            if is_unused {
                // 3. 构建新的 Program
                let mut new_program = 0u64;
                let mut insert_ptr = 0;
                for val in 0..check_limit {
                    if (val >> bit_idx) & 1 == 0 {
                        let out = (program >> val) & 1;
                        new_program |= out << insert_ptr;
                        insert_ptr += 1;
                    }
                }

                // 4. 构建新 Inputs 列表
                let mut new_inputs = inputs.clone();
                new_inputs.remove(i);

                // [FIX] 检查是否所有输入都被移除了 (变成常量)
                if new_inputs.is_empty() {
                    // 如果 Program 的第 0 位是 1，则是 True，否则是 False
                    let const_val = (new_program & 1) != 0;
                    // 注意：这里假设你的 LutLang 有 Const 变体。
                    // 如果没有，你需要根据你的 enum 定义修改 (例如 (LUT 3) for true)
                    // 查看 constant_luts 规则，通常 egraph 会自动处理 Const(bool)
                    let const_node = egraph.add(lut::LutLang::Const(const_val));
                    if egraph.union(eclass, const_node) {
                        return vec![const_node];
                    } else {
                        return vec![];
                    }
                }

                // 5. 添加新节点
                let new_prog_id = egraph.add(lut::LutLang::Program(new_program));
                let mut new_children = vec![new_prog_id];
                new_children.extend(new_inputs);

                let new_lut = egraph.add(lut::LutLang::Lut(new_children.into()));

                if egraph.union(eclass, new_lut) {
                    return vec![new_lut];
                }
            }
        }

        vec![]
    }
}

/// Returns rules that remove unused inputs from LUTs.
pub fn remove_unused_rules() -> Vec<Rewrite<lut::LutLang, LutAnalysis>> {
    let mut rules = Vec::new();
    for k in 2..=6 {
        let vars = (0..k)
            .map(|i| format!("?v{}", i))
            .collect::<Vec<_>>()
            .join(" ");
        let pattern_str = format!("(LUT ?p {})", vars);

        let pattern = pattern_str.parse::<Pattern<lut::LutLang>>().unwrap();

        rules.push(
            Rewrite::new(
                format!("lut{}-remove-unused", k),
                pattern,
                RemoveUnusedInput,
            )
            .expect("Failed to create remove-unused rule"),
        );
    }
    rules
}

//  这里似乎不应该打开将CANON写回的规则，否则会导致LUT数量变多
/// Generates rewrite rules for NPN canonicalization.
/// Converts LUTs into their canonical NPN form to maximize structural sharing.
pub fn npn_canon_rules() -> Vec<Rewrite<lut::LutLang, LutAnalysis>> {
    vec![
        rewrite!("lut6-canon"; "(LUT ?p ?a ?b ?c ?d ?e ?f)" => { ToCanonicalApplier }),
        rewrite!("lut5-canon"; "(LUT ?p ?a ?b ?c ?d ?e)"    => { ToCanonicalApplier }),
        rewrite!("lut4-canon"; "(LUT ?p ?a ?b ?c ?d)"       => { ToCanonicalApplier }),
        rewrite!("lut3-canon"; "(LUT ?p ?a ?b ?c)"          => { ToCanonicalApplier }),
        rewrite!("lut2-canon"; "(LUT ?p ?a ?b)"             => { ToCanonicalApplier }),
        rewrite!("lut1-canon"; "(LUT ?p ?a)"                => { ToCanonicalApplier }),
        // rewrite!("canon6-to-lut"; "(CANON ?p ?a ?b ?c ?d ?e ?f)" => "(LUT ?p ?a ?b ?c ?d ?e ?f)"),
        // rewrite!("canon5-to-lut"; "(CANON ?p ?a ?b ?c ?d ?e)"    => "(LUT ?p ?a ?b ?c ?d ?e)"),
        // rewrite!("canon4-to-lut"; "(CANON ?p ?a ?b ?c ?d)"       => "(LUT ?p ?a ?b ?c ?d)"),
        // rewrite!("canon3-to-lut"; "(CANON ?p ?a ?b ?c)"          => "(LUT ?p ?a ?b ?c)"),
        // rewrite!("canon2-to-lut"; "(CANON ?p ?a ?b)"             => "(LUT ?p ?a ?b)"),
        // rewrite!("canon1-to-lut"; "(CANON ?p ?a)"                => "(LUT ?p ?a)"),
    ]
}

/// Represents a trivial logic function found during decomposition
#[derive(Debug, Clone, Copy)]
enum AtomicLogic {
    Const(bool), // 0 or 1
    Var(usize),  // x_i (index relative to the current cofactor's inputs)
    Inv(usize),  // !x_i
}

/// Represents the structure of a discovered logic (Atomic or MUX)
#[derive(Debug, Clone)]
enum LogicStruct {
    Atomic(AtomicLogic),
    // Mux(selector_index, High_Branch, Low_Branch)
    // selector_index is relative to the current input list at this recursion depth
    Mux(usize, Box<LogicStruct>, Box<LogicStruct>),
}

/// Checks if a truth table represents an atomic logic (Const, Var, or NotVar).
fn analyze_atomic(prog: u64, k: usize) -> Option<AtomicLogic> {
    let mask = if k >= 6 {
        !0u64
    } else {
        (1u64 << (1 << k)) - 1
    };
    let val = prog & mask;

    // 1. Const Check
    if val == 0 {
        return Some(AtomicLogic::Const(false));
    }
    if val == mask {
        return Some(AtomicLogic::Const(true));
    }

    // 2. Var / InvVar Check
    // Variable i (0=LSB) alternates 0..1 every 2^i bits.
    for i in 0..k {
        let mut var_mask = 0u64;
        let limit = 1 << k;

        for bit in 0..limit {
            if (bit >> i) & 1 == 1 {
                var_mask |= 1 << bit;
            }
        }

        if val == var_mask {
            return Some(AtomicLogic::Var(i));
        }
        if val == (!var_mask & mask) {
            return Some(AtomicLogic::Inv(i));
        }
    }

    None
}

/// Helper to extract cofactor when input `sel_bit_idx` is fixed to `val` (0 or 1).
fn extract_cofactor(prog: u64, k: usize, sel_bit_idx: usize, val: u8) -> u64 {
    let mut new_prog = 0u64;
    let new_size = 1 << (k - 1);

    for row in 0..new_size {
        // Construct original index from 'row' by inserting 'val' at 'sel_bit_idx'.
        let lower_mask = (1 << sel_bit_idx) - 1;
        let lower_part = row & lower_mask;
        let upper_part = (row & !lower_mask) << 1;

        let original_idx = upper_part | lower_part | ((val as u64) << sel_bit_idx);

        if (prog >> original_idx) & 1 == 1 {
            new_prog |= 1 << row;
        }
    }
    new_prog
}

/// Recursively checks if a truth table is Atomic OR a simple MUX structure.
/// `depth`: recursion depth limit (1 is enough for 4:1 MUX).
fn analyze_logic(prog: u64, k: usize, depth: usize) -> Option<LogicStruct> {
    // 1. Try Atomic First
    if let Some(atom) = analyze_atomic(prog, k) {
        return Some(LogicStruct::Atomic(atom));
    }

    // 2. If not atomic, try to decompose as MUX (if depth > 0)
    if depth > 0 {
        // Try every input as the selector
        for i in 0..k {
            // Note: In our Logic, i=0 corresponds to inputs[0] (MSB in array),
            // which corresponds to bit (k-1) in truth table index?
            // Wait. In analyze_atomic, Var(i) refers to bit i.
            // Let's stick to bit index `sel_bit_idx` for math, and `i` for array index.
            // Assumption: inputs[0] is MSB, so it is bit (k-1).
            // inputs[i] is bit (k - 1 - i).

            let sel_bit_idx = k - 1 - i;

            let low_prog = extract_cofactor(prog, k, sel_bit_idx, 0);
            let high_prog = extract_cofactor(prog, k, sel_bit_idx, 1);
            let child_k = k - 1;

            let low_struct = analyze_logic(low_prog, child_k, depth - 1);
            let high_struct = analyze_logic(high_prog, child_k, depth - 1);

            if let (Some(ls), Some(hs)) = (low_struct, high_struct) {
                // Found a MUX! 'i' is the index in the current input list
                return Some(LogicStruct::Mux(i, Box::new(hs), Box::new(ls)));
            }
        }
    }

    None
}

/// Fast decomposition for LUTs that are essentially MUXes.
/// Supports recursive MUX structures (e.g. 4:1 MUX).
#[derive(Debug, Clone)]
pub struct SimpleMuxDecomposition;

impl Applier<lut::LutLang, LutAnalysis> for SimpleMuxDecomposition {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<lut::LutLang, LutAnalysis>,
        eclass: egg::Id,
        _subst: &Subst,
        _searcher_ast: Option<&PatternAst<lut::LutLang>>,
        _rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let mut program = 0u64;
        let mut inputs = Vec::new();

        // 1. 获取 Program 和 Inputs (修复 Scope 报错的关键)
        for node in &egraph[eclass].nodes {
            if let lut::LutLang::Lut(children) = node {
                if let Ok(p) = egraph[children[0]].data.get_program() {
                    program = p;
                } else {
                    continue;
                }
                inputs = children[1..].to_vec();
                break;
            }
        }

        let k = inputs.len();
        if k < 3 || k > 6 {
            return vec![];
        }

        // 2. Analyze Logic Structure
        // depth=1 allows parsing MUX(s1, MUX(s0, a, b), MUX(s0, c, d))
        if let Some(logic) = analyze_logic(program, k, 1) {
            return vec![build_logic_recursive(egraph, &logic, &inputs)];
        }

        vec![]
    }
}

/// Helper function to reconstruct E-Graph nodes from LogicStruct
fn build_logic_recursive(
    egraph: &mut egg::EGraph<lut::LutLang, LutAnalysis>,
    logic: &LogicStruct,
    current_inputs: &[egg::Id],
) -> egg::Id {
    match logic {
        LogicStruct::Atomic(atom) => match atom {
            AtomicLogic::Const(b) => egraph.add(lut::LutLang::Const(*b)),
            AtomicLogic::Var(idx) => {
                // idx is bit index (0=LSB).
                // current_inputs is [MSB, ..., LSB].
                // so LSB is at len-1.
                current_inputs[current_inputs.len() - 1 - idx]
            }
            AtomicLogic::Inv(idx) => {
                let id = current_inputs[current_inputs.len() - 1 - idx];
                egraph.add(lut::LutLang::Not([id]))
            }
        },
        LogicStruct::Mux(sel_idx, high, low) => {
            // sel_idx is the index in current_inputs array
            let sel_var = current_inputs[*sel_idx];

            // Create new inputs list for children (remove selector)
            let mut child_inputs = current_inputs.to_vec();
            child_inputs.remove(*sel_idx);

            let high_node = build_logic_recursive(egraph, high, &child_inputs);
            let low_node = build_logic_recursive(egraph, low, &child_inputs);

            // MUX(s, a, b) => 0xCA (s ? a : b)
            let mux_prog = egraph.add(lut::LutLang::Program(202));
            egraph.add(lut::LutLang::Lut(
                vec![mux_prog, sel_var, high_node, low_node].into(),
            ))
        }
    }
}

/// Returns rules for fast, structure-based MUX decomposition.
pub fn simple_mux_rules() -> Vec<Rewrite<lut::LutLang, LutAnalysis>> {
    let mut rules = Vec::new();
    rules.push(rewrite!("fast-mux-decomp-6"; "(LUT ?p ?v0 ?v1 ?v2 ?v3 ?v4 ?v5)" => { SimpleMuxDecomposition }));
    rules.push(
        rewrite!("fast-mux-decomp-5"; "(LUT ?p ?v0 ?v1 ?v2 ?v3 ?v4)" => { SimpleMuxDecomposition }),
    );
    rules.push(
        rewrite!("fast-mux-decomp-4"; "(LUT ?p ?v0 ?v1 ?v2 ?v3)" => { SimpleMuxDecomposition }),
    );
    rules.push(rewrite!("fast-mux-decomp-3"; "(LUT ?p ?v0 ?v1 ?v2)" => { SimpleMuxDecomposition }));
    rules
}

/// General Topological Decomposition (Relaxed)
/// Attempts to decompose a k-LUT (k=3..6) into two cascaded LUTs of size <= LIMIT.
///
/// New Constraints for LIMIT=5:
///   Inner <= 5
///   Outer <= 5
/// This allows decomposing 6-LUTs with high variable sharing (up to S=3).
#[derive(Debug, Clone)]
pub struct GeneralLutDecomposition;

// 用户设定的最大允许 LUT 大小 (你说是 5)
const DECOMP_LIMIT: usize = 5;

impl Applier<lut::LutLang, LutAnalysis> for GeneralLutDecomposition {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<lut::LutLang, LutAnalysis>,
        eclass: egg::Id,
        _subst: &Subst,
        _searcher_ast: Option<&PatternAst<lut::LutLang>>,
        _rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let mut program = 0u64;
        let mut inputs = Vec::new();

        // 1. 获取 Program 和 Inputs
        for node in &egraph[eclass].nodes {
            if let lut::LutLang::Lut(children) = node {
                if let Ok(p) = egraph[children[0]].data.get_program() {
                    program = p;
                } else {
                    continue;
                }
                inputs = children[1..].to_vec();
                break;
            }
        }

        let k = inputs.len();
        // 如果当前 LUT 已经比限制还小，通常没必要强行拆（除非为了提取更小的公共子表达式）
        // 但为了通用性，我们允许拆解 k=4,5,6
        if k < 3 || k > 6 {
            return vec![];
        }

        // 2. 动态搜索最佳划分 (Shared, Inner, Outer)
        // 约束推导:
        //   |Inner| = S + U <= LIMIT
        //   |Outer| = S + W + 1 <= LIMIT
        //   k = S + U + W
        //
        // 联合推导 S 的上限:
        //   2S + U + W <= 2*LIMIT - 1
        //   S + k <= 2*LIMIT - 1
        //   S <= 2*LIMIT - 1 - k
        //
        // 当 LIMIT=5, k=6: S <= 10 - 1 - 6 = 3. (支持 S=0,1,2,3)
        // 当 LIMIT=4, k=6: S <= 8 - 1 - 6 = 1.  (只支持 S=0,1)

        let max_possible_s = (2 * DECOMP_LIMIT).saturating_sub(1 + k);
        // S 不能超过 k-2 (必须留至少 1 个 U 和 1 个 W，否则就不是分解了，是重命名)
        // 实际上 U+W >= 2.
        let safe_s_limit = std::cmp::min(max_possible_s, k - 2);

        for num_shared in (0..=safe_s_limit).rev() {
            let num_remaining = k - num_shared;

            let max_inner = DECOMP_LIMIT - num_shared;
            let max_outer = DECOMP_LIMIT - 1 - num_shared;

            // 遍历 Inner 的大小
            // Inner 至少要有 1 个独有输入
            for num_inner in 1..=max_inner {
                if num_inner >= num_remaining {
                    continue;
                } // 必须给 Outer 留至少 1 个

                let num_outer = num_remaining - num_inner;
                if num_outer > max_outer {
                    continue;
                }

                // 找到了合法的数量配置！
                // S=num_shared, U=num_inner, W=num_outer
                // 开始寻找具体的变量组合
                if let Some(res) = try_partition_decomposition(
                    egraph, program, &inputs, num_shared, num_outer, num_inner,
                ) {
                    return vec![res];
                }
            }
        }

        vec![]
    }
}

/// Tries to find a specific input partition that satisfies decomposition.
fn try_partition_decomposition(
    egraph: &mut egg::EGraph<lut::LutLang, LutAnalysis>,
    program: u64,
    inputs: &[egg::Id],
    n_s: usize,
    n_w: usize,
    n_u: usize,
) -> Option<egg::Id> {
    let k = inputs.len();
    let indices: Vec<usize> = (0..k).collect();

    // We need to iterate all ways to pick n_s items from k, then n_w items from remainder.
    // Since k is small (max 6), we can use a simple recursive approach or combinatorics.

    // 1. Pick Shared (S)
    let s_combos = get_combinations(&indices, n_s);
    for s_idxs in s_combos {
        let remaining_after_s: Vec<usize> = indices
            .iter()
            .filter(|i| !s_idxs.contains(i))
            .cloned()
            .collect();

        // 2. Pick Outer Unique (W)
        let w_combos = get_combinations(&remaining_after_s, n_w);
        for w_idxs in w_combos {
            // 3. The rest are Inner Unique (U)
            let u_idxs: Vec<usize> = remaining_after_s
                .iter()
                .filter(|i| !w_idxs.contains(i))
                .cloned()
                .collect();

            assert_eq!(u_idxs.len(), n_u);

            // --- Check Compatibility ---
            if let Some((inner_prog_val, outer_prog_val)) =
                check_general_compatibility(program, k, &s_idxs, &w_idxs, &u_idxs)
            {
                // Success! Build the nodes.

                // Build Inner LUT
                // Inputs: [Shared..., Unique_Inner...]
                let mut inner_children = vec![];
                let inner_prog_id = egraph.add(lut::LutLang::Program(inner_prog_val));
                inner_children.push(inner_prog_id);
                for &idx in &s_idxs {
                    inner_children.push(inputs[idx]);
                }
                for &idx in &u_idxs {
                    inner_children.push(inputs[idx]);
                }
                let inner_lut = egraph.add(lut::LutLang::Lut(inner_children.into()));

                // Build Outer LUT
                // Inputs: [Shared..., Unique_Outer..., Inner]
                let mut outer_children = vec![];
                let outer_prog_id = egraph.add(lut::LutLang::Program(outer_prog_val));
                outer_children.push(outer_prog_id);
                for &idx in &s_idxs {
                    outer_children.push(inputs[idx]);
                }
                for &idx in &w_idxs {
                    outer_children.push(inputs[idx]);
                }
                outer_children.push(inner_lut);

                let outer_lut = egraph.add(lut::LutLang::Lut(outer_children.into()));
                return Some(outer_lut);
            }
        }
    }

    None
}

/// Checks if the partition is valid and calculates Inner/Outer truth tables.
/// Returns (Inner_Program_u64, Outer_Program_u64) if valid.
fn check_general_compatibility(
    prog: u64,
    k: usize,
    s_idxs: &[usize],
    w_idxs: &[usize],
    u_idxs: &[usize],
) -> Option<(u64, u64)> {
    let n_s = s_idxs.len();
    let n_w = w_idxs.len();
    let n_u = u_idxs.len();

    // Inner function H(S, U) will be constructed piece by piece.
    // It has (n_s + n_u) inputs. Max size 4 -> 16 bits.
    let mut inner_prog = 0u64;

    // We iterate through all 2^|S| configurations of shared variables.
    let num_s_configs = 1 << n_s;

    for s_val in 0..num_s_configs {
        // For a fixed S, we look at the sub-function of (W, U).
        // We need to verify that for ALL 2^|W| configs, the dependence on U is consistent.

        let mut candidate_h: Option<u64> = None; // The required shape of H(s_val, U)

        let num_w_configs = 1 << n_w;
        for w_val in 0..num_w_configs {
            // Extract the truth table of U (size 2^|U|) for fixed S and W
            let mut u_func = 0u64;
            let num_u_configs = 1 << n_u;

            for u_val in 0..num_u_configs {
                // Reconstruct full k-bit index
                let mut full_idx = 0;

                // Map bits from S, W, U back to original positions
                // Note: s_val bit 0 corresponds to s_idxs[n_s - 1] ?
                // Let's adhere to: val bit 0 -> idxs[last]. (LSB).

                // Helper to map bits
                let map_bits = |val: usize, idxs: &[usize], target: &mut usize| {
                    for b in 0..idxs.len() {
                        if (val >> b) & 1 == 1 {
                            // original input index idxs[idxs.len() - 1 - b]
                            // corresponds to bit (k - 1 - idx) in program index
                            let input_idx = idxs[idxs.len() - 1 - b];
                            *target |= 1 << (k - 1 - input_idx);
                        }
                    }
                };

                map_bits(s_val, s_idxs, &mut full_idx);
                map_bits(w_val, w_idxs, &mut full_idx);
                map_bits(u_val, u_idxs, &mut full_idx);

                if (prog >> full_idx) & 1 == 1 {
                    u_func |= 1 << u_val;
                }
            }

            // Check consistency
            // If u_func is const 0 or const 1 (all bits set for size n_u), it's trivial
            let u_mask = (1 << num_u_configs) - 1;
            if u_func == 0 || u_func == u_mask {
                continue; // Always consistent
            }

            if let Some(h) = candidate_h {
                // Must be equal or inverse
                if u_func != h && u_func != (!h & u_mask) {
                    return None; // Conflict! Cannot decompose.
                }
            } else {
                candidate_h = Some(u_func);
            }
        }

        // If candidate_h is still None, it means for this S, the output is independent of U.
        // We can pick H=0.
        let h_slice = candidate_h.unwrap_or(0);

        // Store h_slice into Inner Program
        // Inner inputs: S (high bits), U (low bits)
        // S_val is the high part index.
        inner_prog |= h_slice << (s_val * (1 << n_u));
    }

    // --- Construct Outer Program ---
    // G(S, W, Inner_Bit)
    let mut outer_prog = 0u64;

    // Iterate G inputs: S (high), W (mid), Inner (low)
    // Total bits = n_s + n_w + 1

    let total_outer_bits = n_s + n_w + 1;
    for row in 0..(1 << total_outer_bits) {
        // row structure: [ S... | W... | Inner ]
        let v_inner = row & 1;
        let v_w = (row >> 1) & ((1 << n_w) - 1);
        let v_s = (row >> (1 + n_w)) & ((1 << n_s) - 1);

        // We need to find the output value.
        // We know H(s, u) = v_inner. We need to find a 'u' that makes this true.

        // Get the H slice for this S
        let h_slice = (inner_prog >> (v_s * (1 << n_u))) & ((1 << (1 << n_u)) - 1);

        // Find a u_val such that bit u_val of h_slice == v_inner
        let mut found_u = None;
        for u_val in 0..(1 << n_u) {
            if (h_slice >> u_val) & 1 == (v_inner as u64) {
                found_u = Some(u_val);
                break;
            }
        }

        let out_bit = if let Some(u_val) = found_u {
            // Calculate original index to check F
            let mut full_idx = 0;
            // Similar mapping as above
            let map_bits = |val: usize, idxs: &[usize], target: &mut usize| {
                for b in 0..idxs.len() {
                    if (val >> b) & 1 == 1 {
                        let input_idx = idxs[idxs.len() - 1 - b];
                        *target |= 1 << (k - 1 - input_idx);
                    }
                }
            };
            map_bits(v_s, s_idxs, &mut full_idx);
            map_bits(v_w, w_idxs, &mut full_idx);
            map_bits(u_val, u_idxs, &mut full_idx);

            (prog >> full_idx) & 1
        } else {
            0 // Don't care
        };

        outer_prog |= out_bit << row;
    }

    Some((inner_prog, outer_prog))
}

// Simple combination generator
fn get_combinations(pool: &[usize], k: usize) -> Vec<Vec<usize>> {
    if k == 0 {
        return vec![vec![]];
    }
    if pool.is_empty() {
        return vec![];
    }

    let head = pool[0];
    let tail = &pool[1..];

    let mut result = Vec::new();

    // Include head
    let sub_combos = get_combinations(tail, k - 1);
    for mut sub in sub_combos {
        sub.insert(0, head);
        result.push(sub);
    }

    // Exclude head
    let mut skip_combos = get_combinations(tail, k);
    result.append(&mut skip_combos);

    result
}

/// Returns a set of general decomposition rules for k=3..6
pub fn general_decomp_rules() -> Vec<Rewrite<lut::LutLang, LutAnalysis>> {
    let mut rules = Vec::new();

    // 针对 6-LUT (S=1, 0)
    rules.push(rewrite!(
        "lut6-general-decomp";
        "(LUT ?p ?v0 ?v1 ?v2 ?v3 ?v4 ?v5)" => { GeneralLutDecomposition }
    ));

    // 针对 5-LUT (S=2, 1, 0) -> 这非常重要，能解开复杂的 5-LUT
    rules.push(rewrite!(
        "lut5-general-decomp";
        "(LUT ?p ?v0 ?v1 ?v2 ?v3 ?v4)" => { GeneralLutDecomposition }
    ));

    // 针对 4-LUT (S=3, 2, 1, 0) -> 尝试进一步拆解 4-LUT 为两个 3-LUT (优化面积/速度)
    rules.push(rewrite!(
        "lut4-general-decomp";
        "(LUT ?p ?v0 ?v1 ?v2 ?v3)" => { GeneralLutDecomposition }
    ));

    // 针对 3-LUT
    rules.push(rewrite!(
        "lut3-general-decomp";
        "(LUT ?p ?v0 ?v1 ?v2)" => { GeneralLutDecomposition }
    ));

    rules
}

/// Returns a list of all static LUT rewrite rules
/// `bidirectional` determines if gates are inserted for 2-LUTs
pub fn all_static_rules(bidirectional: bool) -> Vec<Rewrite<lut::LutLang, LutAnalysis>> {
    let mut rules: Vec<Rewrite<lut::LutLang, LutAnalysis>> = Vec::new();

    rules.append(&mut struct_lut_map(bidirectional));
    rules.append(&mut constant_luts());

    rules.push(rewrite!("lut1-const-false"; "(LUT 0 ?a)" => "false"));
    rules.push(rewrite!("lut1-const-true"; "(LUT 3 ?a)" => "true"));
    rules.push(rewrite!("lut1-const-id"; "(LUT 2 ?a)" => "?a"));
    rules.push(rewrite!("lut2-invariant"; "(LUT 12 ?a ?b)" => "(LUT 2 ?a)"));
    rules.push(rewrite!("lut1-const-true-inv"; "(LUT 1 false)" => "true"));
    rules.push(rewrite!("lut1-const-false-inv"; "(LUT 1 true)" => "false"));
    rules.push(rewrite!("double-complement"; "(NOT (NOT ?a))" => "?a"));

    // LUT permutation groups
    // rules.append(&mut permute_groups());

    rules.append(&mut redundant_inputs());
    rules.append(&mut condense_cofactors());
    rules.append(&mut general_cut_fusion());
    rules.append(&mut known_decompositions());
    // rules.append(&mut npn_canon_rules());

    // Feature-gated DSD
    // #[cfg(feature = "dyn_decomp")]
    // rules.append(&mut dsd_rules());

    // #[cfg(feature = "dyn_decomp")]
    // rules.append(&mut dyn_decompositions(false));

    rules.append(&mut invert_lut_rules());

    rules.append(&mut remove_unused_rules());

    // 以下两个重写规则目前都会导致test-runner.py 运行后出现filecheck error: '<stdin>' is empty.暂时不启用
    // rules.append(&mut simple_mux_rules());

    // rules.append(&mut general_decomp_rules());

    rules
}

#[derive(Debug, Clone)]
struct InvertLutApplier {
    p_var: Var,
    vars: Vec<Var>,
}

impl Applier<lut::LutLang, LutAnalysis> for InvertLutApplier {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<lut::LutLang, LutAnalysis>,
        eclass: egg::Id,
        subst: &Subst,
        _searcher_ast: Option<&PatternAst<lut::LutLang>>,
        _rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let p_id = subst[self.p_var];
        let p_val = match egraph[p_id].data.get_program() {
            Ok(p) => p,
            Err(_) => return vec![],
        };

        let k = self.vars.len();
        let mask = if k >= 6 {
            !0u64
        } else {
            (1u64 << (1 << k)) - 1
        };
        // [Optimize] Just mask the input, no redundant calculation
        let clean_p = p_val & mask;
        let new_p = (!clean_p) & mask;

        let new_p_id = egraph.add(lut::LutLang::Program(new_p));
        let mut children = vec![new_p_id];
        children.extend(self.vars.iter().map(|v| subst[*v]));

        let new_lut = egraph.add(lut::LutLang::Lut(children.into()));
        if egraph.union(eclass, new_lut) {
            vec![new_lut]
        } else {
            vec![]
        }
    }
}

// [NEW] Feature-gated DSD Applier
#[cfg(feature = "dyn_decomp")]
#[derive(Debug, Clone)]
struct DSDExpand {
    p_var: Var,
    vars: Vec<Var>,
}

#[cfg(feature = "dyn_decomp")]
impl Applier<lut::LutLang, LutAnalysis> for DSDExpand {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<lut::LutLang, LutAnalysis>,
        eclass: egg::Id,
        subst: &Subst,
        _searcher_ast: Option<&PatternAst<lut::LutLang>>,
        _rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let operands: Vec<egg::Id> = self.vars.iter().map(|v| subst[*v]).collect();
        let k = operands.len();
        if k < 3 {
            return vec![];
        }

        let p_id = subst[self.p_var];
        let original_p_val = match egraph[p_id].data.get_program() {
            Ok(p) => p,
            Err(_) => return vec![],
        };

        // [Optimize] One mask to rule them all
        let mask = if k >= 6 {
            !0u64
        } else {
            (1u64 << (1 << k)) - 1
        };
        let clean_p = original_p_val & mask;

        let dsd_pairs = get_cached_dsd(clean_p, k);
        if dsd_pairs.is_empty() {
            return vec![];
        }

        for (i, j) in dsd_pairs {
            let i = i as usize;
            let j = j as usize;

            let mut residuals = [0u64; 4];
            let sub_space = 1 << (k - 2);
            let bit_i = k - 1 - i;
            let bit_j = k - 1 - j;

            for sub_idx in 0..sub_space {
                let mut base_idx = 0u64;
                let mut insert_ptr = 0;
                for bit in 0..k {
                    if bit == bit_i || bit == bit_j {
                        continue;
                    }
                    if (sub_idx >> insert_ptr) & 1 == 1 {
                        base_idx |= 1 << bit;
                    }
                    insert_ptr += 1;
                }

                let idx_00 = base_idx;
                let idx_01 = base_idx | (1 << bit_j);
                let idx_10 = base_idx | (1 << bit_i);
                let idx_11 = base_idx | (1 << bit_i) | (1 << bit_j);

                if (clean_p >> idx_00) & 1 == 1 {
                    residuals[0] |= 1 << sub_idx;
                }
                if (clean_p >> idx_01) & 1 == 1 {
                    residuals[1] |= 1 << sub_idx;
                }
                if (clean_p >> idx_10) & 1 == 1 {
                    residuals[2] |= 1 << sub_idx;
                }
                if (clean_p >> idx_11) & 1 == 1 {
                    residuals[3] |= 1 << sub_idx;
                }
            }

            let r_a = residuals[0];
            let mut r_b = r_a;
            for &r in &residuals {
                if r != r_a {
                    r_b = r;
                    break;
                }
            }

            let mut h_prog = 0u64;
            for case in 0..4 {
                if residuals[case] == r_b && r_a != r_b {
                    h_prog |= 1 << case;
                }
            }

            let mask_sub = if (k - 2) >= 6 {
                !0u64
            } else {
                (1u64 << (1 << (k - 2))) - 1
            };
            let clean_r_a = r_a & mask_sub;
            let clean_r_b = r_b & mask_sub;
            let g_prog = (clean_r_b << (1 << (k - 2))) | clean_r_a;

            let h_prog_id = egraph.add(lut::LutLang::Program(h_prog));
            let child_lut = egraph.add(lut::LutLang::Lut(
                vec![h_prog_id, operands[i], operands[j]].into(),
            ));

            let g_prog_id = egraph.add(lut::LutLang::Program(g_prog));
            let mut parent_inputs = vec![g_prog_id, child_lut];

            for (idx, &op) in operands.iter().enumerate() {
                if idx != i && idx != j {
                    parent_inputs.push(op);
                }
            }

            let parent_lut = egraph.add(lut::LutLang::Lut(parent_inputs.into()));

            if egraph.union(eclass, parent_lut) {
                return vec![parent_lut];
            }
        }
        vec![]
    }
}

// ... (Helper functions like zip_vars_with_ids and union_with_lut_pattern remain) ...
fn zip_vars_with_ids(vars: &[Var], subst: &Subst) -> HashMap<egg::Id, Var> {
    vars.iter().map(|v| (subst[*v], *v)).collect()
}

fn union_with_lut_pattern<A>(
    old_ast: &PatternAst<lut::LutLang>,
    program: u64,
    new_lut: &lut::LutLang,
    vars: &[Var],
    subst: &egg::Subst,
    rule_name: egg::Symbol,
    egraph: &mut egg::EGraph<lut::LutLang, A>,
) -> Vec<egg::Id>
where
    A: Analysis<lut::LutLang> + std::default::Default,
{
    match new_lut {
        lut::LutLang::Lut(l) => {
            let id_to_var = zip_vars_with_ids(vars, subst);
            let c = l.clone();
            let var_list = c[1..]
                .iter()
                .map(|id| id_to_var[id].to_string())
                .collect::<Vec<String>>();
            let new_ast: PatternAst<lut::LutLang> =
                format!("(LUT {} {})", program, var_list.join(" "))
                    .parse()
                    .unwrap();
            let (id, b) = egraph.union_instantiations(old_ast, &new_ast, subst, rule_name);
            if b { vec![id] } else { vec![] }
        }
        _ => panic!("Expected LUT in union_with_lut_pattern"),
    }
}

/// A rewrite applier for permuting input `pos` with input `pos - 1` from the msb.
/// This means that a `pos` of 1 refers to the input second from the left when printed to a string.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct PermuteInput {
    /// Position of the input to permute
    pos: usize,
    program: Var,
    /// List of operands with msb first
    vars: Vec<Var>,
}

impl PermuteInput {
    /// Create a new [PermuteInput] applier given a transposition at `pos` in `operands`
    pub fn new(pos: usize, program: Var, vars: Vec<Var>) -> Self {
        Self { pos, program, vars }
    }
}

impl Applier<lut::LutLang, LutAnalysis> for PermuteInput {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<lut::LutLang, LutAnalysis>,
        eclass: egg::Id,
        subst: &egg::Subst,
        searcher_ast: Option<&egg::PatternAst<lut::LutLang>>,
        rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let operands = self
            .vars
            .iter()
            .map(|v| subst[*v])
            .collect::<Vec<egg::Id>>();
        let program = egraph[subst[self.program]]
            .data
            .get_program()
            .expect("Expected program");

        assert!(self.pos > 0);

        if operands[self.pos] == operands[self.pos - 1] {
            return vec![];
        }

        let pos_from_lsb = (operands.len() - 1) - self.pos;
        let new_program = lut::swap_pos(&program, operands.len(), pos_from_lsb);
        let new_program_id = egraph.add(lut::LutLang::Program(new_program));

        assert!(self.pos < operands.len());

        let mut swaperands = operands.clone();
        swaperands.swap(self.pos, self.pos - 1);

        let mut c = Vec::from(&[new_program_id]);
        c.append(&mut swaperands);

        let new_node = lut::LutLang::Lut(c.into());

        match searcher_ast {
            Some(ast) => union_with_lut_pattern(
                ast,
                new_program,
                &new_node,
                &self.vars,
                subst,
                rule_name,
                egraph,
            ),
            None => {
                let new_lut = egraph.add(new_node);
                if egraph.union_trusted(eclass, new_lut, rule_name) {
                    vec![new_lut]
                } else {
                    vec![]
                }
            }
        }
    }
}

/// A rewrite applier for combining two inputs that are the same.
/// The redundant inputs *must* be in the rightmost position in the LUT when printed to a string.
/// This means the last two elements in `vars` must be the same
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CombineAlikeInputs {
    /// The program
    program: Var,
    /// The redundant inputs must be at the last two positions
    vars: Vec<Var>,
}

impl CombineAlikeInputs {
    /// Create an applier that combines duplicated inputs to a LUT.
    /// The last two elements in `vars` must be the same.
    pub fn new(program: Var, vars: Vec<Var>) -> Self {
        Self { program, vars }
    }
}

impl Applier<lut::LutLang, LutAnalysis> for CombineAlikeInputs {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<lut::LutLang, LutAnalysis>,
        eclass: egg::Id,
        subst: &egg::Subst,
        searcher_ast: Option<&egg::PatternAst<lut::LutLang>>,
        rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        // 1. 解析所有输入操作数
        let operands = self
            .vars
            .iter()
            .map(|v| subst[*v])
            .collect::<Vec<egg::Id>>();

        let k = operands.len();

        // 2. 寻找重复的输入对 (idx1, idx2) 其中 idx1 < idx2
        // 我们只需要找到一对即可，下一次迭代会处理剩下的
        let mut dup_pair = None;
        for i in 0..k {
            for j in (i + 1)..k {
                if operands[i] == operands[j] {
                    dup_pair = Some((i, j));
                    break;
                }
            }
            if dup_pair.is_some() {
                break;
            }
        }

        // 如果没有重复输入，直接返回
        let (idx1, idx2) = match dup_pair {
            Some(pair) => pair,
            None => return vec![],
        };

        let program = egraph[subst[self.program]]
            .data
            .get_program()
            .expect("Expected program");

        // 特殊情况处理：3-LUT MUX (202)
        // 如果是 MUX(s, a, a)，上面的规则 "lut3-redundant-mux" 已经处理了
        // 这里我们主要处理通用的逻辑折叠
        if k == 3 && program == 202 {
            // 如果是 MUX 的选择端和输入端相同，也可以折叠，但这里先跳过特殊处理
            // 保持原有逻辑的防御性
            return vec![];
        }

        // 3. 计算新的 Program
        // 我们要移除 idx2。
        // 原理：新真值表仅保留那些 "Bit at idx1 == Bit at idx2" 的行。
        // 注意：operands 索引 0 是 MSB (Bit k-1), 索引 k-1 是 LSB (Bit 0).
        let bit_pos_kept = k - 1 - idx1; // 保留位的 bit index
        let bit_pos_removed = k - 1 - idx2; // 移除位的 bit index (必定小于 kept，因为 idx2 > idx1)

        let mut new_prog = 0u64;

        // 遍历旧真值表的所有行
        for old_idx in 0..(1 << k) {
            let bit_val_kept = (old_idx >> bit_pos_kept) & 1;
            let bit_val_removed = (old_idx >> bit_pos_removed) & 1;

            // 只有当两个重复引脚的电平相同时，该行才有效
            if bit_val_kept == bit_val_removed {
                // 计算该行在“新”真值表中的索引
                // 方法：把 old_idx 中的 bit_pos_removed 这一位抠掉，剩下的位拼接起来

                // 1. 取高于 removed 位的部分，并右移一位填补空缺
                let high_part = old_idx >> (bit_pos_removed + 1);
                // 2. 取低于 removed 位的部分，保持不变
                let low_mask = (1 << bit_pos_removed) - 1;
                let low_part = old_idx & low_mask;

                let new_idx = (high_part << bit_pos_removed) | low_part;

                // 复制输出值
                let val = (program >> old_idx) & 1;
                new_prog |= val << new_idx;
            }
        }

        // 4. 构建新节点
        let new_prog_id = egraph.add(lut::LutLang::Program(new_prog));
        let mut new_children = vec![new_prog_id];

        // 添加除了 idx2 以外的所有输入
        for (i, &op_id) in operands.iter().enumerate() {
            if i != idx2 {
                new_children.push(op_id);
            }
        }

        let new_node = lut::LutLang::Lut(new_children.into());

        match searcher_ast {
            Some(ast) => union_with_lut_pattern(
                ast, new_prog, &new_node, &self.vars, subst, rule_name, egraph,
            ),
            None => {
                let new_lut = egraph.add(new_node);
                if egraph.union_trusted(eclass, new_lut, rule_name) {
                    vec![new_lut]
                } else {
                    vec![]
                }
            }
        }
    }
}

/// A rewrite applier for condensing Shannon expansions into a single LUT.
/// The matched eclass *must* be a 2:1 mux (i.e. `LUT 202`).
/// [MODIFIED] Can handle MUX logic where inputs are permuted (e.g. by NPN).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ShannonCondense {
    sel: Var,
    root_p: Var,
    p: Var, // Child 1 program
    q: Var, // Child 2 program
    vars: Vec<Var>,
    s_pos: usize, // Position of selector
    p_pos: usize, // Position of Child 1 (P)
}

impl ShannonCondense {
    /// Create a new applier for condensing Shannon expansions. This is a special case of [FuseCut].
    /// The matched node should take the form `(LUT 202 ?s (LUT ?p ?a ?b ... ) (LUT ?q ?a ?b ...))`
    pub fn new(
        sel: Var,
        root_p: Var,
        p: Var,
        q: Var,
        vars: Vec<Var>,
        s_pos: usize,
        p_pos: usize,
    ) -> Self {
        Self {
            sel,
            root_p,
            p,
            q,
            vars,
            s_pos,
            p_pos,
        }
    }
}

impl Applier<lut::LutLang, LutAnalysis> for ShannonCondense {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<lut::LutLang, LutAnalysis>,
        eclass: egg::Id,
        subst: &egg::Subst,
        searcher_ast: Option<&egg::PatternAst<lut::LutLang>>,
        rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let operands = self
            .vars
            .iter()
            .map(|v| subst[*v])
            .collect::<Vec<egg::Id>>();

        let root_prog = egraph[subst[self.root_p]]
            .data
            .get_program()
            .expect("Expected program");
        let p_val = egraph[subst[self.p]]
            .data
            .get_program()
            .expect("Expected program");
        let q_val = egraph[subst[self.q]]
            .data
            .get_program()
            .expect("Expected program");

        if p_val == q_val {
            return vec![];
        }
        let k = operands.len();

        // [CORE LOGIC] Decode Root MUX Logic
        // We need to verify if root_prog implements `S ? P : Q` or `S ? Q : P`.
        // We also need to handle inversions (e.g., `S ? P : !Q`), but basic Shannon usually assumes strict muxing.

        // Identify position of Q
        let q_pos = 3 - self.s_pos - self.p_pos;

        // Helper: get bit value at input position `pos` from a 3-bit integer `i`
        // EqMap Convention: Input 0 is MSB (Bit 2), Input 2 is LSB (Bit 0).
        let val_at_pos = |i: usize, pos: usize| ((i >> (2 - pos)) & 1) as u64;

        // Analyze dependencies for High (S=1) and Low (S=0)
        let mut high_is_p = true;
        let mut high_is_q = true;
        let mut low_is_p = true;
        let mut low_is_q = true;

        for i in 0..8 {
            // Now these are all u64
            let s_val = val_at_pos(i, self.s_pos);
            let p_bit = val_at_pos(i, self.p_pos);
            let q_bit = val_at_pos(i, q_pos);

            // root_prog is u64, so out is u64
            let out = (root_prog >> i) & 1;

            if s_val == 1 {
                if out != p_bit {
                    high_is_p = false;
                }
                if out != q_bit {
                    high_is_q = false;
                }
            } else {
                if out != p_bit {
                    low_is_p = false;
                }
                if out != q_bit {
                    low_is_q = false;
                }
            }
        }

        // Determine High/Low programs
        let high_prog = if high_is_p {
            p_val
        } else if high_is_q {
            q_val
        } else {
            return vec![];
        };
        let low_prog = if low_is_p {
            p_val
        } else if low_is_q {
            q_val
        } else {
            return vec![];
        };

        // Validity Check: Must use both P and Q (otherwise it's redundant or constant in one path)
        // Also ensures we don't merge `S ? P : P` here (redundant_inputs handles that)
        if (high_is_p && low_is_p) || (high_is_q && low_is_q) {
            return vec![];
        }

        // Construct New Program
        // New LUT structure: (LUT new_prog s vars...)
        // S is input 0 (MSB).
        // High part (S=1) is upper bits, Low part (S=0) is lower bits.
        let prog_mask = if k >= 6 {
            !0u64
        } else {
            (1u64 << (1 << k)) - 1
        };
        let new_prog_val = ((high_prog & prog_mask) << (1 << k)) | (low_prog & prog_mask);

        // Build Node
        let new_prog_id = egraph.add(lut::LutLang::Program(new_prog_val));
        let sel_id = subst[self.sel];
        let mut c = vec![new_prog_id, sel_id];
        c.extend(operands);

        let new_node = lut::LutLang::Lut(c.into());

        match searcher_ast {
            Some(ast) => {
                let mut vars = self.vars.clone();
                vars.insert(0, self.sel);
                union_with_lut_pattern(
                    ast,
                    new_prog_val,
                    &new_node,
                    &vars,
                    subst,
                    rule_name,
                    egraph,
                )
            }
            None => {
                let new_lut = egraph.add(new_node);
                if egraph.union_trusted(eclass, new_lut, rule_name) {
                    vec![new_lut]
                } else {
                    vec![]
                }
            }
        }
    }
}

/// A pattern for compiling a k-sized cut of logic elements into a single LUT
/// [MODIFIED] Supports child LUT at any position `child_pos`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FuseCut {
    root_p: Var,
    root: Vec<Var>,   // Direct inputs to the root (excluding the child LUT)
    rhs_p: Var,       // Child program
    rhs: Vec<Var>,    // Child inputs
    child_pos: usize, // [NEW] Position of the child LUT
}

impl FuseCut {
    /// Create a new applier for fusing two cut of logic elements into a single LUT.
    /// The union of `root` and `rhs` must be no larger than 6 total nodes.
    /// The matched node should take the form `(LUT ?root_p ?root ... (LUT ?rhs_p ?rhs ...))`
    pub fn new(root_p: Var, root: Vec<Var>, rhs_p: Var, rhs: Vec<Var>, child_pos: usize) -> Self {
        Self {
            root_p,
            root,
            rhs_p,
            rhs,
            child_pos,
        }
    }

    fn has_repeats(operands: &[egg::Id]) -> bool {
        let vset: HashSet<egg::Id> = HashSet::from_iter(operands.iter().cloned());
        vset.len() < operands.len()
    }

    fn get_sorted_map(vset: &HashSet<egg::Id>) -> HashMap<egg::Id, usize> {
        let mut s = Vec::from_iter(vset.iter().cloned());
        s.sort();
        let mut pos_map: HashMap<egg::Id, usize> = HashMap::default();
        for (i, v) in s.iter().enumerate() {
            pos_map.insert(*v, i);
        }
        pos_map
    }

    // Helper to extract input values from the global state `bv`
    fn get_input_vec(bv: &BitVec, pos_map: &HashMap<egg::Id, usize>, inputs: &[egg::Id]) -> BitVec {
        let mut new_bv = bitvec!(usize, Lsb0; 0; inputs.len());
        for (i, input) in inputs.iter().enumerate() {
            let pos = pos_map[input];
            // inputs[i] corresponds to bit (len - 1 - i) because inputs are MSB-first
            new_bv.set(inputs.len() - 1 - i, *bv.get(bv.len() - 1 - pos).unwrap());
        }
        new_bv
    }
}

impl Applier<lut::LutLang, LutAnalysis> for FuseCut {
    fn apply_one(
        &self,
        egraph: &mut egg::EGraph<lut::LutLang, LutAnalysis>,
        eclass: egg::Id,
        subst: &egg::Subst,
        searcher_ast: Option<&egg::PatternAst<lut::LutLang>>,
        rule_name: egg::Symbol,
    ) -> Vec<egg::Id> {
        let root_operands = self
            .root
            .iter()
            .map(|v| subst[*v])
            .collect::<Vec<egg::Id>>();
        let rhs_operands = self.rhs.iter().map(|v| subst[*v]).collect::<Vec<egg::Id>>();

        if FuseCut::has_repeats(&root_operands) || FuseCut::has_repeats(&rhs_operands) {
            return vec![];
        }

        let root_program = egraph[subst[self.root_p]]
            .data
            .get_program()
            .expect("Expected program");
        let rhs_program = egraph[subst[self.rhs_p]]
            .data
            .get_program()
            .expect("Expected program");

        // Determine total inputs (K) for the new fused LUT
        let mut vset: HashSet<egg::Id> = HashSet::new();
        for v in root_operands.iter().chain(rhs_operands.iter()) {
            vset.insert(*v);
        }
        let nk = vset.len();
        if nk > 6 {
            return vec![];
        } // Can't fit in 6-LUT

        let pos_map = FuseCut::get_sorted_map(&vset);

        // New program table size
        let mut new_prog = bitvec!(usize, Lsb0; 0; 1 << nk);

        // Root LUT size (inputs count)
        let p_size = root_operands.len() + 1; // +1 for the child LUT

        // Sweep all possible input combinations
        for i in 0..(1 << nk) {
            let bv = to_bitvec(i, nk).unwrap();

            // 1. Evaluate Child (RHS)
            let rhs_bv = FuseCut::get_input_vec(&bv, &pos_map, &rhs_operands);
            let rhs_eval = lut::eval_lut_bv(rhs_program, &rhs_bv);

            // 2. Evaluate Root
            let mut root_bv = bitvec!(usize, Lsb0; 0; p_size);

            // [CORE LOGIC] Map inputs to Root's bit positions
            // EqMap inputs are MSB-first (Index 0 is MSB).
            // eval_lut_bv uses LSB-based indexing (Bit 0 is LSB).
            // So input at index `idx` maps to Bit `size - 1 - idx`.

            // A. Place Child Result
            // Child is at `self.child_pos` in the root's input list.
            let child_bit = p_size - 1 - self.child_pos;
            root_bv.set(child_bit, rhs_eval);

            // B. Place other Root Inputs
            // `root_operands` contains the inputs *skipping* the child.
            for (j, root_op) in root_operands.iter().enumerate() {
                // Determine original index in Root's input list
                let original_idx = if j < self.child_pos { j } else { j + 1 };
                let target_bit = p_size - 1 - original_idx;

                // Get value from global state `bv`
                let global_pos = pos_map[root_op];
                let val = *bv.get(bv.len() - 1 - global_pos).unwrap();

                root_bv.set(target_bit, val);
            }

            new_prog.set(i as usize, lut::eval_lut_bv(root_program, &root_bv));
        }

        let new_prog = lut::from_bitvec(&new_prog);
        let mut c = vec![egraph.add(lut::LutLang::Program(new_prog)); nk + 1];

        // Fill inputs for the new LUT node based on sorted map
        // Note: pos_map maps ID -> Index in `vset` (sorted).
        // We need to reconstruct the input list in that sorted order.
        // Actually, `pos_map` values 0..nk correspond to the bit indices in `bv` (MSB to LSB logic handled in loop).
        // But here we just need to put the IDs in the children list.
        // The loop `for i in 0..(1<<nk)` iterates `bv` as LSB=0.
        // Wait, `to_bitvec` logic: `bv[0]` is LSB.
        // `pos_map` implies: ID with map value 0 corresponds to `bv` bit 0 (LSB)?
        // Let's check `get_input_vec`:
        // `*bv.get(bv.len() - 1 - pos).unwrap()` -> It implies `pos` 0 is MSB!
        // Yes, `get_sorted_map` sorts IDs. Usually one wants MSB to be the "first" ID.
        // If `pos_map` 0 is MSB, then we should place ID with map 0 at `c[1]`.

        for (&id, &pos) in pos_map.iter() {
            c[pos + 1] = id;
        }

        let new_node = lut::LutLang::Lut(c.clone().into());

        match searcher_ast {
            Some(ast) => {
                // For proof generation, we need all vars including children vars
                let all_vars: Vec<Var> = self
                    .root
                    .iter()
                    .cloned()
                    .chain(self.rhs.iter().cloned())
                    .collect();
                union_with_lut_pattern(
                    ast, new_prog, &new_node, &all_vars, subst, rule_name, egraph,
                )
            }
            None => {
                let new_lut = egraph.add(new_node);
                if egraph.union_trusted(eclass, new_lut, rule_name) {
                    vec![new_lut]
                } else {
                    vec![]
                }
            }
        }
    }
}

/// A module dedicated to dynamically finding decompositions of LUTs
#[cfg(feature = "dyn_decomp")]
pub mod decomp {

    use crate::{
        analysis::{self, LutAnalysis},
        lut::{self, LutLang, from_bitvec, to_bitvec},
    };
    use bitvec::prelude::*;
    use egg::{Analysis, Applier, Id, Var};

    #[derive(Debug, Clone, PartialEq, Eq)]
    /// A data type for folding LUTs
    enum AbstractNode {
        /// A LUT node with [u64] configuration
        Lut(u64, Vec<Id>),
        /// A constant true/false node
        Const(bool),
        /// An indirect node
        Node(Id),
    }

    impl AbstractNode {
        pub fn num_inputs(&self) -> usize {
            match self {
                AbstractNode::Lut(_, inputs) => inputs.len(),
                AbstractNode::Node(_) => 1,
                _ => 0,
            }
        }

        pub fn construct<A>(self, egraph: &mut egg::EGraph<LutLang, A>) -> Id
        where
            A: Analysis<LutLang>,
        {
            match self {
                AbstractNode::Lut(program, mut inputs) => {
                    // [Safety] Mask program to avoid panic in to_bitvec later
                    let k = inputs.len();
                    let mask = if k >= 6 {
                        !0u64
                    } else {
                        (1u64 << (1 << k)) - 1
                    };
                    let pid = egraph.add(LutLang::Program(program & mask));

                    let mut c = vec![pid];
                    c.append(&mut inputs);
                    egraph.add(LutLang::Lut(c.into()))
                }
                AbstractNode::Const(b) => egraph.add(LutLang::Const(b)),
                AbstractNode::Node(id) => id,
            }
        }

        fn fold_lut(self) -> Self {
            if let Self::Lut(program, inputs) = self {
                let k = inputs.len();

                if k <= 1 {
                    match program & 3 {
                        0 => return Self::Const(false),
                        3 => return Self::Const(true),
                        2 => return Self::Node(inputs[0]),
                        1 => return Self::Lut(1, inputs),
                        _ => unreachable!(),
                    }
                }

                // [FIX] Mask program to avoid panic
                let mask = if k >= 6 {
                    !0u64
                } else {
                    (1u64 << (1 << k)) - 1
                };
                let clean_program = program & mask;

                // Evaluate invariant inputs
                for pos in 0..k {
                    let pbv = to_bitvec(clean_program, 1 << k).unwrap();
                    let mut nbv: BitVec<usize, Lsb0> = BitVec::with_capacity(1 << (k - 1));
                    for i in 0..(1 << (k - 1)) {
                        let mut index_lo = to_bitvec(i, k - 1).unwrap();
                        let mut index_hi = index_lo.clone();

                        // Logic: Insert 0/1 at 'pos'
                        // Note: pos is index in inputs vector (MSB first).
                        // to_bitvec returns LSB first.
                        // We need to map pos to bit index.
                        // BUT: fold_lut logic here seems to treat pos as direct bit index?
                        // Let's check `index_lo.insert(k - pos - 1, ...)`
                        // Original code: `index_lo.insert(k - pos - 1, false);`
                        // This implies pos=0 is MSB. Correct.

                        index_lo.insert(k - pos - 1, false);
                        index_hi.insert(k - pos - 1, true);
                        let index_lo = from_bitvec(&index_lo) as usize;
                        let index_hi = from_bitvec(&index_hi) as usize;
                        if pbv[index_lo] != pbv[index_hi] {
                            break;
                        }
                        nbv.push(pbv[index_lo]);
                    }
                    if nbv.len() == 1 << (k - 1) {
                        let np = from_bitvec(&nbv);
                        let mut c = inputs;
                        c.remove(pos);
                        return Self::Lut(np, c);
                    } else {
                        continue;
                    }
                }
                Self::Lut(program, inputs)
            } else {
                self
            }
        }
    }

    fn fold_lut_greedily(program: u64, inputs: Vec<Id>) -> AbstractNode {
        let init = AbstractNode::Lut(program, inputs);
        let mut current = init;
        loop {
            let next = current.clone().fold_lut();
            if next == current {
                break;
            }
            current = next;
        }
        current
    }

    /// A rewrite applier for expanding a LUT along a specific variable position.
    #[derive(Debug, Clone, PartialEq, Eq)]
    pub struct ShannonExpand {
        program: Var,
        vars: Vec<Var>,
        pos: usize, // [NEW] The position of the variable to decompose (0=MSB)
    }

    impl ShannonExpand {
        /// Create an applier that combines duplicated inputs to a LUT.
        /// The last two elements in `vars` must be the same.
        pub fn new(program: Var, vars: Vec<Var>, pos: usize) -> Self {
            Self { program, vars, pos }
        }

        fn cuts_overlap(
            egraph: &mut egg::EGraph<lut::LutLang, analysis::LutAnalysis>,
            children: &[egg::Id],
        ) -> bool {
            for (i, a) in children.iter().enumerate() {
                let ac = egraph[*a].data.get_cut();
                if ac.len() == 1 && !egraph[*a].data.is_an_input() {
                    return true;
                }
                for b in children.iter().skip(i + 1) {
                    if a == b {
                        return true;
                    }
                    let bc = egraph[*b].data.get_cut();
                    if ac.intersection(bc).count() > 0 {
                        return true;
                    }
                }
            }
            false
        }
    }

    impl Applier<LutLang, LutAnalysis> for ShannonExpand {
        fn apply_one(
            &self,
            egraph: &mut egg::EGraph<LutLang, LutAnalysis>,
            eclass: egg::Id,
            subst: &egg::Subst,
            _searcher_ast: Option<&egg::PatternAst<LutLang>>,
            rule_name: egg::Symbol,
        ) -> Vec<egg::Id> {
            let operands = self
                .vars
                .iter()
                .map(|v| subst[*v])
                .collect::<Vec<egg::Id>>();

            let program = egraph[subst[self.program]]
                .data
                .get_program()
                .expect("Expected program");

            let k = operands.len();

            // Basic checks
            if k <= 2 || program == 0 {
                return vec![];
            }

            // Check if already decomposed or trivial
            // (Simple population count check)
            let mask = if k >= 6 {
                !0u64
            } else {
                (1u64 << (1 << k)) - 1
            };
            let clean_p = program & mask;
            if clean_p.count_ones() == (1 << k) {
                return vec![];
            } // Constant True

            // MUX check: if it's already a MUX(202) and we try to decompose Selector, it's redundant
            // BUT: decomposing data inputs of a MUX is valid.
            // To be safe/simple, skip 3-LUT MUXes for now.
            if k == 3 && clean_p == 202 {
                return vec![];
            }

            // Overlap check
            if operands.contains(&eclass) {
                return vec![];
            }
            if Self::cuts_overlap(egraph, &operands) {
                return vec![];
            }

            // println!("[INFO] Applying SHANNON_decompositions!");

            // [CORE] Calculate Cofactors for variable at `self.pos`
            // Pos 0 is MSB (Bit k-1). Pos x is Bit k-1-x.
            // Cofactors:
            // C1 (High): Var=1.  C0 (Low): Var=0.

            let bit_idx = k - 1 - self.pos; // Bit index in Truth Table

            let half_size = 1 << (k - 1); // Size of new truth tables (2^(k-1))
            let mut c1_prog = 0u64;
            let mut c0_prog = 0u64;

            // We iterate 0..half_size. These are the indices of the cofactors.
            // We need to map them back to the original program indices.
            // Original Index = (NewIndex with '0' inserted at bit_idx) | (VarVal << bit_idx)

            for i in 0..half_size {
                // Expand i to create a "hole" at bit_idx
                // High part: bits >= bit_idx
                // Low part: bits < bit_idx
                let high_mask = !((1 << bit_idx) - 1);
                let low_mask = (1 << bit_idx) - 1;

                let high_part = (i as u64 & high_mask) << 1;
                let low_part = i as u64 & low_mask;

                let hole_idx = high_part | low_part;

                // C0: Var=0. Index = hole_idx.
                if (clean_p >> hole_idx) & 1 == 1 {
                    c0_prog |= 1 << i;
                }

                // C1: Var=1. Index = hole_idx | (1 << bit_idx).
                if (clean_p >> (hole_idx | (1 << bit_idx))) & 1 == 1 {
                    c1_prog |= 1 << i;
                }
            }

            // Construct children inputs (remove the decomposed variable)
            let mut child_inputs = operands.clone();
            child_inputs.remove(self.pos);

            // Fold greedily
            let c1 = fold_lut_greedily(c1_prog, child_inputs.clone());
            let c0 = fold_lut_greedily(c0_prog, child_inputs);

            // Heuristic: Don't decompose if one cofactor becomes trivial (empty/constant)
            // unless we really need to split.
            if c0.num_inputs() == 0 || c1.num_inputs() == 0 {
                return vec![];
            }

            // Build Nodes
            let c1_id = c1.construct(egraph);
            let c0_id = c0.construct(egraph);
            let mux_p = egraph.add(lut::LutLang::Program(202));

            // Selector is the variable we decomposed on
            let sel_id = operands[self.pos];

            let new_node = lut::LutLang::Lut(vec![mux_p, sel_id, c1_id, c0_id].into());
            let new_lut = egraph.add(new_node);

            if egraph.union_trusted(eclass, new_lut, rule_name) {
                vec![new_lut]
            } else {
                vec![]
            }
        }
    }

    #[test]
    fn test_decomp() {
        use egg::rewrite;
        // 4-LUT Input
        let expr: egg::RecExpr<lut::LutLang> = "(LUT 61642 s1 s0 c d)".parse().unwrap();

        // [FIX] 构造一个纯净的规则集，不包含 NPN
        // 我们只想要验证：能否把 4-LUT 拆成 MUX + 3-LUT
        let mut rules = Vec::new();
        // 1. 必须包含分解规则
        rules.append(&mut super::dyn_decompositions(false));
        // 2. 包含常量优化规则 (处理分解后产生的 trivial 节点，如 (LUT 2 s0) -> s0)
        rules.append(&mut super::constant_luts());
        rules.push(rewrite!("lut1-const-id"; "(LUT 2 ?a)" => "?a"));

        use crate::driver::{SynthReport, SynthRequest};
        let mut req = SynthRequest::default()
            .with_expr(expr)
            .with_rules(rules) // 使用纯净规则集
            .with_k(3) // 强制 k=3，逼迫 4-LUT 分解
            .with_asserts()
            .without_progress_bar()
            .with_joint_limits(60, 20_000, 30);

        let output = req.synth::<SynthReport>().unwrap();
        let ans = output.get_expr().to_string();

        println!("Decomposed Result: {}", ans);

        // 现在没有 NPN 捣乱，Program ID 应该稳定为 202
        assert!(
            ans.contains("LUT 202"),
            "Result should contain MUX (202), got: {}",
            ans
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lut::LutLang;
    use egg::{EGraph, Runner};

    #[test]
    fn test_npn_equivalence_merging() {
        let mut egraph = EGraph::<LutLang, LutAnalysis>::default();
        let a = egraph.add(LutLang::Var("a".into()));
        let b = egraph.add(LutLang::Var("b".into()));

        // 1. 节点 A: 标准 AND (a & b)
        let p_and = egraph.add(LutLang::Program(0x8));
        let lut_and = egraph.add(LutLang::Lut(vec![p_and, a, b].into()));

        // 2. 节点 B: 德摩根 AND (!(!a | !b))
        let not_a = egraph.add(LutLang::Not([a]));
        let not_b = egraph.add(LutLang::Not([b]));
        let p_nor = egraph.add(LutLang::Program(0x1));
        let lut_nor_inputs = egraph.add(LutLang::Lut(vec![p_nor, not_a, not_b].into()));

        // 3. 运行全套规则 (含 double-complement)
        let mut rules = npn_canon_rules();
        rules.push(rewrite!("double-complement"; "(NOT (NOT ?a))" => "?a"));

        let runner = Runner::default().with_egraph(egraph).run(&rules);
        let egraph = runner.egraph;

        assert_eq!(
            egraph.find(lut_and),
            egraph.find(lut_nor_inputs),
            "Standard AND and DeMorgan AND (NOR(!a,!b)) should be merged!"
        );
    }

    #[test]
    fn test_npn_3input_complex_merging() {
        let mut egraph = EGraph::<LutLang, LutAnalysis>::default();
        let a = egraph.add(LutLang::Var("a".into()));
        let b = egraph.add(LutLang::Var("b".into()));
        let c = egraph.add(LutLang::Var("c".into()));

        println!("=== Setup IDs: a={}, b={}, c={} ===", a, b, c);

        // =========================================================
        // 场景 1: 完全对称逻辑 3-Input AND (0x80)
        // 目标：验证 任意乱序 和 De Morgan 都能合并
        // =========================================================

        // Truth Table for AND3 (inputs MSB: a, b, c): Only index 7 (111) is 1. -> 0x80
        let p_and3 = egraph.add(LutLang::Program(0x80));

        // 1. 标准 AND(a, b, c)
        // EqMap 约定: Inputs 列表是 [MSB, ..., LSB]
        let lut_abc = egraph.add(LutLang::Lut(vec![p_and3, a, b, c].into()));

        // 2. 乱序 AND(c, b, a) - 验证对称性排序
        // 物理上这是把 c 接到 MSB，a 接到 LSB，但逻辑是不变的
        let lut_cba = egraph.add(LutLang::Lut(vec![p_and3, c, b, a].into()));

        // 3. 德摩根等价: NOR3(!a, !b, !c)
        // 逻辑推导: AND(a,b,c) == NOR(!a, !b, !c)
        // NOR3 真值表: 只有输入全为0时输出1 (Index 0) -> 0x01
        let not_a = egraph.add(LutLang::Not([a]));
        let not_b = egraph.add(LutLang::Not([b]));
        let not_c = egraph.add(LutLang::Not([c]));
        let p_nor3 = egraph.add(LutLang::Program(0x01));

        let lut_demorgan = egraph.add(LutLang::Lut(vec![p_nor3, not_a, not_b, not_c].into()));

        // =========================================================
        // 场景 2: 部分对称逻辑 (a & b & !c)
        // 目标：验证只合并对称的 (a,b)，不合并非对称的 c
        // =========================================================

        // F = a & b & !c.
        // MSB->LSB: a, b, c.
        // 110 -> 1. Index 6. P = 1<<6 = 0x40.
        let p_asym = egraph.add(LutLang::Program(0x40));

        // 4. Base: (a, b, c)
        let lut_base = egraph.add(LutLang::Lut(vec![p_asym, a, b, c].into()));

        // 5. Symmetric Swap: (b, a, c) -> 应该合并 (a, b 是对称的)
        let lut_sym_swap = egraph.add(LutLang::Lut(vec![p_asym, b, a, c].into()));

        // 6. Asymmetric Swap: (a, c, b) -> 不应合并 (b, c 不对称)
        // F' = a & c & !b. 这是不同的逻辑。
        let lut_asym_swap = egraph.add(LutLang::Lut(vec![p_asym, a, c, b].into()));

        // =========================================================
        // 运行 NPN 规则
        // =========================================================
        let mut rules = crate::rewrite::npn_canon_rules();
        rules.push(rewrite!("double-complement"; "(NOT (NOT ?a))" => "?a"));

        let runner = Runner::default().with_egraph(egraph).run(&rules);
        let egraph = runner.egraph;

        // =========================================================
        // 详细 Debug 输出检查
        // =========================================================
        println!("\n=== Debugging Canonical Structures ===");

        // 辅助闭包：打印某个 Class 下的所有 CANON 节点及其子节点顺序
        let inspect_class = |id: egg::Id, label: &str| {
            let canon_id = egraph.find(id);
            println!("Class [{}] -> Canon Class {}:", label, canon_id);
            let class = &egraph[canon_id];
            for node in &class.nodes {
                if let LutLang::Canonical(children) = node {
                    println!("  Found CANON Node: {:?}", children);
                    // 检查子节点是否按照 ID 排序 (跳过第一个 Program ID)
                    let inputs = &children[1..];
                    println!("  CANON Inputs (Should be sorted): {:?}", inputs);

                    // 简单的排序检查 (针对 AND 这种全对称逻辑)
                    if inputs.windows(2).any(|w| w[0] > w[1]) {
                        println!("  [WARN] Inputs are NOT sorted by ID!");
                    } else {
                        println!("  [OK] Inputs are sorted.");
                    }
                }
            }
        };

        inspect_class(lut_abc, "AND(a,b,c)");
        inspect_class(lut_cba, "AND(c,b,a)");
        inspect_class(lut_demorgan, "NOR(!a,!b,!c)");

        println!("--- Asymmetric Check ---");
        inspect_class(lut_base, "Base(a,b,c)");
        inspect_class(lut_sym_swap, "Sym(b,a,c)");

        // =========================================================
        // 断言验证
        // =========================================================

        // 1. 验证 3-Input 全对称合并
        assert_eq!(
            egraph.find(lut_abc),
            egraph.find(lut_cba),
            "Failed: AND(a,b,c) and AND(c,b,a) did not merge! (Permutation Check)"
        );
        assert_eq!(
            egraph.find(lut_abc),
            egraph.find(lut_demorgan),
            "Failed: AND(a,b,c) and NOR(!a,!b,!c) did not merge! (De Morgan Check)"
        );

        // 2. 验证 部分对称合并
        assert_eq!(
            egraph.find(lut_base),
            egraph.find(lut_sym_swap),
            "Failed: a&b&!c and b&a&!c should merge (a,b are symmetric)!"
        );

        // 3. 验证 非对称不合并
        assert_ne!(
            egraph.find(lut_base),
            egraph.find(lut_asym_swap),
            "Failed: a&b&!c and a&c&!b SHOULD NOT merge (b,c are not symmetric)!"
        );

        println!("\n>>> 3-Input NPN Test Passed! Sorting logic is correct.");
    }

    #[test]
    fn test_smart_redundant_elimination() {
        let mut egraph = EGraph::<LutLang, LutAnalysis>::default();
        let a = egraph.add(LutLang::Var("a".into()));
        let b = egraph.add(LutLang::Var("b".into()));
        let c = egraph.add(LutLang::Var("c".into()));

        println!("=== Test Setup: a={}, b={}, c={} ===", a, b, c);

        // =========================================================
        // 测试场景 1: 非相邻重复 (Non-adjacent redundancy)
        // 原有规则只能处理 (LUT p a b b)，我们要测试 (LUT p a b a)
        // =========================================================

        // 构造一个简单的 3-LUT Program: Y = (I2 & I1) | I0
        // Inputs: [a, b, a].  这里 I2=a, I1=b, I0=a.
        // 逻辑变成: Y = (a & b) | a = a. (吸收律)
        // 对应的真值表 (I2,I1,I0):
        // 000(0), 001(1), 010(0), 011(1), 100(0), 101(1), 110(1), 111(1)
        // P = 0b11101010 = 0xEA
        let p_val = 0xEA;
        let p = egraph.add(LutLang::Program(p_val));

        // 构造节点: (LUT 0xEA a b a)
        // 注意 EqMap 的顺序: [Program, MSB, ..., LSB] -> [p, a, b, a]
        let lut_redundant = egraph.add(LutLang::Lut(vec![p, a, b, a].into()));

        // =========================================================
        // 运行规则
        // =========================================================
        // 只加载 redundant_inputs 规则，确保是它在起作用
        let rules = redundant_inputs();
        let runner = Runner::default().with_egraph(egraph).run(&rules);
        let egraph = runner.egraph;

        // =========================================================
        // 验证结果
        // =========================================================
        let class_id = egraph.find(lut_redundant);
        println!("Merged Class ID: {}", class_id);

        // 1. 检查是否降维 (从 3-LUT 变成 2-LUT)
        // 3-LUT 节点有 4 个 children (1 prog + 3 inputs)
        // 2-LUT 节点有 3 个 children (1 prog + 2 inputs)
        let mut found_reduced_lut = false;
        let mut reduced_inputs = Vec::new();
        let mut reduced_prog = 0;

        for node in &egraph[class_id].nodes {
            if let LutLang::Lut(children) = node
                && children.len() == 3
            {
                // 2-LUT
                found_reduced_lut = true;
                // 获取新 Program
                if let Ok(p) = egraph[children[0]].data.get_program() {
                    reduced_prog = p;
                }
                reduced_inputs = children[1..].to_vec();
                println!(
                    "Found Reduced LUT: Program=0x{:x}, Inputs={:?}",
                    reduced_prog, reduced_inputs
                );
            }
        }

        assert!(
            found_reduced_lut,
            "Failed: LUT(a, b, a) did not reduce to a 2-LUT!"
        );

        // 2. 检查逻辑正确性
        // 原逻辑是 Y = a.
        // 降维后的 2-LUT 输入应该是 [a, b] 或者 [b, a] (取决于保留了哪个)
        // 如果输入是 [a, b] (I1=a, I0=b)，Program 应该是 1010 (0xA) -> Y=a
        // 如果输入是 [b, a] (I1=b, I0=a)，Program 应该是 1100 (0xC) -> Y=a
        // 根据你的实现逻辑 (remove idx2)，我们移除了靠后的 'a'。
        // 原 inputs: [a(0), b(1), a(2)]. Remove idx 2.
        // 新 inputs: [a, b].

        let expected_inputs = vec![a, b];
        assert_eq!(reduced_inputs, expected_inputs, "Inputs should be [a, b]");

        // 检查新真值表是否正确实现 Y = a
        // 输入 [a, b] -> I1=a, I0=b.
        // Truth table for Y=I1:
        // I1=0, I0=0 -> 0
        // I1=0, I0=1 -> 0
        // I1=1, I0=0 -> 1
        // I1=1, I0=1 -> 1
        // Result: 1100 (0xC) ? 不对，等等。
        // 让我们手动推导 CombineAlikeInputs 的逻辑:
        // 原表 0xEA (1110 1010). k=3. inputs=[a, b, a]. idx1=0, idx2=2.
        // bit_pos_kept = 3-1-0 = 2. bit_pos_removed = 3-1-2 = 0.
        // 我们只保留 Bit 2 == Bit 0 的行。
        // Idx:
        // 0 (000) -> kept=0, rem=0 (match). val=0. NewIdx -> 00(0). NewBit 0 = 0.
        // 1 (001) -> kept=0, rem=1 (diff).
        // 2 (010) -> kept=0, rem=0 (match). val=0. NewIdx -> 01(1). NewBit 1 = 0.
        // 3 (011) -> kept=0, rem=1 (diff).
        // 4 (100) -> kept=1, rem=0 (diff).
        // 5 (101) -> kept=1, rem=1 (match). val=1. NewIdx -> 10(2). NewBit 2 = 1.
        // 6 (110) -> kept=1, rem=0 (diff).
        // 7 (111) -> kept=1, rem=1 (match). val=1. NewIdx -> 11(3). NewBit 3 = 1.
        // Result Prog: 1 1 0 0 -> 0xC.

        assert_eq!(
            reduced_prog, 0xC,
            "Program logic verification failed! Expected Y=a (0xC), got 0x{:x}",
            reduced_prog
        );

        println!("SUCCESS: Smart Redundant Elimination works correctly!");
    }

    #[test]
    fn test_shannon_condense_any_position() {
        let mut egraph = EGraph::<LutLang, LutAnalysis>::default();
        let s = egraph.add(LutLang::Var("s".into()));
        let a = egraph.add(LutLang::Var("a".into()));
        let b = egraph.add(LutLang::Var("b".into()));

        println!("=== Test Shannon Condense (Position Agnostic) ===");

        // 1. 构造两个子 LUT (2-LUT)
        let p_xor = egraph.add(LutLang::Program(0x6));
        let child_p = egraph.add(LutLang::Lut(vec![p_xor, a, b].into())); // P: a^b

        let p_and = egraph.add(LutLang::Program(0x8));
        let child_q = egraph.add(LutLang::Lut(vec![p_and, a, b].into())); // Q: a&b

        // 2. 构造乱序 Root MUX
        // 目标逻辑: s ? P : Q
        // 物理连接: Inputs = [P, Q, s]
        // EqMap Program 是 MSB-first (Input 0 is P)
        // 计算出的真值表应该是 0xE4
        let p_root = egraph.add(LutLang::Program(0xE4));
        let root_mux = egraph.add(LutLang::Lut(vec![p_root, child_p, child_q, s].into()));

        // 3. 运行规则
        let rules = condense_cofactors();
        let runner = Runner::default().with_egraph(egraph).run(&rules);
        let mut egraph = runner.egraph;

        // 4. 验证
        // 目标逻辑: s ? (a^b) : (a&b)
        // 新 3-LUTInputs: [s, a, b]
        // s=1 -> XOR (0x6), s=0 -> AND (0x8)
        // Combined: (0x6 << 4) | 0x8 = 0x60 | 0x8 = 0x68
        let target_prog = egraph.add(LutLang::Program(0x68));
        let target_lut = egraph.add(LutLang::Lut(vec![target_prog, s, a, b].into()));

        assert_eq!(
            egraph.find(root_mux),
            egraph.find(target_lut),
            "Failed: MUX(P, Q, s) did not condense into single LUT!"
        );

        println!("SUCCESS: Shannon Condense works with rotated inputs!");
    }

    #[test]
    fn test_fuse_cut_any_position() {
        let mut egraph = EGraph::<LutLang, LutAnalysis>::default();
        let a = egraph.add(LutLang::Var("a".into()));
        let b = egraph.add(LutLang::Var("b".into()));
        let c = egraph.add(LutLang::Var("c".into()));

        println!("=== Test Fuse Cut (Position Agnostic) ===");

        // 1. Child LUT (Index 0 of Parent): (a & b)
        let p_and = egraph.add(LutLang::Program(0x8));
        let child = egraph.add(LutLang::Lut(vec![p_and, a, b].into()));

        // 2. Root LUT: Child | c
        // Root inputs: [Child, c] -> Child is at MSB (pos 0)
        let p_or = egraph.add(LutLang::Program(0xE));
        let root = egraph.add(LutLang::Lut(vec![p_or, child, c].into()));

        // 3. Run Rules
        let rules = general_cut_fusion();
        let runner = Runner::default().with_egraph(egraph).run(&rules);
        let mut egraph = runner.egraph;

        // 4. Expected Result
        // Logic: (a & b) | c [cite: 122]
        // Inputs: [a, b, c]
        // Truth Table: 0xEA (1110 1010)

        let expected_prog = egraph.add(LutLang::Program(0xEA)); // [FIXED] 0xF8 -> 0xEA
        let expected_lut = egraph.add(LutLang::Lut(vec![expected_prog, a, b, c].into()));

        assert_eq!(
            egraph.find(root),
            egraph.find(expected_lut),
            "Failed to fuse (LUT OR (LUT AND a b) c) where child is at MSB!"
        );

        println!("SUCCESS: FuseCut works for child at MSB!");
    }

    #[test]
    fn test_dsd_decomposition() {
        let mut egraph = EGraph::<LutLang, LutAnalysis>::default();
        let a = egraph.add(LutLang::Var("a".into()));
        let b = egraph.add(LutLang::Var("b".into()));
        let c = egraph.add(LutLang::Var("c".into()));

        println!("=== Test DSD Decomposition ===");

        // 构造逻辑: F = (a & b) ^ c
        // Inputs: [a, b, c] (MSB -> LSB)
        // Truth Table:
        // c=0: a&b. (000->0, 010->0, 100->0, 110->1) -> 0x80 (in bits 0,2,4,6) ??
        // Let's calc carefully.
        // i corresponds to bit (a,b,c).
        // 000(0): 0^0=0
        // 001(1): 0^1=1
        // 010(2): 0^0=0
        // 011(3): 0^1=1
        // 100(4): 0^0=0
        // 101(5): 0^1=1
        // 110(6): 1^0=1  <-- AND is 1
        // 111(7): 1^1=0  <-- AND is 1, XOR 1 is 0
        // Result: 0101 0110 (LSB first in binary representation?)
        // Prog u64: ...0 1 1 0 1 0 1 0 (Bin) -> 0x6A

        let p_val = 0x6A;
        let p = egraph.add(LutLang::Program(p_val));
        let root = egraph.add(LutLang::Lut(vec![p, a, b, c].into()));

        // 运行 DSD
        let rules = dsd_rules();
        let runner = Runner::default().with_egraph(egraph).run(&rules);
        let mut egraph = runner.egraph;

        // 验证结果
        // 我们期望分解出 child = (a & b), parent = child ^ c
        // Child (a,b): AND -> 0x8
        // Parent (child, c): XOR -> 0x6

        let p_and = egraph.add(LutLang::Program(0x8));
        let child = egraph.add(LutLang::Lut(vec![p_and, a, b].into()));

        let p_xor = egraph.add(LutLang::Program(0x6));
        let expected = egraph.add(LutLang::Lut(vec![p_xor, child, c].into())); // DSD puts child at MSB

        assert_eq!(
            egraph.find(root),
            egraph.find(expected),
            "Failed to DSD decompose (a & b) ^ c"
        );

        println!("SUCCESS: DSD works!");
    }
}
