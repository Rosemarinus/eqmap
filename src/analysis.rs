/*!

  The analysis stored with signals in the LUT network.
  In most respects, the analysis helps "type check" for any erroneous rewrite rules.

*/

use super::lut;
use egg::{Analysis, DidMerge};
#[cfg(feature = "cut_analysis")]
use std::collections::HashSet;

/// 1. 定义结构体 (公有，供 rewrite.rs 使用)
#[repr(C)]
#[derive(Debug, Default, Clone, Copy)]
pub struct NpnTransformC {
    /// The canonical form of the truth table (P-equivalent).
    pub canon_prog: u64,
    /// The input permutation vector. perm[i] is the new position of the i-th input.
    pub perm: [i8; 6],
    /// The input phase (negation) mask. Bit i is 1 if the i-th input is inverted.
    pub input_phase: u8,
    /// The output phase (negation). 1 if the output is inverted.
    pub output_phase: u8,
}

// 2. 引入 C++ 函数
unsafe extern "C" {
    unsafe fn Npn_GetTransform(uTruth: u64, n_vars: i32, result: *mut NpnTransformC);
}

/// 3. 安全包装器 (公有) 获取完整的变换信息
pub fn get_npn_transform(tt: u64, k: usize) -> NpnTransformC {
    let mut transform = NpnTransformC::default();
    unsafe {
        Npn_GetTransform(tt, k as i32, &mut transform);
    }
    transform
}

/// An e-class is typically a boolean signal.
/// However, we store constants and input aliases for folding.
/// A [lut::LutLang::Program] should never really be rewritten, so storing programs allow us to quickly check if a class is a program and extract the program.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct LutAnalysisData {
    /// If a class is a Program(u64), it should be by itself
    pub program: Option<u64>,
    /// Is Some(bool) when the class is equivalent to a constant `true` or `false`
    const_val: Option<bool>,
    /// Eventually, this should be a vector so we can store aliases
    input: Option<String>,
    /// The bus size of the node (if it is a bus)
    size: Option<usize>,

    /// [Added] NPN Canonical Signature for fast equivalence checking
    pub npn_class: Option<u64>,

    /// Dominating cut
    #[cfg(feature = "cut_analysis")]
    cut: HashSet<String>,
}

impl LutAnalysisData {
    /// Create a new LutAnalysisData struct
    pub fn new(
        program: Option<u64>,
        const_val: Option<bool>,
        input: Option<String>,
        size: Option<usize>,
    ) -> Self {
        Self {
            program,
            const_val,
            input,
            size,
            npn_class: None, // Initialize as None, filled in make()
            #[cfg(feature = "cut_analysis")]
            cut: HashSet::new(),
        }
    }

    /// Add a cut to the class, removing the old one
    #[cfg(feature = "cut_analysis")]
    pub fn with_cut(self, cut: HashSet<String>) -> Self {
        Self { cut, ..self }
    }

    /// Get the cut
    #[cfg(feature = "cut_analysis")]
    pub fn get_cut(&self) -> &HashSet<String> {
        &self.cut
    }

    /// Merge the child cuts into the class, removing the old one
    #[cfg(feature = "cut_analysis")]
    pub fn merge_cut(
        self,
        egraph: &egg::EGraph<lut::LutLang, LutAnalysis>,
        node: &lut::LutLang,
    ) -> Self {
        let mut cut: HashSet<String> = HashSet::new();
        use egg::Language;
        for c in node.children() {
            for e in &egraph[*c].data.cut {
                cut.insert(e.clone());
            }
        }

        Self { cut, ..self }
    }

    /// Extract the LUT program in this class. If it is an input or gate, throw an error
    pub fn get_program(&self) -> Result<u64, String> {
        match self.program {
            Some(p) => Ok(p),
            None => Err("No program found".to_string()),
        }
    }

    /// Return the constant associated with this class. If it is not a constant, throw an error.
    pub fn get_as_const(&self) -> Result<bool, String> {
        match self.const_val {
            Some(v) => Ok(v),
            None => Err("No constant value found".to_string()),
        }
    }

    /// Returns true if the class is an input
    pub fn is_an_input(&self) -> bool {
        self.input.is_some()
    }
}

/// The analysis struct allows for discovering when signals are equivalent to constants or leaf inputs.
/// Additonally, the struct assists in folding constant inputs to smaller LUTs.
#[derive(Default, Debug, Clone)]
pub struct LutAnalysis;

impl Analysis<lut::LutLang> for LutAnalysis {
    type Data = LutAnalysisData;

    fn merge(&mut self, to: &mut Self::Data, from: Self::Data) -> DidMerge {
        // 1. Program Merge Check
        if to.program.is_some() && from.program.is_some() && to.program != from.program {
            // 这是严重的冲突：同一个节点既被认为是逻辑A，又被认为是逻辑B
            // 在 LUT 优化中，如果出现这种情况，通常意味着逻辑错误或 NPN 碰撞（极罕见）
            // eprintln!("[WARN] Program conflict in merge: {:?} vs {:?}", to.program, from.program);
        }

        // 2. Size 检查
        if let (Some(s1), Some(s2)) = (to.size, from.size)
            && s1 != s2
        {
            panic!("Tried to merge two conflicting bus sizes");
        }

        // 3. Constant Value 检查
        if !(to.const_val == from.const_val || to.const_val.is_none() || from.const_val.is_none()) {
            eprintln!("\n[CRITICAL ERROR] Merge Conflict Detected!");
            eprintln!(
                "  TO:   const_val={:?}, program={:?}",
                to.const_val, to.program
            );
            eprintln!(
                "  FROM: const_val={:?}, program={:?}",
                from.const_val, from.program
            );
            eprintln!(
                "Cannot merge constant type with non-constant type (True vs False conflict)."
            );
        }

        let mut merged = to.clone();
        merged.const_val = to.const_val.or(from.const_val);
        merged.input = to.input.clone().or(from.input.clone());
        merged.npn_class = to.npn_class.or(from.npn_class);
        merged.program = to.program.or(from.program);
        merged.size = to.size.or(from.size);

        #[cfg(feature = "cut_analysis")]
        from.cut.iter().for_each(|x| {
            merged.cut.insert(x.clone());
        });

        let merged_to = merged != *to;
        *to = merged;
        DidMerge(merged_to, *to != from)
    }

    fn make(egraph: &mut egg::EGraph<lut::LutLang, Self>, enode: &lut::LutLang) -> Self::Data {
        let (program_val, k) = match enode {
            lut::LutLang::Program(p) => (Some(*p), 6),
            lut::LutLang::Lut(ids) | lut::LutLang::Canonical(ids) => {
                if ids.is_empty() {
                    // 防御性：空 LUT 视为 Const(False)
                    (Some(0), 0)
                } else {
                    let k = ids.len() - 1;
                    let p = if let Ok(p) = egraph[ids[0]].data.get_program() {
                        Some(p)
                    } else if let lut::LutLang::Program(val) = &egraph[ids[0]].nodes[0] {
                        Some(*val)
                    } else {
                        None
                    };
                    (p, k)
                }
            }
            // 逻辑门支持
            lut::LutLang::And(_) => (Some(0x8), 2),
            lut::LutLang::Nor(_) => (Some(0x1), 2),
            lut::LutLang::Xor(_) => (Some(0x6), 2),
            lut::LutLang::Not(_) => (Some(0x1), 1),
            lut::LutLang::Mux(_) => (Some(0xCA), 3),

            // [修复] 显式处理 Const 节点，赋予其正确的 program 值
            lut::LutLang::Const(c) => {
                let p = if *c { !0u64 } else { 0u64 };
                (Some(p), 0)
            }

            _ => (None, 0),
        };

        // NPN 计算: 仅当 k > 0 时计算，避免对常量调用
        let npn_sig = if k > 0 {
            program_val.map(|p| get_npn_transform(p, k).canon_prog)
        } else {
            None
        };

        // 3. Construct Data
        let mut data = match enode {
            lut::LutLang::Program(p) => LutAnalysisData::new(Some(*p), None, None, None),

            // [修复] 使用计算出的 program 初始化 Const 数据
            lut::LutLang::Const(c) => {
                let p = if *c { !0u64 } else { 0u64 };
                LutAnalysisData::new(Some(p), Some(*c), None, None)
            }

            lut::LutLang::Var(v) => {
                let d = LutAnalysisData::new(None, None, Some(v.to_string()), None);
                #[cfg(feature = "cut_analysis")]
                let d = d.with_cut(HashSet::from([v.to_string()]));
                d
            }
            lut::LutLang::Arg([index]) => {
                let index_val = egraph[*index]
                    .data
                    .get_program()
                    .expect("Expected Arg child to be an index");
                let name = "arg".to_string() + &index_val.to_string();
                let d = LutAnalysisData::new(None, None, Some(name.clone()), None);
                #[cfg(feature = "cut_analysis")]
                let d = d.with_cut(HashSet::from([name]));
                d
            }
            lut::LutLang::Bus(b) => LutAnalysisData::new(None, None, None, Some(b.len())),
            _ => {
                let d = LutAnalysisData::default();
                #[cfg(feature = "cut_analysis")]
                let d = d.merge_cut(egraph, enode);
                d
            }
        };

        // 4. Fill in NPN and Program info
        data.npn_class = npn_sig;

        if let Some(p) = program_val {
            if matches!(enode, lut::LutLang::Lut(_)) {
                data.program = Some(p);

                // [增强] 检查 LUT 是否实质上是常量
                // 如果一个 LUT 的真值表全0或全1，它就是常量。
                // 这能帮助 E-Graph 尽早发现 LUT(0) 和 Const(false) 是等价的。
                let mask = if k >= 6 {
                    !0u64
                } else {
                    (1u64 << (1 << k)) - 1
                };
                let masked_p = p & mask;

                if masked_p == 0 {
                    data.const_val = Some(false);
                } else if masked_p == mask {
                    data.const_val = Some(true);
                }
            }
        }

        data
    }

    #[cfg(feature = "egraph_fold")]
    fn modify(egraph: &mut egg::EGraph<lut::LutLang, Self>, id: egg::Id) {
        let nodes = egraph[id].nodes.clone();
        for node in nodes {
            if let lut::LutLang::Lut(_) = node {
                let operands = node.get_operand_classes(egraph).expect("Expected operands");
                let msb_const = egraph[operands[0]].data.get_as_const();
                let program = node
                    .get_program_in_egraph(egraph)
                    .expect("Expected program");
                let k = operands.len();

                // Refactor LUT invariant to input at lsb
                if let Some(np) = lut::remove_lsb_var(program, k) {
                    let mut c = operands.clone();
                    let pi = egraph.add(lut::LutLang::Program(np));
                    c.pop();
                    c.insert(0, pi);
                    let repl = egraph.add(lut::LutLang::Lut(c.into()));
                    egraph.union(id, repl);
                }

                // Evaluate constant input at the msb
                if msb_const.is_ok() {
                    if operands.len() > 1 {
                        let mod_program = lut::eval_lut_const_input(
                            &program,
                            operands.len() - 1,
                            msb_const.unwrap(),
                        );
                        let pi = egraph.add(lut::LutLang::Program(mod_program));
                        let mut c = operands.clone();
                        c[0] = pi;
                        let repl = egraph.add(lut::LutLang::Lut(c.into()));
                        egraph.union(id, repl);
                    } else {
                        // Constant folding for 0-input LUTs (which rely on program bits)
                        let const_val = msb_const.unwrap();
                        match program & 3 {
                            0 => {
                                let repl = egraph.add(lut::LutLang::Const(false));
                                egraph.union(id, repl);
                            }
                            3 => {
                                let repl = egraph.add(lut::LutLang::Const(true));
                                egraph.union(id, repl);
                            }
                            2 => {
                                let repl = egraph.add(lut::LutLang::Const(const_val));
                                egraph.union(id, repl);
                            }
                            1 => {
                                let repl = egraph.add(lut::LutLang::Const(!const_val));
                                egraph.union(id, repl);
                            }
                            _ => unreachable!(),
                        }
                    }
                }
            }
        }
    }
}
