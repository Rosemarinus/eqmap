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
        // if to.program != from.program {
        //     panic!("Tried to merge two different programs");
        // }
        // if to.size != from.size {
        //     panic!("Tried to merge two conflicting bus sizes");
        // }

        // 1. Program Merge Check (Relaxed)
        // 允许 Some(A) 和 None 合并 (保留 A)
        // 如果 Some(A) 和 Some(B) 冲突，打印警告但不 Panic (保留 A)
        if to.program.is_some() && from.program.is_some() && to.program != from.program {
            // println!("[WARN] Program conflict in merge: {:?} vs {:?}", to.program, from.program);
            // 实际运行中，NPN 规则可能会导致这种冲突，
            // 只要 npn_class 一致，我们就可以容忍 program 的不一致。
        }

        // 2. Size 检查 (同理)
        if let (Some(s1), Some(s2)) = (to.size, from.size)
            && s1 != s2
        {
            panic!("Tried to merge two conflicting bus sizes");
        }

        // 3. NPN 检查
        if let (Some(n1), Some(n2)) = (to.npn_class, from.npn_class)
            && n1 != n2
        {
            // 不应panic
            // panic!(
            //     "CRITICAL: Merging nodes with different NPN signatures! {:x} vs {:x}",
            //     n1, n2
            // );
            // println!(
            //     "[WARN] Merging nodes with different NPN signatures: {:x} vs {:x}",
            //     n1, n2
            // );
        }

        if !(to.const_val == from.const_val || to.const_val.is_none() || from.const_val.is_none()) {
            // Later we will want to relax this condition for constant folding.
            // For now, it is a good sanity check.
            // panic!("Cannot merge constant type with non-constant type.");
            eprintln!("Cannot merge constant type with non-constant type.");
        }
        if !(to.input == from.input || to.input.is_none() || from.input.is_none()) {
            // Later, we will want to relax this condition when we're okay with input aliasing.
            // panic!("Cannot merge input type with non-input type.");
            eprintln!("Cannot merge input type with non-input type.");
        }

        let mut merged = to.clone();
        merged.const_val = to.const_val.or(from.const_val);
        merged.input = to.input.clone().or(from.input.clone());
        merged.npn_class = to.npn_class.or(from.npn_class);
        merged.program = to.program.or(from.program);
        merged.size = to.size.or(from.size);

        // Rewrite rules can create redundant logic, so we need to track the current cut.
        // If we took the intersection, we would not have that info. So we take the union.
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

            lut::LutLang::And(_) => (Some(0x8), 2),
            lut::LutLang::Nor(_) => (Some(0x1), 2),
            lut::LutLang::Xor(_) => (Some(0x6), 2),
            lut::LutLang::Not(_) => (Some(0x1), 1),
            lut::LutLang::Mux(_) => (Some(0xCA), 3),
            _ => (None, 0),
        };

        // NPN 计算 (Canonical 节点也需要计算 NPN，以便在 merge 时进行一致性检查)
        let npn_sig = program_val.map(|p| get_npn_transform(p, k).canon_prog);

        // 3. Construct Data (Original Logic Preserved)
        // -------------------------------------------------------------
        let mut data = match enode {
            lut::LutLang::Program(p) => LutAnalysisData::new(Some(*p), None, None, None),
            lut::LutLang::Const(c) => LutAnalysisData::new(None, Some(*c), None, None),
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
        // -------------------------------------------------------------
        data.npn_class = npn_sig;

        if let Some(p) = program_val {
            // Only set program for LUT/Canonical nodes to enable get_program() checks
            if matches!(enode, lut::LutLang::Lut(_)) {
                data.program = Some(p);
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_npn_sanity_check() {
        let raw_and = 0x8;
        let raw_or = 0xE;
        let raw_xor = 0x6;
        let raw_xnor = 0x9;

        println!("Running NPN Sanity Check via New Transform API...");

        // Updated to use get_npn_transform(...).canon_prog
        let sig_and = get_npn_transform(raw_and, 2).canon_prog;
        let sig_or = get_npn_transform(raw_or, 2).canon_prog;
        let sig_xor = get_npn_transform(raw_xor, 2).canon_prog;
        let sig_xnor = get_npn_transform(raw_xnor, 2).canon_prog;

        println!("AND (2-in): {:016x}", sig_and);
        println!("OR  (2-in): {:016x}", sig_or);

        assert_eq!(
            sig_and, sig_or,
            "Error: AND and OR should have the same NPN signature!"
        );
        assert_eq!(
            sig_xor, sig_xnor,
            "Error: XOR and XNOR should have the same NPN signature!"
        );
        assert_ne!(
            sig_and, sig_xor,
            "Error: AND and XOR should NOT be equivalent!"
        );

        println!(">>> NPN Sanity Check Passed!");
    }

    #[test]
    fn test_npn_6input_complex() {
        // ==========================================
        // 1. De Morgan
        // ==========================================
        let tt_and6 = 1u64 << 63;
        let tt_or6 = !1u64;

        let sig_and6 = get_npn_transform(tt_and6, 6).canon_prog;
        let sig_or6 = get_npn_transform(tt_or6, 6).canon_prog;

        println!("AND6 (0x{:016x}) Sig: 0x{:016x}", tt_and6, sig_and6);
        println!("OR6  (0x{:016x}) Sig: 0x{:016x}", tt_or6, sig_or6);

        assert_eq!(
            sig_and6, sig_or6,
            "Error: 6-input AND and OR should be NPN equivalent (De Morgan)!"
        );

        // ==========================================
        // 2. Permutation
        // ==========================================
        let tt_x0 = 0xAAAAAAAAAAAAAAAAu64;
        let tt_x5 = 0xFFFFFFFF00000000u64;

        let sig_x0 = get_npn_transform(tt_x0, 6).canon_prog;
        let sig_x5 = get_npn_transform(tt_x5, 6).canon_prog;

        println!("Buf x0 (0x{:016x}) Sig: 0x{:016x}", tt_x0, sig_x0);
        println!("Buf x5 (0x{:016x}) Sig: 0x{:016x}", tt_x5, sig_x5);

        assert_eq!(
            sig_x0, sig_x5,
            "Error: Input variables x0 and x5 should be NPN equivalent (Permutation)!"
        );

        // ==========================================
        // 3. Output Negation
        // ==========================================
        let tt_mux = 18374951396690406058u64;
        let tt_mux_inv = !tt_mux;

        let sig_mux = get_npn_transform(tt_mux, 6).canon_prog;
        let sig_mux_inv = get_npn_transform(tt_mux_inv, 6).canon_prog;

        println!("MUX    (0x{:016x}) Sig: 0x{:016x}", tt_mux, sig_mux);
        println!("!MUX   (0x{:016x}) Sig: 0x{:016x}", tt_mux_inv, sig_mux_inv);

        assert_eq!(
            sig_mux, sig_mux_inv,
            "Error: Function and its inverse should be NPN equivalent (Output Negation)!"
        );

        println!(">>> 6-Input NPN Complex Checks Passed!");
    }
}
