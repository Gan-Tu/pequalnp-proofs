import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19382_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def witness (n : ℕ) : Circuit :=
  ⟨[⟨.or, [1, n]⟩, ⟨.or, [n + 1, n + 2]⟩, ⟨.or, [2 * n, 2 * n + 1]⟩, ⟨.or, [2 * n + 1, 0]⟩,
    ⟨.and, [2 * n, 2 * n + 3]⟩, ⟨.not, [2 * n + 4]⟩, ⟨.and, [2 * n + 2, 2 * n + 5]⟩], 2 * n + 6⟩

theorem basis (n : ℕ) : FanInTwo (witness n) := by
  intro g hg
  simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp

theorem getLo (x t : List Bool) (i : ℕ) (h : i < x.length) :
    (x ++ t).getD i false = x.getD i false :=
  List.getD_append x t false i h

theorem getHi (x t : List Bool) (m j : ℕ) (hm : x.length = m) :
    (x ++ t).getD (m + j) false = t.getD j false := by
  subst hm
  rw [List.getD_append_right x t false _ (Nat.le_add_right _ _)]
  simp

theorem getHi0 (x t : List Bool) (m : ℕ) (hm : x.length = m) :
    (x ++ t).getD m false = t.getD 0 false := by
  have := getHi x t m 0 hm
  simpa using this

theorem evalGen (n : ℕ) (hn : 3 ≤ n) (x : List Bool) (hx : x.length = 2 * n) :
    (witness n).eval x =
      (((x.getD 1 false || x.getD n false) || (x.getD (n + 1) false || x.getD (n + 2) false)) &&
        !((x.getD 1 false || x.getD n false) &&
          ((x.getD (n + 1) false || x.getD (n + 2) false) || x.getD 0 false))) := by
  have h0 : 0 < x.length := by omega
  have h1 : 1 < x.length := by omega
  have h2 : n < x.length := by omega
  have h3 : n + 1 < x.length := by omega
  have h4 : n + 2 < x.length := by omega
  simp only [Circuit.eval, Circuit.wires, witness, List.foldl_cons, List.foldl_nil, List.map_cons,
    List.map_nil, GateOp.eval, List.append_assoc, List.cons_append, List.nil_append,
    List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.headD_cons, id_eq,
    Bool.and_true, Bool.or_false,
    getLo x _ 0 h0, getLo x _ (n + 1) h3, getLo x _ (n + 2) h4,
    getHi x _ (2 * n) _ hx, getHi0 x _ (2 * n) hx,
    List.getD_cons_zero, List.getD_cons_succ]

theorem oeRow {n : ℕ} (u v : Fin n) (i : ℕ) (hi : i < n) :
    (oneEach u v).getD i false = decide (i = u.val) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simpa using hi)]
  simp [List.getD_eq_getElem?_getD, hi, Fin.ext_iff]

theorem oeCol {n : ℕ} (u v : Fin n) (j : ℕ) (hj : j < n) :
    (oneEach u v).getD (n + j) false = decide (j = v.val) := by
  unfold oneEach
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, hj, Fin.ext_iff]

theorem represents (n : ℕ) (hn : 3 ≤ n) :
    Represents (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ (v.val = 1 ∨ v.val = 2)) ∨ (u.val = 1 ∧ ¬ (v.val = 1 ∨ v.val = 2)) ∨ (2 ≤ u.val ∧ v.val ≤ 2))) (witness n) := by
  intro u v
  have hlen : (oneEach u v).length = 2 * n := by simp [oneEach]; omega
  rw [evalGen n hn _ hlen, oeRow u v 0 (by omega), oeRow u v 1 (by omega)]
  have c0 := oeCol u v 0 (by omega)
  have c1 := oeCol u v 1 (by omega)
  have c2 := oeCol u v 2 (by omega)
  simp only [Nat.add_zero] at c0
  rw [c0, c1, c2]
  have hu := u.isLt
  have hv := v.isLt
  rw [Bool.eq_iff_iff]
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff,
    Bool.or_eq_false_iff, decide_eq_true_eq, decide_eq_false_iff_not]
  omega

end PEqualNP.Outside.L_meta_19382_aux

theorem PEqualNP.Outside.L_meta_19382 : (∀ n : ℕ, 3 ≤ n → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 7 ∧ PEqualNP.Represents.Represents (fun (u : Fin n) (v : Fin n) => decide ((u.val = 0 ∧ (v.val = 1 ∨ v.val = 2)) ∨ (u.val = 1 ∧ ¬ (v.val = 1 ∨ v.val = 2)) ∨ (2 ≤ u.val ∧ v.val ≤ 2))) C) :=
  fun n hn => ⟨PEqualNP.Outside.L_meta_19382_aux.witness n, PEqualNP.Outside.L_meta_19382_aux.basis n,
    by simp [PEqualNP.Outside.L_meta_19382_aux.witness, PEqualNP.CircuitLowerBounds.Circuit.size],
    PEqualNP.Outside.L_meta_19382_aux.represents n hn⟩
