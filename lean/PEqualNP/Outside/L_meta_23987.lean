import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23987_aux

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.or, [1, 4]⟩,
    ⟨.and, [2, 6]⟩,
    ⟨.or, [3, 6]⟩,
    ⟨.not, [7]⟩,
    ⟨.and, [5, 8]⟩,
    ⟨.or, [2, 10]⟩,
    ⟨.and, [9, 11]⟩], 12⟩

end PEqualNP.Outside.L_meta_23987_aux

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_23987 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (13150 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_23987_aux.witness, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_23987_aux.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
