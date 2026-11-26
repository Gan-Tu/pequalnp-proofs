import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23972_aux

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[
    ⟨.or, [0, 1]⟩,
    ⟨.and, [2, 3]⟩,
    ⟨.or, [2, 3]⟩,
    ⟨.or, [0, 7]⟩,
    ⟨.and, [1, 8]⟩,
    ⟨.not, [9]⟩,
    ⟨.and, [5, 10]⟩,
    ⟨.or, [6, 11]⟩], 12⟩

end PEqualNP.Outside.L_meta_23972_aux

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_23972 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (8797 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_23972_aux.witness, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_23972_aux.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
