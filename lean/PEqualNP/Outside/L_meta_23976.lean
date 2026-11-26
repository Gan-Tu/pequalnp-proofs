import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_23976_aux

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[
    ⟨.and, [1, 2]⟩,
    ⟨.or, [1, 2]⟩,
    ⟨.not, [3]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.and, [0, 7]⟩,
    ⟨.not, [8]⟩,
    ⟨.and, [6, 10]⟩,
    ⟨.or, [9, 11]⟩], 12⟩

end PEqualNP.Outside.L_meta_23976_aux

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_23976 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ ∀ i j : Fin 5, C.eval (List.ofFn fun k : Fin 5 => decide (k = i ∨ k = j)) = (12631 : ℕ).testBit (5 * min i.val j.val + max i.val j.val)) := by
  refine ⟨PEqualNP.Outside.L_meta_23976_aux.witness, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_23976_aux.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
