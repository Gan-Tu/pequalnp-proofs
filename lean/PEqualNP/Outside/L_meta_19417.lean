import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19417_aux

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[
    ⟨.or, [0, 8]⟩,
    ⟨.or, [4, 5]⟩,
    ⟨.or, [9, 10]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [3, 12]⟩,
    ⟨.not, [11]⟩,
    ⟨.or, [2, 14]⟩,
    ⟨.not, [16]⟩,
    ⟨.or, [15, 17]⟩,
    ⟨.and, [13, 18]⟩], 19⟩

end PEqualNP.Outside.L_meta_19417_aux

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19417 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 10 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (8151870 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19417_aux.witness, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19417_aux.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
