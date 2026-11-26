import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19356_aux

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[
    ⟨.or, [3, 4]⟩,
    ⟨.or, [1, 9]⟩,
    ⟨.or, [8, 10]⟩,
    ⟨.or, [2, 11]⟩,
    ⟨.or, [7, 12]⟩,
    ⟨.or, [11, 14]⟩,
    ⟨.and, [13, 14]⟩,
    ⟨.not, [16]⟩,
    ⟨.and, [15, 17]⟩], 18⟩

end PEqualNP.Outside.L_meta_19356_aux

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19356 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 9 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (16237180 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19356_aux.witness, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19356_aux.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
