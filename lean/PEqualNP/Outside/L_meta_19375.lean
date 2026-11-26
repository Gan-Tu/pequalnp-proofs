import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_19375_aux

open PEqualNP.CircuitLowerBounds

def witness : Circuit :=
  ⟨[
    ⟨.or, [1, 2]⟩,
    ⟨.or, [5, 10]⟩,
    ⟨.or, [6, 7]⟩,
    ⟨.or, [11, 12]⟩,
    ⟨.or, [0, 12]⟩,
    ⟨.and, [11, 14]⟩,
    ⟨.not, [15]⟩,
    ⟨.and, [13, 16]⟩], 17⟩

end PEqualNP.Outside.L_meta_19375_aux

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_19375 : (∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C ∧ C.size ≤ 8 ∧ PEqualNP.Represents.Represents (fun u v : Fin 5 => (7595814 : ℕ).testBit (5 * u.val + v.val)) C) := by
  refine ⟨PEqualNP.Outside.L_meta_19375_aux.witness, ?_, ?_, ?_⟩
  · intro g hg
    simp only [PEqualNP.Outside.L_meta_19375_aux.witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · decide
  · decide +kernel
