import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2163_63
    (normalize : ∀ c : Circuit, FanInTwo c → c.size ≤ 15 →
        (∃ i j : Fin c.gates.length, i≠j ∧ (c.gates.get i).op = .not ∧ (c.gates.get j).op = .not) →
        (∀ x : Fin 9 → Bool, (c.wires (List.ofFn x)).getD 9 false = (x 0 || x 2)) →
        circuitFun 9 c = (fun x : Fin 9 → Bool =>
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) → ∃ d : Circuit, FanInTwo d ∧ d.size ≤ 14 ∧
        d.gates.countP (fun g => !(g.op.eval [false])) ≤ 12 ∧
        (∀ x : Fin 9 → Bool, d.eval (List.ofFn x ++ [x 0 || x 2]) = (circuitFun 9 c) x) ∧
        ∀ i ∈ ([0,1,2,4,7,8] : List (Fin 10)), ∀ w,
          Relation.ReflTransGen (fun a b : ℕ => ∃ j : Fin d.gates.length, b = 10+j.val ∧ a ∈ (d.gates.get j).inputs) i.val w →
          ∀ u v : Fin d.gates.length, w ∈ (d.gates.get u).inputs → w ∈ (d.gates.get v).inputs → u=v)
    (exclude : ¬∃ d : Circuit, FanInTwo d ∧ d.size ≤ 14 ∧
        d.gates.countP (fun g => !(g.op.eval [false])) ≤ 12 ∧
        (∀ x : Fin 9 → Bool, d.eval (List.ofFn x ++ [x 0 || x 2]) = (fun x : Fin 9 → Bool =>
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) x) ∧
        ∀ i ∈ ([0,1,2,4,7,8] : List (Fin 10)), ∀ w,
          Relation.ReflTransGen (fun a b : ℕ => ∃ j : Fin d.gates.length, b = 10+j.val ∧ a ∈ (d.gates.get j).inputs) i.val w →
          ∀ u v : Fin d.gates.length, w ∈ (d.gates.get u).inputs → w ∈ (d.gates.get v).inputs → u=v) :
  ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x1 → (∃ (x3 : Fin x1.gates.length) (x4 : Fin x1.gates.length), x3 ≠ x4 ∧ (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ (x1.gates.get x4).op = PEqualNP.CircuitLowerBounds.GateOp.not ∧ ∀ (x5 : Fin x1.gates.length), (x1.gates.get x5).op = PEqualNP.CircuitLowerBounds.GateOp.not → x5 = x3 ∨ x5 = x4) → (∀ (x4 : Fin (9 : ℕ) → Bool), (x1.wires (List.ofFn x4)).getD (9 : ℕ) Bool.false = (x4 (0 : Fin (9 : ℕ)) || x4 (2 : Fin (9 : ℕ)))) → (PEqualNP.MetaComplexity.circuitFun (9 : ℕ) x1 = fun (x5 : Fin (9 : ℕ) → Bool) => x5 (0 : Fin (9 : ℕ)) && x5 (1 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (2 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (3 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (4 : Fin (9 : ℕ)) || x5 (4 : Fin (9 : ℕ)) && x5 (0 : Fin (9 : ℕ)) || x5 (0 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ)) || x5 (1 : Fin (9 : ℕ)) && x5 (6 : Fin (9 : ℕ)) || x5 (2 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (3 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (5 : Fin (9 : ℕ)) && x5 (7 : Fin (9 : ℕ)) || x5 (6 : Fin (9 : ℕ)) && x5 (8 : Fin (9 : ℕ)) || x5 (8 : Fin (9 : ℕ)) && x5 (5 : Fin (9 : ℕ))) → (16 : ℕ) ≤ x1.size := by

  intro C fan witnesses first computes
  obtain ⟨i,j,ne,hi,hj,_⟩ := witnesses
  by_contra! short
  have eq : circuitFun 9 C = (fun x : Fin 9 → Bool =>
        ([(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)] :
          List (Fin 9 × Fin 9)).any (fun e => x e.1 && x e.2)) := by
    funext x
    simpa only [List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc] using congrFun computes x
  obtain ⟨D,fanD,len,cap,ok,forks⟩ := normalize C fan (by omega) ⟨i,j,ne,hi,hj⟩ first eq
  exact exclude ⟨D,fanD,len,cap,fun x => (ok x).trans (congrFun eq x),forks⟩
