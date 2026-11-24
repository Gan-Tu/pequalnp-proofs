import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.ReadK

-- Separate the coefficients with one marked leaf from the edges requiring both repeats.
-- The first question asks for all one-leaf coefficients in one shared circuit.
-- Its construction can evaluate the circuit with marked inputs zero and propagate
-- contexts backwards, multiplying by the unused operand at each AND.
-- The second counts only edges with a short witness and no one-leaf coefficient on either side.
theorem PEqualNP.Outside.R_meta_1942_31 :
  (∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
    IsAO2 (N + N) C →
    (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
    ∀ swap : Bool,
      let hit := fun p l : Fin N =>
        lineSingle C (N + N) (fun i => if swap then decide (i < N) else decide (N ≤ i))
          (if swap then l.val else p.val) (N + if swap then p.val else l.val)
      ∃ (D : Circuit) (r : Fin N → ℕ) (W : Finset (Fin N)),
        IsAO2 N D ∧ D.size + W.card ≤ 4 * C.size + 1 ∧
        (∀ p l, hit p l = true → l ∈ W ∧
          (D.wires (List.ofFn fun i => decide (i = p))).getD (r l) false = true) ∧
        (∀ l ∈ W, (D.wires (List.ofFn fun p =>
          if swap then decide (¬ I l p) else decide (¬ I p l))).getD (r l) false = false)) →
  (∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
    2 ≤ q → N = q ^ 2 + q + 1 →
    (∀ l : Fin N, ∃ S : Finset (Fin N), S.card = q + 1 ∧ ∀ p, p ∈ S ↔ I p l) →
    (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
    IsAO2 (N + N) C →
    (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
    ∀ E : Finset (Fin N × Fin N), (∀ e ∈ E,
      I e.1 e.2 ∧ readsAtMost C (N + N)
        (setList {Fin.castAdd N e.1, Fin.natAdd N e.2}) 2 = true ∧
      lineSingle C (N + N) (fun i => decide (N ≤ i)) e.1.val (N + e.2.val) = false ∧
      lineSingle C (N + N) (fun i => decide (i < N)) e.1.val (N + e.2.val) = false) →
      E.card ≤ 84 * C.size) →
  ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
    2 ≤ q → N = q ^ 2 + q + 1 →
    (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) →
    (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
    IsAO2 (N + N) C →
    (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
      decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
    IsReadK (N + N) C 2 → N * q ≤ 100 * C.size := by
  intro extract residualBound q N I inst C hq order regular uniqueLine allowed computes readTwo
  classical
  have columnCharge (N : ℕ) (J : Fin N → Fin N → Prop) [DecidableRel J]
      (rect : ∀ p p' l l', p ≠ p' → l ≠ l' → J p l → J p l' → J p' l → J p' l' → False)
      (D : Circuit) (roots : Fin N → ℕ) (labels : Finset (Fin N)) (mono : IsAO2 N D)
      (off : ∀ l ∈ labels,
        (D.wires (List.ofFn fun p => decide (¬ J p l))).getD (roots l) false = false) :
      (Finset.univ.filter (fun e : Fin N × Fin N => e.2 ∈ labels ∧
        (D.wires (List.ofFn fun i => decide (i = e.1))).getD (roots e.2) false = true)).card ≤
          2 * D.size + labels.card := by
    classical
    let F := (Fin N → Bool) → Bool
    let zero : F := fun _ => false
    let onePoint := fun (p i : Fin N) => decide (i = p)
    let outside := fun (l i : Fin N) => decide (¬ J i l)
    let alive (f : F) := Finset.univ.filter fun p => f (onePoint p) = true
    let dark (f : F) := Finset.univ.filter fun l => f (outside l) = false
    let honest (f : F) := ∀ p ∈ alive f, ∀ l ∈ dark f, J p l
    let heavy (f : F) : Finset (Fin N × Fin N) :=
      if 2 ≤ (alive f).card then alive f ×ˢ dark f else ∅
    let small (A : Finset (Fin N)) := if A.card ≤ 1 then A else ∅
    have smallCard (A : Finset (Fin N)) : (small A).card ≤ 1 := by
      by_cases h : A.card ≤ 1 <;> simp [small, h]
    have zeroOK : honest zero ∧ heavy zero = ∅ := by simp [honest, heavy, alive, zero]
    have leaves (i : Fin N) : honest (fun x => x i) ∧ heavy (fun x => x i) = ∅ := by
      have eq : alive (fun x => x i) = {i} := by
        ext p
        simp only [alive, onePoint, Finset.mem_filter, Finset.mem_univ, true_and,
          decide_eq_true_eq, Finset.mem_singleton]
        exact eq_comm
      simp [honest, heavy, eq, dark, outside]
    have chooseAnd : ∀ a b c d : Bool, (a && b) = true → (c && d) = false →
        (a = true ∧ c = false) ∨ (b = true ∧ d = false) := by decide
    have chooseOr : ∀ a b c d : Bool, (a || b) = true → (c || d) = false →
        (a = true ∧ c = false) ∨ (b = true ∧ d = false) := by decide
    have andTwo (a b : Bool) : GateOp.and.eval [a,b] = (a && b) := by cases a <;> cases b <;> rfl
    have orTwo (a b : Bool) : GateOp.or.eval [a,b] = (a || b) := by cases a <;> cases b <;> rfl
    have addWire (a b f : F) (A : Finset (Fin N × Fin N)) (ha : honest a) (hb : honest b)
        (ca : heavy a ⊆ A) (cb : heavy b ⊆ A)
        (selects : ∀ p l, p ∈ alive f → l ∈ dark f →
          (p ∈ alive a ∧ l ∈ dark a) ∨ (p ∈ alive b ∧ l ∈ dark b)) :
        honest f ∧ ∃ B, A ⊆ B ∧ heavy f ⊆ B ∧ B.card ≤ A.card + 2 := by
      have hf : honest f := by
        intro p hp l hl
        obtain h | h := selects p l hp hl
        · exact ha p h.1 l h.2
        · exact hb p h.1 l h.2
      refine ⟨hf, ?_⟩
      by_cases big : 2 ≤ (alive f).card
      · have uniqueLabel : (dark f).card ≤ 1 := by
          rw [Finset.card_le_one]
          intro l hl l' hl'
          by_contra ne
          obtain ⟨p,hp,p',hp',hne⟩ := Finset.one_lt_card.mp big
          exact rect p p' l l' hne ne (hf p hp l hl) (hf p hp l' hl')
            (hf p' hp' l hl) (hf p' hp' l' hl')
        let tiny := small (alive a) ∪ small (alive b)
        let extra := tiny ×ˢ dark f
        have ht : tiny.card ≤ 2 := (Finset.card_union_le _ _).trans
          (Nat.add_le_add (smallCard _) (smallCard _))
        have he : extra.card ≤ 2 := by
          change (tiny ×ˢ dark f).card ≤ 2
          rw [Finset.card_product]
          exact Nat.mul_le_mul ht uniqueLabel
        refine ⟨A ∪ extra, Finset.subset_union_left, ?_, (Finset.card_union_le _ _).trans (by omega)⟩
        intro e mem
        obtain ⟨hp,hl⟩ := Finset.mem_product.mp (by simpa [heavy, big] using mem)
        obtain h | h := selects e.1 e.2 hp hl
        · by_cases large : 2 ≤ (alive a).card
          · exact Finset.mem_union_left _ (ca (by simpa [heavy, large] using Finset.mem_product.mpr h))
          · have lone : (alive a).card ≤ 1 := by omega
            exact Finset.mem_union_right _ (Finset.mem_product.mpr
              ⟨Finset.mem_union_left _ (by simpa [small, lone] using h.1), hl⟩)
        · by_cases large : 2 ≤ (alive b).card
          · exact Finset.mem_union_left _ (cb (by simpa [heavy, large] using Finset.mem_product.mpr h))
          · have lone : (alive b).card ≤ 1 := by omega
            exact Finset.mem_union_right _ (Finset.mem_product.mpr
              ⟨Finset.mem_union_right _ (by simpa [small, lone] using h.1), hl⟩)
      · exact ⟨A, fun _ h => h, by simp [heavy, big], by omega⟩
    let get := fun (w : List F) (i : ℕ) => w.getD i zero
    let make := fun (w : List F) (g : Gate) (x : Fin N → Bool) =>
      g.op.eval (g.inputs.map fun i => get w i x)
    let appendGate := fun (w : List F) (g : Gate) => w ++ [make w g]
    let valid := fun (w : List F) (A : Finset (Fin N × Fin N)) =>
      ∀ f ∈ w, honest f ∧ heavy f ⊆ A
    have lookup (w : List F) (A : Finset (Fin N × Fin N)) (hw : valid w A) (i : ℕ) :
        honest (get w i) ∧ heavy (get w i) ⊆ A := by
      by_cases hi : i < w.length
      · change honest (w.getD i zero) ∧ heavy (w.getD i zero) ⊆ A
        rw [List.getD_eq_getElem _ _ hi]
        exact hw _ (List.getElem_mem hi)
      · have he : get w i = zero := List.getD_eq_default _ _ (by omega)
        rw [he, zeroOK.2]
        exact ⟨zeroOK.1, Finset.empty_subset _⟩
    have accumulate (gs : List Gate)
        (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2)
        (w : List F) (A : Finset (Fin N × Fin N)) (hw : valid w A) :
        ∃ B, valid (gs.foldl appendGate w) B ∧ B.card ≤ A.card + 2 * gs.length := by
      induction gs generalizing w A with
      | nil => exact ⟨A, hw, by simp⟩
      | cons g gs ih =>
        obtain ⟨hop, hlen⟩ := hg g (by simp)
        obtain ⟨i, j, hij⟩ : ∃ i j, g.inputs = [i,j] := by
          rcases e : g.inputs with _ | ⟨i, rest⟩
          · simp [e] at hlen
          · rcases rest with _ | ⟨j, tail⟩
            · simp [e] at hlen
            · have hn : tail = [] := by simpa [e] using hlen
              exact ⟨i,j,by simp [hn]⟩
        have key (p l : Fin N) (hp : p ∈ alive (make w g)) (hl : l ∈ dark (make w g)) :
            (p ∈ alive (get w i) ∧ l ∈ dark (get w i)) ∨
            (p ∈ alive (get w j) ∧ l ∈ dark (get w j)) := by
          simp only [alive, dark, Finset.mem_filter, Finset.mem_univ, true_and] at hp hl ⊢
          rcases hop with op | op
          · simp only [make, hij, op, List.map_cons, List.map_nil, andTwo] at hp hl
            exact chooseAnd _ _ _ _ hp hl
          · simp only [make, hij, op, List.map_cons, List.map_nil, orTwo] at hp hl
            exact chooseOr _ _ _ _ hp hl
        obtain ⟨ok, B, old, added, budget⟩ := addWire _ _ _ A
          (lookup w A hw i).1 (lookup w A hw j).1 (lookup w A hw i).2 (lookup w A hw j).2 key
        have hw' : valid (appendGate w g) B := by
          intro f hf
          obtain mem | last := List.mem_append.mp hf
          · exact ⟨(hw f mem).1, (hw f mem).2.trans old⟩
          · have he : f = make w g := List.mem_singleton.mp last
            exact he ▸ ⟨ok, added⟩
        obtain ⟨K,hK,hs⟩ := ih (fun a ha => hg a (by simp [ha])) (appendGate w g) B hw'
        exact ⟨K,hK, by simp only [List.length_cons]; omega⟩
    let initial : List F := (List.finRange N).map fun i x => x i
    let finalW := D.gates.foldl appendGate initial
    have initOK : valid initial ∅ := by
      intro f hf
      obtain ⟨i, _, rfl⟩ := List.mem_map.mp hf
      exact ⟨(leaves i).1, by rw [(leaves i).2]⟩
    obtain ⟨K, finalOK, budget⟩ := accumulate D.gates
      (fun g hg => ⟨mono.1 g hg, mono.2.2 g hg⟩) initial ∅ initOK
    have bound : K.card ≤ 2 * D.size := by
      change K.card ≤ 2 * D.gates.length
      simpa only [Finset.card_empty, Nat.zero_add] using budget
    let boolStep := fun (w : List Bool) (g : Gate) => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]
    have mapRead (w : List F) (i : ℕ) (x : Fin N → Bool) :
        (w.map (fun f => f x)).getD i false = get w i x :=
      List.getD_map w zero (fun f => f x)
    have mapRun (gs : List Gate) (w : List F) (x : Fin N → Bool) :
        (gs.foldl appendGate w).map (fun f => f x) = gs.foldl boolStep (w.map fun f => f x) := by
      induction gs generalizing w with
      | nil => rfl
      | cons g rest ih =>
        change (rest.foldl appendGate (appendGate w g)).map _ = rest.foldl boolStep (boolStep _ g)
        rw [ih]
        simp only [appendGate, make, boolStep, List.map_append, List.map_cons, List.map_nil, mapRead]
    have bridge (x : Fin N → Bool) (i : ℕ) :
        (D.wires (List.ofFn x)).getD i false = get finalW i x := by
      have e : finalW.map (fun f => f x) = D.wires (List.ofFn x) := by
        have start : initial.map (fun f => f x) = List.ofFn x := by
          simp only [initial, List.map_map, Function.comp_def, List.ofFn_eq_map]
        change finalW.map (fun f => f x) = D.gates.foldl boolStep (List.ofFn x)
        rw [← start]
        exact mapRun D.gates initial x
      rw [← e]
      exact mapRead finalW i x
    let tiny := fun l : Fin N => small (alive (get finalW (roots l))) ×ˢ ({l} : Finset (Fin N))
    have tinyBudget : (labels.biUnion tiny).card ≤ labels.card := by
      have h := Finset.card_biUnion_le_card_mul labels tiny 1
        (fun l _ => by simpa [tiny, Finset.card_product] using smallCard (alive (get finalW (roots l))))
      simpa using h
    have covered : (Finset.univ.filter (fun e : Fin N × Fin N => e.2 ∈ labels ∧
        (D.wires (List.ofFn fun i => decide (i = e.1))).getD (roots e.2) false = true)) ⊆
        K ∪ labels.biUnion tiny := by
      intro e he
      obtain ⟨hl, hv⟩ := (Finset.mem_filter.mp he).2
      have hp : e.1 ∈ alive (get finalW (roots e.2)) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (bridge _ _).symm.trans hv⟩
      have hd : e.2 ∈ dark (get finalW (roots e.2)) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, (bridge _ _).symm.trans (off e.2 hl)⟩
      by_cases big : 2 ≤ (alive (get finalW (roots e.2))).card
      · apply Finset.mem_union_left
        apply (lookup finalW K finalOK (roots e.2)).2
        simpa only [heavy, ite_eq_left big, Finset.mem_product] using And.intro hp hd
      · apply Finset.mem_union_right
        apply Finset.mem_biUnion.mpr
        refine ⟨e.2, hl, Finset.mem_product.mpr ⟨?_, Finset.mem_singleton_self _⟩⟩
        have hle : (alive (get finalW (roots e.2))).card ≤ 1 := by omega
        simpa only [small, ite_eq_left hle] using hp
    exact (Finset.card_le_card covered).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add bound tinyBudget))
  let edges := Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)
  let points (l : Fin N) := Finset.univ.filter fun p => I p l
  let onLine (l : Fin N) := points l ×ˢ ({l} : Finset (Fin N))
  have edgeCount : edges.card = N * (q + 1) := by
    have byLines : edges = Finset.univ.biUnion onLine := by
      ext e
      simp [edges, onLine, points]
      constructor
      · intro h
        exact ⟨e.2,e.1,h,rfl⟩
      · rintro ⟨l,p,h,rfl⟩
        exact h
    have disj : (↑(Finset.univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint onLine := by
      intro l _ l' _ ne
      apply Finset.disjoint_left.mpr
      intro e he he'
      have a : e.2 = l := Finset.mem_singleton.mp (Finset.mem_product.mp he).2
      have b : e.2 = l' := Finset.mem_singleton.mp (Finset.mem_product.mp he').2
      exact ne (a.symm.trans b)
    rw [byLines, Finset.card_biUnion disj]
    simp [onLine, points, regular]
  have rect (p p' l l' : Fin N) (pp : p ≠ p') (ll : l ≠ l')
      (a : I p l) (b : I p l') (c : I p' l) (d : I p' l') : False :=
    ll ((uniqueLine p p' pp).unique ⟨a,c⟩ ⟨b,d⟩)
  let hit := fun (swap : Bool) (p l : Fin N) =>
    lineSingle C (N + N) (fun i => if swap then decide (i < N) else decide (N ≤ i))
      (if swap then l.val else p.val) (N + if swap then p.val else l.val)
  let single := fun (swap : Bool) =>
    Finset.univ.filter (fun e : Fin N × Fin N => hit swap e.1 e.2 = true)
  have singles (swap : Bool) : (single swap).card ≤ 8 * C.size + 2 := by
    obtain ⟨D, r, W, dAO, cost, cover, reject⟩ := extract N I C allowed computes swap
    let J := fun p l : Fin N => if swap then I l p else I p l
    have rectJ (p p' l l' : Fin N) (pp : p ≠ p') (ll : l ≠ l')
        (a : J p l) (b : J p l') (c : J p' l) (d : J p' l') : False := by
      cases swap
      · exact rect p p' l l' pp ll a b c d
      · exact rect l l' p p' ll pp a c b d
    have negTest : ∀ l ∈ W,
        (D.wires (List.ofFn fun p => decide (¬ J p l))).getD (r l) false = false := by
      intro l hl
      cases swap <;> simpa only [J, Bool.false_eq_true, ite_false, ite_true] using reject l hl
    have charge := columnCharge N J rectJ D r W dAO negTest
    have sub : single swap ⊆ Finset.univ.filter (fun e : Fin N × Fin N =>
        e.2 ∈ W ∧ (D.wires (List.ofFn fun i => decide (i = e.1))).getD (r e.2) false = true) := by
      intro e he
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, cover e.1 e.2 (Finset.mem_filter.mp he).2⟩
    have := Finset.card_le_card sub
    omega
  have disjointSides (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
    intro eq
    have h := congrArg Fin.val eq
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h
    omega
  have prime (p l : Fin N) (pl : I p l) :
      IsPrimeImplicant (N + N) C {Fin.castAdd N p, Fin.natAdd N l} := by
    constructor
    · rw [computes]
      apply decide_eq_true
      refine ⟨p,l,pl,?_,?_⟩
      · change decide (Fin.castAdd N p ∈ ({Fin.castAdd N p, Fin.natAdd N l} : Finset _)) = true
        simp
      · change decide (Fin.natAdd N l ∈ ({Fin.castAdd N p, Fin.natAdd N l} : Finset _)) = true
        simp
    · intro T hT
      rw [computes]
      apply decide_eq_false
      rintro ⟨u,v,_,hu,hv⟩
      have proper := Finset.mem_ssubsets.mp hT
      have uT : Fin.castAdd N u ∈ T := of_decide_eq_true hu
      have vT : Fin.natAdd N v ∈ T := of_decide_eq_true hv
      have ueq : Fin.castAdd N u = Fin.castAdd N p := by
        obtain e | e := Finset.mem_insert.mp (proper.1 uT)
        · exact e
        · exact False.elim (disjointSides u l (Finset.mem_singleton.mp e))
      have veq : Fin.natAdd N v = Fin.natAdd N l := by
        obtain e | e := Finset.mem_insert.mp (proper.1 vT)
        · exact False.elim (disjointSides p v e.symm)
        · exact Finset.mem_singleton.mp e
      apply proper.2
      intro i hi
      obtain e | e := Finset.mem_insert.mp hi
      · simpa only [e, ← ueq] using uT
      · simpa only [Finset.mem_singleton.mp e, ← veq] using vT
  let double := Finset.univ.filter (fun e : Fin N × Fin N =>
    I e.1 e.2 ∧ readsAtMost C (N + N) (setList {Fin.castAdd N e.1, Fin.natAdd N e.2}) 2 = true ∧
    hit false e.1 e.2 = false ∧ hit true e.2 e.1 = false)
  have residual : double.card ≤ 84 * C.size := by
    apply residualBound q N I C hq order (fun l =>
      ⟨points l, regular l, fun p => by simp [points]⟩) uniqueLine allowed computes double
    intro e he
    exact (Finset.mem_filter.mp he).2
  let other := (single true).image Prod.swap
  have cover : edges ⊆ (single false ∪ other) ∪ double := by
    intro e he
    have incidence := (Finset.mem_filter.mp he).2
    by_cases h : hit false e.1 e.2 = true
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩))
    by_cases k : hit true e.2 e.1 = true
    · have mem : e.swap ∈ single true := Finset.mem_filter.mpr ⟨Finset.mem_univ _, k⟩
      exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e.swap,mem,by simp⟩))
    apply Finset.mem_union_right
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, incidence, readTwo _ (prime e.1 e.2 incidence),
      Bool.eq_false_iff.mpr h, Bool.eq_false_iff.mpr k⟩
  have h₁ := Finset.card_le_card cover
  have h₂ := Finset.card_union_le (single false ∪ other) double
  have h₃ := Finset.card_union_le (single false) other
  have h₄ : other.card ≤ (single true).card := Finset.card_image_le
  have h₅ := singles false
  have h₆ := singles true
  have four : 4 ≤ N := by rw [order]; nlinarith
  rw [edgeCount, Nat.mul_add, Nat.mul_one] at h₁
  omega
