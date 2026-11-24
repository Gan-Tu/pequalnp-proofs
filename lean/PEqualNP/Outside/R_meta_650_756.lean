import Mathlib
import PEqualNP.Defs

-- The coordinates and monotonicity argument are adapted from Steve Digital's previous reduction.
-- Each certificate node is a rectangle of incident inputs and maximal false inputs.
-- Earlier nodes may cover a rectangle without fixing the values on any other input.
set_option maxRecDepth 32768 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_650_756
    (certificate : let near := fun p l : Fin 13 => (p.val+l.val)%13 ∈ ([0,1,3,9] : List ℕ)
      let off := fun (t : Finset (Fin 13)) => Finset.univ.filter fun p : Fin 13 => ∀ l ∈ t, ¬ near l p
      ∃ s ≤ 63, ∃ R : ℕ → Set ((Fin 13 × Fin 13) × Finset (Fin 13)),
        (∀ i : Fin 26, ∀ z ∈ R i.val,
          Fin.ofNat 13 i.val = (if i.val<13 then z.1.1 else z.1.2) ∧
          Fin.ofNat 13 i.val ∉ (if i.val<13 then off z.2 else z.2)) ∧
        (∀ j < s,
        (∀ x ∈ R (26+j), ∀ y ∈ R (26+j), (x.1,y.2) ∈ R (26+j)) ∧
        ∃ a < 26+j, ∃ b < 26+j, R (26+j) ⊆ R a ∪ R b) ∧
        ∃ o < 26+s, ∀ p l, near p l → ∀ t, off (off t) = t → ((p,l),t) ∈ R o)
    (synthesize : ∀ (n s : ℕ) (α β : Type)
      (P : α → Fin n → Bool) (B : β → Fin n → Bool) (R : ℕ → Set (α × β)),
      (∀ i : Fin n, ∀ z ∈ R i.val, P z.1 i = true ∧ B z.2 i = false) →
      (∀ j < s,
        (∀ x ∈ R (n+j), ∀ y ∈ R (n+j), (x.1,y.2) ∈ R (n+j)) ∧
        ∃ a < n+j, ∃ b < n+j, R (n+j) ⊆ R a ∪ R b) →
      ∀ o < n+s, ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ z ∈ R o,
        C.eval (List.ofFn (P z.1)) = true ∧ C.eval (List.ofFn (B z.2)) = false) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 63 ∧ (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  obtain ⟨s,hs,R,raw,joins,o,valid,full⟩ := certificate
  let near := fun p l : Fin 13 => (p.val + l.val) % 13 ∈ ([0,1,3,9] : List ℕ)
  let vec := fun (s t : Finset (Fin 13)) (i : Fin 26) => if i.val < 13 then decide ((Fin.ofNat 13 i.val) ∈ s) else decide ((Fin.ofNat 13 i.val) ∈ t)
  let off := fun (s : Finset (Fin 13)) => Finset.univ.filter fun j : Fin 13 => ∀ i ∈ s, ¬ near i j
  let P := fun e : Fin 13 × Fin 13 => vec {e.1} {e.2}
  let B := fun t : Finset (Fin 13) => vec (off t) t
  have initial : ∀ i : Fin 26, ∀ z ∈ R i.val, P z.1 i=true ∧ B z.2 i=false := by
    intro i z member
    have h := raw i z member
    change Fin.ofNat 13 i.val = (if i.val<13 then z.1.1 else z.1.2) ∧
      Fin.ofNat 13 i.val ∉ (if i.val<13 then off z.2 else z.2) at h
    by_cases side : i.val<13 <;> simpa [P,B,vec,side] using h
  obtain ⟨C,hm,sz,tableRead⟩ := synthesize 26 s (Fin 13 × Fin 13) (Finset (Fin 13)) P B R initial joins o valid
  let read := fun s t => C.eval (List.ofFn (vec s t))
  have reverse {S T : Finset (Fin 13)} (sub : S ⊆ T) : off T ⊆ off S := by
    intro p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun i hi => (Finset.mem_filter.mp hp).2 i (sub hi)⟩
  have expand (T : Finset (Fin 13)) : T ⊆ off (off T) := by
    intro p hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    intro l hl
    simpa only [near,Nat.add_comm l.val p.val] using (Finset.mem_filter.mp hl).2 p hp
  have triple (T : Finset (Fin 13)) : off (off (off T)) = off T :=
    Finset.Subset.antisymm (reverse (expand T)) (expand (off T))
  have on (p l : Fin 13) (hit : near p l) : read {p} {l} = true := by
    exact (tableRead ((p,l),off ∅) (full p l hit (off ∅) (triple ∅))).1
  have reject (t : Finset (Fin 13)) (closed : off (off t)=t) : read (off t) t=false := by
    have hit : near 0 0 := by decide +kernel
    exact (tableRead ((0,0),t) (full 0 0 hit t closed)).2
  let step (w : List Bool) (g : PEqualNP.CircuitLowerBounds.Gate) :=
    w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  let Le := fun (w z : List Bool) => ∀ i : ℕ, w.getD i false = true → z.getD i false = true
  have extend (gs : List PEqualNP.CircuitLowerBounds.Gate)
      (ok : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) (w z : List Bool)
      (len : w.length = z.length) (le : Le w z) :
      Le (gs.foldl step w) (gs.foldl step z) := by
    induction gs generalizing w z with
    | nil => exact le
    | cons g gs ih =>
      apply ih (fun k hk => ok k (by simp [hk])) (step w g) (step z g) (by simp [step,len])
      have gate : g.op.eval (g.inputs.map fun i => w.getD i false) = true →
          g.op.eval (g.inputs.map fun i => z.getD i false) = true := by
        rcases ok g (by simp) with hop | hop
        · rw [hop]
          change (g.inputs.map fun i => w.getD i false).all id = true → (g.inputs.map fun i => z.getD i false).all id = true
          simp only [List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
          intro h i hi
          exact le i (h i hi)
        · rw [hop]
          change (g.inputs.map fun i => w.getD i false).any id = true → (g.inputs.map fun i => z.getD i false).any id = true
          simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
          rintro ⟨i,hi,ha⟩
          exact ⟨i,hi,le i ha⟩
      intro i
      by_cases small : i < w.length
      · simpa only [step,List.getD_append _ _ _ _ small,List.getD_append _ _ _ _ (len ▸ small)] using le i
      · have big : w.length ≤ i := by omega
        simp only [step,List.getD_append_right _ _ _ _ big,List.getD_append_right _ _ _ _ (len ▸ big), ← len]
        cases e : i-w.length with
        | zero => exact gate
        | succ j => simp
  have mono {s t u v : Finset (Fin 13)} (a : s ⊆ u) (b : t ⊆ v) :
      read s t = true → read u v = true := by
    have init : Le (List.ofFn (vec s t)) (List.ofFn (vec u v)) := by
      intro j
      by_cases hj : j < 26
      · rw [List.getD_eq_getElem (List.ofFn (vec s t)) false (by simpa only [List.length_ofFn] using hj),
            List.getD_eq_getElem (List.ofFn (vec u v)) false (by simpa only [List.length_ofFn] using hj)]
        simp only [List.getElem_ofFn]
        by_cases hp : j < 13
        · simpa [vec,hp] using a (x := Fin.ofNat 13 j)
        · simpa [vec,hp] using b (x := Fin.ofNat 13 j)
      · rw [List.getD_eq_default (List.ofFn (vec s t)) false (by simp only [List.length_ofFn]; omega)]
        intro h
        exact Bool.noConfusion h
    exact extend C.gates (fun g hg => (hm g hg).1) _ _ (by simp) init C.output
  let pt (p : Fin 13) : Fin 26 := ⟨p.val,by omega⟩
  let ln (l : Fin 13) : Fin 26 := ⟨13+l.val,by omega⟩
  let edges : List (ℕ × ℕ) := [(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)]
  have table : ∀ u v : Fin 26, (u.val,v.val) ∈ edges ↔
      u.val < 13 ∧ 13 ≤ v.val ∧ near (Fin.ofNat 13 u.val) (Fin.ofNat 13 v.val) := by
    dsimp only [edges,near]
    decide +kernel
  have points : ∀ p : Fin 13, (Fin.ofNat 13 (pt p).val) = p := by
    intro p
    apply Fin.ext
    change p.val % 13 = p.val
    exact Nat.mod_eq_of_lt p.isLt
  have lines : ∀ l : Fin 13, (Fin.ofNat 13 (ln l).val) = l := by
    intro l
    apply Fin.ext
    change (13+l.val) % 13 = l.val
    omega
  have pointInv : ∀ i : Fin 26, i.val < 13 → pt (Fin.ofNat 13 i.val) = i := by
    intro i hi
    apply Fin.ext
    exact Nat.mod_eq_of_lt hi
  have lineInv : ∀ i : Fin 26, 13 ≤ i.val → ln (Fin.ofNat 13 i.val) = i := by
    intro i hi
    apply Fin.ext
    change 13+i.val % 13 = i.val
    omega
  refine ⟨C,hm,sz.trans hs,?_⟩
  intro x
  let s := Finset.univ.filter fun p : Fin 13 => x (pt p) = true
  let t := Finset.univ.filter fun l : Fin 13 => x (ln l) = true
  have repr : vec s t = x := by
    funext i
    by_cases hi : i.val < 13
    · simp only [vec,ite_eq_left hi,s,Finset.mem_filter,Finset.mem_univ,true_and,pointInv i hi]
      simp
    · simp only [vec,ite_eq_right hi,t,Finset.mem_filter,Finset.mem_univ,true_and,lineInv i (by omega)]
      simp
  change C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val,v.val) ∈ edges ∧ x u = true ∧ x v = true
  have arr : (∃ u v : Fin 26, (u.val,v.val) ∈ edges ∧ x u = true ∧ x v = true) ↔
      ∃ p ∈ s, ∃ l ∈ t, near p l := by
    constructor
    · rintro ⟨u,v,he,hu,hv⟩
      obtain ⟨ha,hb,hc⟩ := (table u v).mp he
      exact ⟨Fin.ofNat 13 u.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [pointInv u ha]; exact hu⟩,Fin.ofNat 13 v.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [lineInv v hb]; exact hv⟩,hc⟩
    · rintro ⟨p,hp,l,hl,hpl⟩
      refine ⟨pt p,ln l,(table _ _).mpr ⟨by dsimp [pt]; omega,by dsimp [ln]; omega,?_⟩,?_,?_⟩
      · simpa only [points,lines] using hpl
      · simpa [s] using hp
      · simpa [t] using hl
  rw [arr,← repr]
  change read s t = true ↔ _
  constructor
  · intro accepted
    by_contra no
    have sub : t ⊆ off s := by
      intro l hl
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun p hp e => no ⟨p,hp,l,hl,e⟩⟩
    have bad := mono (expand s) sub accepted
    rw [reject (off s) (triple s)] at bad
    exact Bool.noConfusion bad
  · rintro ⟨p,hp,l,hl,hpl⟩
    exact mono (Finset.singleton_subset_iff.mpr hp) (Finset.singleton_subset_iff.mpr hl) (on p l hpl)
