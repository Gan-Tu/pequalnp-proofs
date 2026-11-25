import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5897

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def graph (u v : Fin 4) := (13823 : Nat).testBit (4 * u.val + v.val)

-- The first two rows and the first column are full. The last two rows each contribute one further entry.
def witness : Circuit := ⟨[
  ⟨.or, [0, 1]⟩,
  ⟨.or, [8, 4]⟩,
  ⟨.and, [2, 6]⟩,
  ⟨.and, [3, 5]⟩,
  ⟨.or, [10, 11]⟩,
  ⟨.or, [9, 12]⟩], 13⟩

lemma upper : RepSizeAtMost graph 6 := by
  refine ⟨witness, ?_, by decide, ?_⟩
  · intro g hg
    simp only [witness, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  · exact (by decide +kernel : Represents graph witness)

def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

def ordered (S : Finset Nat) (x y : List Bool) : Prop :=
  ∀ i ∈ S, x.getD i false = true → y.getD i false = true

lemma oldValue (w : List Bool) (g : Gate) (n i : Nat) (len : w.length = n) (ne : i ≠ n) :
    (step w g).getD i false = w.getD i false := by
  rcases lt_or_gt_of_ne ne with lt | gt
  · exact List.getD_append _ _ _ _ (by omega)
  · rw [List.getD_eq_default _ _ (show (step w g).length ≤ i by simp [step,len]; omega),
      List.getD_eq_default _ _ (show w.length ≤ i by omega)]

lemma newValue (w : List Bool) (g : Gate) (n : Nat) (len : w.length = n) :
    (step w g).getD n false = g.op.eval (g.inputs.map (fun i => w.getD i false)) := by
  unfold step
  rw [List.getD_append_right _ _ _ _ (show w.length ≤ n by omega),len,Nat.sub_self,List.getD_cons_zero]

lemma monotoneGate (g : Gate) (op : g.op = .and ∨ g.op = .or)
    (x y : List Bool) (h : ordered g.inputs.toFinset x y) :
    g.op.eval (g.inputs.map fun i => x.getD i false) = true →
      g.op.eval (g.inputs.map fun i => y.getD i false) = true := by
  rcases op with op | op <;> rw [op]
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    exact fun all i hi => h i (List.mem_toFinset.mpr hi) (all i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i,hi,on⟩
    exact ⟨i,hi,h i (List.mem_toFinset.mpr hi) on⟩

-- Replacing a used gate by its two inputs adds at most one wire to the set.
lemma beforeGate (n : Nat) (g : Gate) (op : g.op = .and ∨ g.op = .or) (arity : g.inputs.length ≤ 2)
    (S : Finset Nat) : ∃ T : Finset Nat, T.card ≤ S.card + 1 ∧
    ∀ x y : List Bool, x.length=n → y.length=n → ordered T x y → ordered S (step x g) (step y g) := by
  by_cases used : n ∈ S
  · refine ⟨S.erase n ∪ g.inputs.toFinset, ?_, ?_⟩
    · have a := Finset.card_union_le (S.erase n) g.inputs.toFinset
      have b := Finset.card_erase_add_one used
      have c := List.toFinset_card_le g.inputs
      omega
    · intro x y hx hy h i hi on
      by_cases new : i=n
      · subst i
        rw [newValue x g n hx] at on
        rw [newValue y g n hy]
        exact monotoneGate g op x y (fun j hj => h j (Finset.mem_union_right _ hj)) on
      · rw [oldValue x g n i hx new] at on
        rw [oldValue y g n i hy new]
        exact h i (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨new,hi⟩)) on
  · refine ⟨S, by omega, ?_⟩
    intro x y hx hy h i hi on
    have ne : i≠n := fun e => used (e ▸ hi)
    rw [oldValue x g n i hx ne] at on
    rw [oldValue y g n i hy ne]
    exact h i hi on

theorem basis (gs : List Gate) (ok : ∀g∈gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
    ∀ (n : Nat) (S : Finset Nat), ∃ T : Finset Nat, T.card ≤ S.card + gs.length ∧
      ∀ x y : List Bool, x.length=n → y.length=n → ordered T x y →
        ordered S (gs.foldl step x) (gs.foldl step y) := by
  induction gs with
  | nil => intro n S; exact ⟨S,by simp,fun x y _ _ h => h⟩
  | cons g gs ih =>
    intro n S
    obtain ⟨U,b,rest⟩ := ih (fun z hz => ok z (List.mem_cons_of_mem _ hz)) (n+1) S
    obtain ⟨op,arity⟩ := ok g List.mem_cons_self
    obtain ⟨T,a,first⟩ := beforeGate n g op arity U
    refine ⟨T,by simp only [List.length_cons]; omega,?_⟩
    intro x y hx hy h
    exact rest (step x g) (step y g) (by simp [step,hx]) (by simp [step,hy]) (first x y hx hy h)

-- In test pair i, exactly input wire i changes from true to false.
def accepted : Fin 7 → Fin 4 × Fin 4 := ![(0,1),(1,1),(2,2),(3,1),(2,0),(3,1),(2,2)]
def rejected : Fin 7 → Fin 4 × Fin 4 := ![(2,1),(2,1),(3,2),(2,1),(2,1),(3,2),(2,1)]
def row (e : Fin 4 × Fin 4) := oneEach e.1 e.2

lemma testData : ∀ i : Fin 7, graph (accepted i).1 (accepted i).2=true ∧
    graph (rejected i).1 (rejected i).2=false ∧
    ∀ j : Fin 8, (row (accepted i)).getD j.val false=true →
      (row (rejected i)).getD j.val false=false → j.val=i.val := by
  decide +kernel

lemma rowLength (e : Fin 4 × Fin 4) : (row e).length=8 := by simp [row,oneEach]

lemma lower : ¬ RepSizeAtMost graph 5 := by
  rintro ⟨C,legal,size,rep⟩
  have ops : ∀g∈C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    obtain ⟨op,arity⟩ := legal g hg
    exact ⟨by simpa using op,arity⟩
  obtain ⟨T,cap,depend⟩ := basis C.gates ops 8 {C.output}
  have required (i : Fin 7) : i.val ∈ T := by
    by_contra absent
    obtain ⟨pos,neg,unique⟩ := testData i
    have h : ordered T (row (accepted i)) (row (rejected i)) := by
      intro j member on
      by_cases small : j<8
      · cases off : (row (rejected i)).getD j false with
        | true => rfl
        | false => exact (absent ((unique ⟨j,small⟩ on off) ▸ member)).elim
      · rw [List.getD_eq_default _ _ (by rw [rowLength]; omega)] at on
        contradiction
    have pass := depend _ _ (rowLength _) (rowLength _) h C.output (Finset.mem_singleton_self _)
    have yes : C.eval (row (accepted i))=true := (rep _ _).trans pos
    have no : C.eval (row (rejected i))=false := (rep _ _).trans neg
    exact Bool.noConfusion ((pass yes).symm.trans no)
  let key (i : Fin 7) : {j // j ∈ T} := ⟨i.val,required i⟩
  have inj : Function.Injective key := fun a b h => Fin.ext (congrArg Subtype.val h)
  have many := Fintype.card_le_of_injective key inj
  simp only [Fintype.card_fin,Fintype.card_coe] at many
  simp only [Finset.card_singleton] at cap
  change C.gates.length ≤ 5 at size
  omega

end PEqualNP.Outside.L_meta_5897

theorem PEqualNP.Outside.L_meta_5897 :
    PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (13823 : ℕ).testBit (4 * u.val + v.val)) 6 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (13823 : ℕ).testBit (4 * u.val + v.val)) 5 :=
  ⟨PEqualNP.Outside.L_meta_5897.upper, PEqualNP.Outside.L_meta_5897.lower⟩
