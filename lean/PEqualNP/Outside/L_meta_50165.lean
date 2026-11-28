import Mathlib.Data.List.GetD
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Pi
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_50165
open PEqualNP.CircuitLowerBounds

abbrev W := BitVec 6
def bit (t : Fin 6) (w : W) := w.getLsbD t.val
def wire (ws : List W) (i : ℕ) := ws.getD i 0
def gen (ws : List W) (g : Gate) : W :=
  let a := wire ws (g.inputs.headD ws.length)
  let b := wire ws ((g.inputs.drop 1).headD ws.length)
  match g.op,g.inputs with
  | .and,[] => ~~~0
  | .and,[_] => a
  | .and,_ => a &&& b
  | .or,[] => 0
  | .or,[_] => a
  | .or,_ => a ||| b
  | .not,[] => ~~~0
  | .not,_ => ~~~a
  | _,_ => 0

def valid (g : Gate) : Prop := (g.op=.and ∨ g.op=.or ∨ g.op=.not) ∧ g.inputs.length≤2
def push (ws : List W) (g : Gate) := ws++[gen ws g]
def boolPush (ws : List Bool) (g : Gate) := ws++[g.op.eval (g.inputs.map fun i => ws.getD i false)]
theorem bit_wire (ws : List W) (t : Fin 6) (i : ℕ) :
  bit t (wire ws i)=(ws.map (bit t)).getD i false := by
  simpa [wire,bit] using (List.getD_map ws (0 : W) (n:=i) (bit t)).symm

theorem gen_sound (ws : List W) (t : Fin 6) (g : Gate) (h : valid g) :
    bit t (gen ws g)=g.op.eval (g.inputs.map (fun i => (ws.map (bit t)).getD i false)) := by
  obtain ⟨op,ins⟩ := g
  obtain ⟨ops,sz⟩ := h
  change op=.and ∨ op=.or ∨ op=.not at ops
  change ins.length≤2 at sz
  have casesList : ins=[] ∨ (∃ a, ins=[a]) ∨ ∃ a b, ins=[a,b] := by
    cases ins with
    | nil => simp
    | cons a tail =>
      cases tail with
      | nil => exact Or.inr (Or.inl ⟨a,rfl⟩)
      | cons b rem =>
        cases rem with
        | nil => exact Or.inr (Or.inr ⟨a,b,rfl⟩)
        | cons c rem => simp at sz
  have rd (i : ℕ) : (ws.map (bit t)).getD i false = (wire ws i).getLsbD t.val := (bit_wire ws t i).symm
  have rd2 (i : ℕ) : (Option.map (bit t) ws[i]?).getD false = (wire ws i).getLsbD t.val := by
    simpa only [List.getD_eq_getElem?_getD,List.getElem?_map] using rd i
  have ones : (63#6).getLsbD t.val = true := (show ∀ z : Fin 6, (63#6).getLsbD z.val = true from by decide +kernel) t
  rcases casesList with rfl|⟨a,rfl⟩|⟨a,b,rfl⟩ <;> rcases ops with rfl|rfl|rfl <;>
    simp [gen,GateOp.eval,bit,rd2,ones,t.isLt]

theorem run_sound (gs : List Gate) (ws : List W) (t : Fin 6) (hg : ∀ g∈gs, valid g) :
    (gs.foldl push ws).map (bit t)=gs.foldl boolPush (ws.map (bit t)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g tail ih =>
    simp only [List.foldl_cons]
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    congr 1
    simp [push,boolPush,gen_sound ws t g (hg g (by simp))]

def next (s : List W) : List W :=
  (s.map (fun a => ~~~a))++(s.flatMap fun a => s.flatMap fun b => [a &&& b,a ||| b])
def win (goal : List W) : ℕ → List W → Bool
  | 0,s => goal.all (fun x => s.contains x)
  | k+1,s => decide ((goal.toFinset \ s.toFinset).card ≤ k+1) &&
    (win goal k s || (next s).eraseDups.any (fun x => !(s.contains x) && win goal k (x::s)))

theorem gen_member (ws s : List W) (g : Gate) (h : valid g) (incl : ∀ w∈ws, w∈s)
    (z : (0:W)∈s) (o : (~~~(0:W))∈s) : gen ws g ∈ s ∨ gen ws g ∈ next s := by
  have read (i : ℕ) : wire ws i ∈ s := by
    by_cases hi : i<ws.length
    · rw [wire,List.getD_eq_getElem _ _ hi];exact incl _ (List.getElem_mem hi)
    · rw [wire,List.getD_eq_default _ _ (by omega)];exact z
  have nn (a : W) (ha : a∈s) : ~~~a ∈ next s :=
    List.mem_append_left _ (List.mem_map.mpr ⟨a,ha,rfl⟩)
  have ab (a b c : W) (ha : a∈s) (hb : b∈s) (hc : c∈[a &&& b,a ||| b]) : c∈next s :=
    List.mem_append_right _ (List.mem_flatMap.mpr ⟨a,ha,List.mem_flatMap.mpr ⟨b,hb,hc⟩⟩)
  obtain ⟨op,ins⟩ := g
  obtain ⟨ops,sz⟩ := h
  change op=.and ∨ op=.or ∨ op=.not at ops
  rcases ops with rfl|rfl|rfl
  · cases ins with
    | nil => exact Or.inl o
    | cons a l => cases l with
      | nil => exact Or.inl (read a)
      | cons b l => exact Or.inr (ab _ _ _ (read a) (read b) List.mem_cons_self)
  · cases ins with
    | nil => exact Or.inl z
    | cons a l => cases l with
      | nil => exact Or.inl (read a)
      | cons b l => exact Or.inr (ab _ _ _ (read a) (read b) (List.mem_cons_of_mem _ List.mem_cons_self))
  · cases ins with
    | nil => exact Or.inl o
    | cons a l => exact Or.inr (nn _ (read a))

theorem extends_by (gs : List Gate) (ws : List W) :
    ∃ suffix : List W, gs.foldl push ws=ws++suffix ∧ suffix.length=gs.length := by
  induction gs generalizing ws with
  | nil => exact ⟨[],by simp, rfl⟩
  | cons g rest ih =>
    obtain ⟨t,eq,sz⟩ := ih (push ws g)
    exact ⟨gen ws g::t,by simpa [push,List.append_assoc] using eq,by simp [sz]⟩
theorem missing_le (gs : List Gate) (ws s goal : List W) (incl : ∀ x∈ws,x∈s)
    (h : ∀ x∈goal,x∈gs.foldl push ws) : (goal.toFinset \ s.toFinset).card ≤ gs.length := by
  obtain ⟨t,eq,sz⟩ := extends_by gs ws
  have sub : (goal.toFinset \ s.toFinset) ⊆ t.toFinset := by
    intro a ha
    obtain ⟨hg,hs⟩ := Finset.mem_sdiff.mp ha
    have member := h a (List.mem_toFinset.mp hg)
    rw [eq] at member
    exact List.mem_toFinset.mpr ((List.mem_append.mp member).resolve_left
      (fun old => hs (List.mem_toFinset.mpr (incl a old))))
  exact (Finset.card_le_card sub).trans (sz ▸ List.toFinset_card_le t)

theorem sound (gs : List Gate) (k : ℕ) (ws s goal : List W) (length : gs.length≤k)
    (hg : ∀g∈gs, valid g) (incl : ∀ w∈ws, w∈s) (z : (0:W)∈s) (o : (~~~(0:W))∈s)
    (witness : ∀ w∈goal, w∈gs.foldl push ws) : win goal k s=true := by
  induction k generalizing gs ws s with
  | zero =>
    have h : gs=[] := List.length_eq_zero_iff.mp (by omega)
    subst gs; exact List.all_eq_true.mpr (fun a ha => List.contains_iff_mem.mpr (incl a (witness a ha)))
  | succ k ih =>
    apply Bool.and_eq_true_iff.mpr
    refine ⟨decide_eq_true ((missing_le gs ws s goal incl witness).trans length),?_⟩
    cases gs with
    | nil =>
      apply Bool.or_eq_true_iff.mpr;left
      exact ih [] ws s (by simp) hg incl z o witness
    | cons g tail =>
      let v := gen ws g
      have sz : tail.length≤k := by simp at length;omega
      have htail : ∀ g∈tail,valid g := fun a ha => hg a (by simp [ha])
      have hgo : ∀ w∈goal,w∈tail.foldl push (push ws g) := witness
      apply Bool.or_eq_true_iff.mpr
      by_cases mem : v ∈ s
      · left;apply ih tail (push ws g) s sz htail _ z o hgo
        intro a ha
        rcases List.mem_append.mp ha with old|new
        · exact incl a old
        · rw [List.mem_singleton.mp new]; exact mem
      · right
        have nx : v ∈ next s := (gen_member ws s g (hg g (by simp)) incl z o).resolve_left mem
        apply List.any_eq_true.mpr
        refine ⟨v,List.mem_eraseDups.mpr nx,Bool.and_eq_true_iff.mpr ⟨by simpa using mem,?_⟩⟩
        apply ih tail (push ws g) (v::s) sz htail _ (List.mem_cons_of_mem _ z) (List.mem_cons_of_mem _ o) hgo
        intro a ha
        rcases List.mem_append.mp ha with old|new
        · exact List.mem_cons_of_mem _ (incl _ old)
        · exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp new))
theorem run_length (gs : List Gate) (ws : List W) : (gs.foldl push ws).length=ws.length+gs.length := by
  induction gs generalizing ws with
  | nil => simp
  | cons g tail ih =>
    rw [List.foldl_cons,ih]
    simp [push];omega

def inputs : List W := [62,60,56,48,32,0,63]
def row (t : Fin 6) := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
theorem initial : ∀ t : Fin 6, inputs.map (bit t)=row t := by decide +kernel

theorem present (D : Circuit) (legal : ∀g∈D.gates, valid g) (p : Fin (7+D.size)) (v : W)
    (h : ∀ t : Fin 6, (D.wires (row t)).getD p.val false = bit t v) :
    v ∈ D.gates.foldl push inputs := by
  let ws := D.gates.foldl push inputs
  have eq : wire ws p.val = v := by
    apply BitVec.eq_of_getLsbD_eq
    intro k hk
    let t : Fin 6 := ⟨k,hk⟩
    change bit t (wire ws p.val) = bit t v
    rw [bit_wire]
    change ((D.gates.foldl push inputs).map (bit t)).getD p.val false=_
    rw [run_sound D.gates inputs t legal,initial]
    exact h t
  rw [← eq,wire]
  have len : ws.length=7+D.size := by exact (run_length D.gates inputs)
  rw [List.getD_eq_getElem _ _ (by rw [len];exact p.isLt)]
  exact List.getElem_mem _

theorem reject_step (goal s add : List W) (k : ℕ)
    (skip : win goal k s=false)
    (covered : (next s).all (fun v => s.contains v || add.contains v)=true)
    (children : ∀ v∈add, win goal k (v::s)=false) : win goal (k+1) s=false := by
  cases h : win goal (k+1) s with
  | false => rfl
  | true =>
    have step := (Bool.and_eq_true_iff.mp h).2
    rcases Bool.or_eq_true_iff.mp step with old|fresh
    · rw [skip] at old; contradiction
    · obtain ⟨v,hm,run⟩:=List.any_eq_true.mp fresh
      obtain ⟨novel,hit⟩:=Bool.and_eq_true_iff.mp run
      have opts := List.all_eq_true.mp covered v (List.mem_eraseDups.mp hm)
      rcases Bool.or_eq_true_iff.mp opts with already|inAdd
      · rw [already] at novel; contradiction
      · rw [children v (List.contains_iff_mem.mp inAdd)] at hit; contradiction

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch2 : win [17,25,28] 4 [62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch3 : win [17,25,28] 4 [1,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch4 : win [17,25,28] 4 [3,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch5 : win [17,25,28] 4 [7,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch6 : win [17,25,28] 4 [15,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch7 : win [17,25,28] 4 [31,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch1 : win [17,25,28] 5 [62,60,56,48,32,0,63] = false := by
  apply reject_step [17,25,28] [62,60,56,48,32,0,63] [1,3,7,15,31] 4 branch2 (by decide +kernel)
  intro v h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact branch3
  · exact branch4
  · exact branch5
  · exact branch6
  · exact branch7

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch9 : win [17,25,28] 4 [3,1,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch10 : win [17,25,28] 4 [7,1,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch11 : win [17,25,28] 4 [15,1,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch12 : win [17,25,28] 4 [31,1,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch13 : win [17,25,28] 4 [33,1,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch14 : win [17,25,28] 4 [49,1,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch15 : win [17,25,28] 4 [57,1,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch16 : win [17,25,28] 4 [61,1,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch8 : win [17,25,28] 5 [1,62,60,56,48,32,0,63] = false := by
  apply reject_step [17,25,28] [1,62,60,56,48,32,0,63] [3,7,15,31,33,49,57,61] 4 branch3 (by decide +kernel)
  intro v h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact branch9
  · exact branch10
  · exact branch11
  · exact branch12
  · exact branch13
  · exact branch14
  · exact branch15
  · exact branch16

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch18 : win [17,25,28] 4 [1,3,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch19 : win [17,25,28] 4 [2,3,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch20 : win [17,25,28] 4 [7,3,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch21 : win [17,25,28] 4 [15,3,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch22 : win [17,25,28] 4 [31,3,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch23 : win [17,25,28] 4 [35,3,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch24 : win [17,25,28] 4 [51,3,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch25 : win [17,25,28] 4 [59,3,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch17 : win [17,25,28] 5 [3,62,60,56,48,32,0,63] = false := by
  apply reject_step [17,25,28] [3,62,60,56,48,32,0,63] [1,2,7,15,31,35,51,59] 4 branch4 (by decide +kernel)
  intro v h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact branch18
  · exact branch19
  · exact branch20
  · exact branch21
  · exact branch22
  · exact branch23
  · exact branch24
  · exact branch25

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch27 : win [17,25,28] 4 [1,7,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch28 : win [17,25,28] 4 [3,7,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch29 : win [17,25,28] 4 [4,7,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch30 : win [17,25,28] 4 [6,7,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch31 : win [17,25,28] 4 [15,7,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch32 : win [17,25,28] 4 [31,7,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch33 : win [17,25,28] 4 [39,7,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch34 : win [17,25,28] 4 [55,7,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch26 : win [17,25,28] 5 [7,62,60,56,48,32,0,63] = false := by
  apply reject_step [17,25,28] [7,62,60,56,48,32,0,63] [1,3,4,6,15,31,39,55] 4 branch5 (by decide +kernel)
  intro v h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact branch27
  · exact branch28
  · exact branch29
  · exact branch30
  · exact branch31
  · exact branch32
  · exact branch33
  · exact branch34

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch36 : win [17,25,28] 4 [1,15,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch37 : win [17,25,28] 4 [3,15,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch38 : win [17,25,28] 4 [7,15,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch39 : win [17,25,28] 4 [8,15,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch40 : win [17,25,28] 4 [12,15,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch41 : win [17,25,28] 4 [14,15,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch42 : win [17,25,28] 4 [31,15,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch43 : win [17,25,28] 4 [47,15,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch35 : win [17,25,28] 5 [15,62,60,56,48,32,0,63] = false := by
  apply reject_step [17,25,28] [15,62,60,56,48,32,0,63] [1,3,7,8,12,14,31,47] 4 branch6 (by decide +kernel)
  intro v h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact branch36
  · exact branch37
  · exact branch38
  · exact branch39
  · exact branch40
  · exact branch41
  · exact branch42
  · exact branch43

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch45 : win [17,25,28] 4 [1,31,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch46 : win [17,25,28] 4 [3,31,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch47 : win [17,25,28] 4 [7,31,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch48 : win [17,25,28] 4 [15,31,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch49 : win [17,25,28] 4 [16,31,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch50 : win [17,25,28] 4 [24,31,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch51 : win [17,25,28] 4 [28,31,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch52 : win [17,25,28] 4 [30,31,62,60,56,48,32,0,63] = false := by
  decide +kernel

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch44 : win [17,25,28] 5 [31,62,60,56,48,32,0,63] = false := by
  apply reject_step [17,25,28] [31,62,60,56,48,32,0,63] [1,3,7,15,16,24,28,30] 4 branch7 (by decide +kernel)
  intro v h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact branch45
  · exact branch46
  · exact branch47
  · exact branch48
  · exact branch49
  · exact branch50
  · exact branch51
  · exact branch52

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
private theorem branch0 : win [17,25,28] 6 [62,60,56,48,32,0,63] = false := by
  apply reject_step [17,25,28] [62,60,56,48,32,0,63] [1,3,7,15,31] 5 branch1 (by decide +kernel)
  intro v h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact branch8
  · exact branch17
  · exact branch26
  · exact branch35
  · exact branch44

theorem excluded : win [17,25,28] 6 inputs=false := branch0

end PEqualNP.Outside.L_meta_50165

open PEqualNP.Outside.L_meta_50165 in
theorem PEqualNP.Outside.L_meta_50165 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (7+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 7 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 6 ∧
  ∀ t : Fin 6,
    let xs := (List.ofFn (fun i : Fin 5 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (17 : Nat).testBit t.val ∧
    w.getD q.val false = (25 : Nat).testBit t.val ∧
    w.getD r.val false = (28 : Nat).testBit t.val)) := by
  rintro ⟨D,p,q,r,fan,_,_,budget,h⟩
  have hg : ∀g∈D.gates,valid g := by
    intro g mem
    obtain ⟨ops,ar⟩:=fan g mem
    exact ⟨by simpa only [Set.mem_insert_iff,Set.mem_singleton_iff] using ops,ar⟩
  have spec : ∀ t : Fin 6, bit t 17=( 17 : ℕ).testBit t.val ∧ bit t 25=( 25 : ℕ).testBit t.val ∧ bit t 28=( 28 : ℕ).testBit t.val := by decide +kernel
  have hp := present D hg p 17 (fun t => (h t).1.trans (spec t).1.symm)
  have hq := present D hg q 25 (fun t => (h t).2.1.trans (spec t).2.1.symm)
  have hr := present D hg r 28 (fun t => (h t).2.2.trans (spec t).2.2.symm)
  have hs : win [17,25,28] 6 inputs=true := by
    apply sound D.gates 6 inputs inputs _ budget hg (fun _ h => h) (by decide +kernel) (by decide +kernel)
    intro z hz
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl <;> assumption
  rw [excluded] at hs
  contradiction
