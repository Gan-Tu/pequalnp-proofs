import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.List.Perm.Basic
import Mathlib.Data.List.Perm.Subperm
import Mathlib.Data.List.Sublists
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Push
import Mathlib.Tactic.Tauto
import PEqualNP.Defs


-- The sample semantics and the finite gate search are adapted from jmwalsh96,
-- L_meta_1672 in this project. The signed-input exclusions and cofactors below
-- apply those semantics to a circuit starting with the complement of input four.

namespace PEqualNP.Outside.L_meta_1920

abbrev Sig := Nat × Nat
def top : Nat := 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def bnot (x : Nat) : Nat := x ^^^ top
def zero : Sig := (0, 0)
def one : Sig := (top, top)
def target : Sig := (top, 0)
def neg (a : Sig) : Sig := (bnot a.1, bnot a.2)
def bin (isOr : Bool) (a b : Sig) : Sig :=
  if isOr then (a.1 ||| b.1, a.2 ||| b.2) else (a.1 &&& b.1, a.2 &&& b.2)
def sep (d : Bool) (a : Sig) : Nat :=
  if d then a.1 ^^^ a.2 else a.1 &&& bnot a.2
def unionSep (d : Bool) : List Sig → Nat
  | [] => 0
  | a :: l => sep d a ||| unionSep d l
def Valid1 (x : Nat) : Prop := ∀ j, 414 ≤ j → x.testBit j = false
def Valid (a : Sig) : Prop := Valid1 a.1 ∧ Valid1 a.2
def proper (a : Sig) : Prop := Valid a ∧ a ≠ zero ∧ a ≠ one
lemma top_eq_pow : top = 2 ^ 207 * 2 ^ 207 - 1 := by decide
lemma pow_add_testBit (a b j : Nat) : (2 ^ a * 2 ^ b - 1).testBit j = decide (j < a + b) := by
  rw [← Nat.pow_add, Nat.testBit_two_pow_sub_one]
lemma testBit_top (j : Nat) : top.testBit j = decide (j < 414) := by
  rw [top_eq_pow]; exact pow_add_testBit 207 207 j
lemma testBit_bnot {x : Nat} (hx : Valid1 x) (j : Nat) :
    (bnot x).testBit j = if j < 414 then !(x.testBit j) else false := by
  simp only [bnot, Nat.testBit_xor, testBit_top]
  by_cases hj : j < 414
  · simp [hj]
  · simp [hj, hx j (by omega)]
lemma testBit_bnot_lt (x : Nat) {j : Nat} (hj : j < 414) :
    (bnot x).testBit j = !(x.testBit j) := by
  simp [bnot, Nat.testBit_xor, testBit_top, hj]
lemma valid1_zero : Valid1 0 := fun _ _ => Nat.zero_testBit _
lemma valid1_top : Valid1 top := fun j hj => by rw [testBit_top]; simp [show ¬ j < 414 by omega]
lemma valid1_bnot {x : Nat} (hx : Valid1 x) : Valid1 (bnot x) := fun j hj => by
  rw [testBit_bnot hx]; simp [show ¬ j < 414 by omega]
lemma valid1_and {x y : Nat} (hx : Valid1 x) : Valid1 (x &&& y) := fun j hj => by
  rw [Nat.testBit_and, hx j hj]; rfl
lemma valid1_or {x y : Nat} (hx : Valid1 x) (hy : Valid1 y) : Valid1 (x ||| y) := fun j hj => by
  rw [Nat.testBit_or, hx j hj, hy j hj]; rfl
lemma valid1_xor {x y : Nat} (hx : Valid1 x) (hy : Valid1 y) : Valid1 (x ^^^ y) := fun j hj => by
  rw [Nat.testBit_xor, hx j hj, hy j hj]; rfl
lemma lt_pow_mul_testBit {a b x j : Nat} (hx : x < 2 ^ a * 2 ^ b) (hj : a + b ≤ j) :
    x.testBit j = false := by
  rw [← Nat.pow_add] at hx
  exact Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by omega) hj))
lemma valid1_of_le_top {x : Nat} (h : x ≤ top) : Valid1 x := fun j hj => by
  have hlt : x < 2 ^ 207 * 2 ^ 207 := by
    have hp : 0 < 2 ^ 207 * 2 ^ 207 := by decide
    rw [top_eq_pow] at h; omega
  exact lt_pow_mul_testBit hlt hj
lemma valid_zero : Valid zero := ⟨valid1_zero, valid1_zero⟩
lemma valid_one : Valid one := ⟨valid1_top, valid1_top⟩
lemma valid_target : Valid target := ⟨valid1_top, valid1_zero⟩
lemma valid_neg {a : Sig} (ha : Valid a) : Valid (neg a) := ⟨valid1_bnot ha.1, valid1_bnot ha.2⟩
lemma valid_bin {d : Bool} {a b : Sig} (ha : Valid a) (hb : Valid b) : Valid (bin d a b) := by
  cases d
  · exact ⟨valid1_and ha.1, valid1_and ha.2⟩
  · exact ⟨valid1_or ha.1 hb.1, valid1_or ha.2 hb.2⟩
lemma valid_sep {d : Bool} {a : Sig} (ha : Valid a) : Valid1 (sep d a) := by
  cases d
  · exact valid1_and ha.1
  · exact valid1_xor ha.1 ha.2
lemma valid_unionSep {d : Bool} {v : List Sig} (hv : ∀ a ∈ v, Valid a) : Valid1 (unionSep d v) := by
  induction v with
  | nil => exact valid1_zero
  | cons a l ih =>
    exact valid1_or (valid_sep (hv a (by simp))) (ih (fun x hx => hv x (by simp [hx])))
lemma bin_comm (d : Bool) (a b : Sig) : bin d a b = bin d b a := by
  cases d
  · simp [bin, Nat.and_comm]
  · simp [bin, Nat.or_comm]
lemma bin_laws {a : Sig} (ha : Valid a) :
    bin false a one = a ∧ bin true a zero = a ∧
    bin false a zero = zero ∧ bin true a one = one ∧
    bin false a a = a ∧ bin true a a = a := by
  obtain ⟨p, n⟩ := a
  obtain ⟨hp, hn⟩ := ha
  have land_top {x : Nat} (hx : Valid1 x) : x &&& top = x := by
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_and, testBit_top]
    by_cases hj : j < 414 <;> simp [hj]
    exact hx j (by omega)
  have lor_top {x : Nat} (hx : Valid1 x) : x ||| top = top := by
    apply Nat.eq_of_testBit_eq; intro j
    rw [Nat.testBit_or, testBit_top]
    by_cases hj : j < 414 <;> simp [hj]
    exact hx j (by omega)
  simp [bin, one, zero, land_top hp, land_top hn, lor_top hp, lor_top hn]
lemma neg_laws : neg zero = one ∧ neg one = zero := by
  have h1 : bnot 0 = top := by simp [bnot]
  have h2 : bnot top = 0 := by simp [bnot]
  exact ⟨Prod.ext h1 h1, Prod.ext h2 h2⟩
lemma target_proper : proper target :=
  ⟨valid_target, by unfold target zero top; decide, by unfold target one top; decide⟩
lemma land_eq (x y : Nat) : Nat.land x y = x &&& y := rfl
lemma lor_eq (x y : Nat) : Nat.lor x y = x ||| y := rfl
lemma lxor_eq (x y : Nat) : Nat.xor x y = x ^^^ y := rfl
lemma testBit_land (x y i : Nat) : (Nat.land x y).testBit i = (x.testBit i && y.testBit i) := Nat.testBit_and x y i
lemma testBit_lor (x y i : Nat) : (Nat.lor x y).testBit i = (x.testBit i || y.testBit i) := Nat.testBit_or x y i
lemma testBit_lxor (x y i : Nat) : (Nat.xor x y).testBit i = (x.testBit i != y.testBit i) := by
  simp [bne]
abbrev Cov := Nat × Nat × Nat
def ValidCov (c : Cov) : Prop :=
  Valid1 c.1 ∧ Valid1 c.2.1 ∧ Valid1 c.2.2 ∧
  (∀ i, c.2.1.testBit i = true → c.1.testBit i = true) ∧
  (∀ i, c.2.2.testBit i = true → c.1.testBit i = true)
def covAdd (z : Nat) (c : Cov) : Cov :=
  (Nat.lor z c.1,
   Nat.land (Nat.xor z c.1) (Nat.lor z c.2.1),
   Nat.xor c.2.2 (Nat.land z (Nat.xor c.2.2 c.2.1)))
def coverage (d : Bool) (v : List Sig) : Cov :=
  v.foldr (fun a c => covAdd (sep d a) c) (0, 0, 0)
def takeOne (c : Cov) (a : Nat) : Nat := Nat.xor c.1 (Nat.land c.2.1 a)
def takeTwo (c : Cov) (a b : Nat) : Nat :=
  Nat.xor c.1 (Nat.lor (Nat.land c.2.1 (Nat.lor a b)) (Nat.land c.2.2 (Nat.land a b)))
lemma validCov_zero : ValidCov (0, 0, 0) :=
  ⟨valid1_zero, valid1_zero, valid1_zero, fun _ h => by simp at h, fun _ h => by simp at h⟩
lemma validCov_add {z : Nat} {c : Cov} (hz : Valid1 z) (hc : ValidCov c) : ValidCov (covAdd z c) := by
  refine ⟨valid1_or hz hc.1, valid1_and (valid1_xor hz hc.1), valid1_xor hc.2.2.1 (valid1_and hz), ?_, ?_⟩
  · intro i h; have h1 := hc.2.2.2.1 i
    simp only [covAdd, testBit_land, testBit_lor, testBit_lxor] at h ⊢
    revert h h1; cases z.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;> simp
  · intro i h; have h1 := hc.2.2.2.1 i; have h2 := hc.2.2.2.2 i
    simp only [covAdd, testBit_land, testBit_lor, testBit_lxor] at h ⊢
    revert h h1 h2; cases z.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;>
      cases c.2.2.testBit i <;> simp
lemma validCov_coverage (d : Bool) {v : List Sig} (hv : ∀ a ∈ v, Valid a) : ValidCov (coverage d v) := by
  induction v with
  | nil => exact validCov_zero
  | cons a l ih => exact validCov_add (valid_sep (hv a (by simp))) (ih (fun x hx => hv x (by simp [hx])))
lemma cov_one {c : Cov} {a : Nat} (hc : ValidCov c) : takeOne (covAdd a c) a = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := hc.2.2.2.1 i
  simp only [takeOne, covAdd, testBit_land, testBit_lor, testBit_lxor]
  revert h1; cases a.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;> simp
lemma cov_two {c : Cov} {a b : Nat} (hc : ValidCov c) :
    takeTwo (covAdd a (covAdd b c)) a b = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := hc.2.2.2.1 i; have h2 := hc.2.2.2.2 i
  simp only [takeTwo, covAdd, testBit_land, testBit_lor, testBit_lxor]
  revert h1 h2; cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
    cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> simp
lemma cov_two_unique_disj {c : Cov} {a b : Nat} (hc : ValidCov c) :
    Nat.land (Nat.land (covAdd a (covAdd b c)).2.1 a) b = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := hc.2.2.2.1 i
  simp only [covAdd, testBit_land, testBit_lor, testBit_lxor, Nat.zero_testBit]
  revert h1; cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
    cases c.2.1.testBit i <;> simp
lemma covAdd_swap {c : Cov} {a b : Nat} (hc : ValidCov c) :
    covAdd a (covAdd b c) = covAdd b (covAdd a c) := by
  have h1 := hc.2.2.2.1; have h2 := hc.2.2.2.2
  refine Prod.ext (Nat.eq_of_testBit_eq fun i => ?_)
    (Prod.ext (Nat.eq_of_testBit_eq fun i => ?_) (Nat.eq_of_testBit_eq fun i => ?_))
  · simp only [covAdd, testBit_lor]; cases a.testBit i <;> cases b.testBit i <;> rfl
  · have h1i := h1 i; simp only [covAdd, testBit_land, testBit_lor, testBit_lxor]
    revert h1i; cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
      cases c.2.1.testBit i <;> simp
  · have h1i := h1 i; have h2i := h2 i; simp only [covAdd, testBit_land, testBit_lor, testBit_lxor]
    revert h1i h2i; cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
      cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> simp
lemma cov_perm (d : Bool) {l r : List Sig} (hl : ∀ a ∈ l, Valid a) (h : l.Perm r) :
    coverage d l = coverage d r := by
  induction h with
  | nil => rfl
  | cons a _ ih =>
    exact congrArg (covAdd (sep d a)) (ih (fun x hx => hl x (by simp [hx])))
  | swap a b t =>
    exact covAdd_swap (validCov_coverage d (fun x hx => hl x (by simp [hx])))
  | trans h1 _ ih1 ih2 =>
    exact (ih1 hl).trans (ih2 (fun x hx => hl x (h1.mem_iff.2 hx)))
lemma cov_union (d : Bool) (v : List Sig) : (coverage d v).1 = unionSep d v := by
  induction v with
  | nil => rfl
  | cons a v ih => change sep d a ||| (coverage d v).1 = sep d a ||| unionSep d v; rw [ih]
def dropped (del v : List Sig) : List Sig := v.filter (fun x => !(del.contains x))
def keepOf (U : Finset Sig) (del : List Sig) : List Sig := del.filter (fun a => decide (a ∈ U))
lemma edit_list {v del : List Sig} {U : Finset Sig}
    (hv : v.Nodup) (hd : del.Nodup) (he : v.toFinset = del.toFinset ∪ U) :
    (keepOf U del ++ dropped del v).Nodup ∧ (keepOf U del ++ dropped del v).toFinset = U := by
  have memv (x : Sig) : x ∈ v ↔ x ∈ del ∨ x ∈ U := by
    rw [← List.mem_toFinset, he]; simp
  constructor
  · rw [List.nodup_append]
    refine ⟨hd.filter _, hv.filter _, ?_⟩
    intro a ha b hb eq; subst b
    simp [keepOf] at ha; simp [dropped] at hb; exact hb.2 ha.1
  · ext x
    simp only [List.mem_toFinset, List.mem_append, List.mem_filter, keepOf, dropped,
      decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem, memv]
    by_cases h : x ∈ del <;> simp_all
lemma recover_perm (del v : List Sig) (hv : v.Nodup) (hd : del.Nodup)
    (hs : ∀ x ∈ del, x ∈ v) : v.Perm (del ++ dropped del v) := by
  apply List.perm_of_nodup_nodup_toFinset_eq hv
  · rw [List.nodup_append]
    refine ⟨hd, hv.filter _, ?_⟩
    intro a ha b hb e; subst b; simp [dropped] at hb; exact hb.2 ha
  · ext x
    simp only [List.mem_toFinset, List.mem_append, dropped, List.mem_filter, Bool.not_eq_true',
      List.contains_eq_mem, decide_eq_false_iff_not]
    by_cases h : x ∈ del <;> simp_all
lemma one_rest (d : Bool) {v : List Sig} {a : Sig} (hv : v.Nodup) (hval : ∀ x ∈ v, Valid x)
    (ha : a ∈ v) :
    v.length - 1 = (dropped [a] v).length ∧
      takeOne (coverage d v) (sep d a) = unionSep d (dropped [a] v) := by
  have p := recover_perm [a] v hv (by simp) (by simpa using ha)
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d hval p]
    have hrest : ∀ x ∈ dropped [a] v, Valid x := fun x hx =>
      hval x (List.mem_of_mem_filter hx)
    exact (cov_one (validCov_coverage d hrest)).trans (cov_union d _)
lemma two_rest (d : Bool) {v : List Sig} {a b : Sig} (hv : v.Nodup) (hval : ∀ x ∈ v, Valid x)
    (ha : a ∈ v) (hb : b ∈ v) (hab : a ≠ b) :
    v.length - 2 = (dropped [a, b] v).length ∧
      takeTwo (coverage d v) (sep d a) (sep d b) = unionSep d (dropped [a, b] v) := by
  have p := recover_perm [a, b] v hv (by simp [hab]) (by simp [ha, hb])
  constructor
  · have l := p.length_eq; simp at l; omega
  · rw [cov_perm d hval p]
    have hrest : ∀ x ∈ dropped [a, b] v, Valid x := fun x hx =>
      hval x (List.mem_of_mem_filter hx)
    exact (cov_two (validCov_coverage d hrest)).trans (cov_union d _)
lemma two_rest_disj (d : Bool) {v : List Sig} {a b : Sig} (hv : v.Nodup) (hval : ∀ x ∈ v, Valid x)
    (ha : a ∈ v) (hb : b ∈ v) (hab : a ≠ b) :
    Nat.land (Nat.land (coverage d v).2.1 (sep d a)) (sep d b) = 0 := by
  have p := recover_perm [a, b] v hv (by simp [hab]) (by simp [ha, hb])
  rw [cov_perm d hval p]
  exact cov_two_unique_disj (validCov_coverage d (fun x hx => hval x (List.mem_of_mem_filter hx)))
inductive Live : Nat → Nat → Finset Sig → Prop
  | stop : Live 0 0 {target}
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} (ha : proper a)
      (hfresh : neg a ∉ insert a U) (tail : Live k t (insert (neg a) U)) :
      Live (k + 1) (t + 1) (insert a U)
  | binary {k t : Nat} {U : Finset Sig} {a b : Sig} {d : Bool}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live k t (insert (bin d a b) U)) :
      Live (k + 1) t (insert a (insert b U))
lemma live_proper {k t S} (h : Live k t S) : ∀ a ∈ S, proper a := by
  induction h with
  | stop => simpa using target_proper
  | unary ha _ _ ih => simpa using And.intro ha (fun a h => ih a (Finset.mem_insert_of_mem h))
  | binary ha hb _ _ _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha, hb, fun a h => ih a (Finset.mem_insert_of_mem h)⟩
lemma live_size {k t S} (h : Live k t S) : t ≤ k ∧ S.card + t ≤ k + 1 := by
  induction h with
  | stop => simp
  | @unary k t U a _ hf _ ih =>
    have hu : neg a ∉ U := fun hm => hf (Finset.mem_insert_of_mem hm)
    rw [Finset.card_insert_of_notMem hu] at ih
    have hc := Finset.card_insert_le a U
    exact ⟨by omega, by omega⟩
  | @binary k t U a b d _ _ _ hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    exact ⟨by omega, by omega⟩
lemma sep_unary (t : Nat) {a : Sig} (ha : Valid a) (i : Nat) (hi : i < 414)
    (h : (sep (decide (0 < t)) (neg a)).testBit i = true) :
    (sep true a).testBit i = true := by
  cases ht : decide (0 < t)
  · simp only [sep, neg, ht, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_and,
      Nat.testBit_xor, testBit_bnot (valid1_bnot ha.2), testBit_bnot ha.1, testBit_bnot ha.2,
      hi] at h ⊢
    cases hx : a.1.testBit i <;> cases hy : a.2.testBit i <;> simp [hx, hy] at h ⊢
  · simp only [sep, neg, ht, ite_true, Nat.testBit_xor,
      testBit_bnot ha.1, testBit_bnot ha.2, hi] at h ⊢
    cases hx : a.1.testBit i <;> cases hy : a.2.testBit i <;> simp [hx, hy] at h ⊢
lemma sep_binary (t d : Bool) {a b : Sig} (_ha : Valid a) (_hb : Valid b) (i : Nat) (hi : i < 414)
    (h : (sep t (bin d a b)).testBit i = true) :
    (sep t a).testBit i = true ∨ (sep t b).testBit i = true := by
  cases t <;> cases d <;>
    simp only [sep, bin, Bool.false_eq_true, ite_true, ite_false, Nat.testBit_xor,
      Nat.testBit_and, Nat.testBit_or, testBit_bnot_lt _ hi] at h ⊢ <;>
    revert h <;>
    cases a.1.testBit i <;> cases a.2.testBit i <;>
    cases b.1.testBit i <;> cases b.2.testBit i <;> simp
lemma sep_weaken (t : Nat) {a : Sig} (ha : Valid a) (i : Nat) (hi : i < 414)
    (h : (sep (decide (0 < t)) a).testBit i = true) : (sep true a).testBit i = true := by
  cases ht : decide (0 < t)
  · simp only [sep, ht, Bool.false_eq_true, ite_false, ite_true, Nat.testBit_and,
      Nat.testBit_xor, testBit_bnot ha.2, hi] at h ⊢
    cases hx : a.1.testBit i <;> cases hy : a.2.testBit i <;> simp [hx, hy] at h ⊢
  · simpa [ht] using h
lemma live_sep {k t S} (h : Live k t S) (i : Nat) (hi : i < 414) :
    ∃ a ∈ S, (sep (decide (0 < t)) a).testBit i = true := by
  induction h with
  | stop =>
    refine ⟨target, by simp, ?_⟩
    simp [sep, target, Nat.testBit_and, testBit_top, testBit_bnot valid1_zero, hi]
  | unary ha _ tail ih =>
    obtain ⟨x, hx, h⟩ := ih
    simp only [Finset.mem_insert] at hx
    simp only [Nat.zero_lt_succ, decide_true]
    rcases hx with rfl | hU
    · exact ⟨_, Finset.mem_insert_self _ _, sep_unary _ ha.1 i hi h⟩
    · exact ⟨x, Finset.mem_insert_of_mem hU,
        sep_weaken _ (live_proper tail x (Finset.mem_insert_of_mem hU)).1 i hi h⟩
  | binary ha hb _ _ _ ih =>
    obtain ⟨x, hx, h⟩ := ih
    rcases Finset.mem_insert.mp hx with rfl | hU
    · rcases sep_binary _ _ ha.1 hb.1 i hi h with h | h
      · exact ⟨_, Finset.mem_insert_self _ _, h⟩
      · exact ⟨_, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), h⟩
    · exact ⟨x, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hU), h⟩
lemma mem_unionSep (d : Bool) (v : List Sig) (i : Nat) :
    (unionSep d v).testBit i = true ↔ ∃ a ∈ v, (sep d a).testBit i = true := by
  induction v with
  | nil => simp [unionSep]
  | cons a v ih =>
    simp only [unionSep, Nat.testBit_or, Bool.or_eq_true, ih, List.mem_cons, exists_eq_or_imp]
lemma live_cover {k t S} {v : List Sig} (h : Live k t S) (he : v.toFinset = S) :
    unionSep (decide (0 < t)) v = top := by
  have hv : ∀ a ∈ v, Valid a := fun a ha => (live_proper h a (he ▸ List.mem_toFinset.mpr ha)).1
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_top]
  by_cases hi : i < 414
  · simp only [hi, decide_true]
    obtain ⟨a, hm, ha⟩ := live_sep h i hi
    exact (mem_unionSep _ _ _).2 ⟨a, List.mem_toFinset.mp (he.symm ▸ hm), ha⟩
  · simp only [hi, decide_false]
    exact valid_unionSep hv i (by omega)
lemma union_append (d : Bool) (l r : List Sig) :
    unionSep d (l ++ r) = unionSep d l ||| unionSep d r := by
  induction l with
  | nil => simp [unionSep]
  | cons a l ih => simp [unionSep, ih, Nat.or_assoc]
open PEqualNP.CircuitLowerBounds
def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (bin false) one
  | .or => xs.foldr (bin true) zero
  | .not => neg (xs.headD zero)
  | _ => zero
def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w
lemma valid_getD {w : List Sig} (hw : ∀ a ∈ w, Valid a) (i : Nat) : Valid (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact valid_zero
  | some a => exact hw a (List.mem_of_getElem? h)
lemma gv_valid {w : List Sig} (hw : ∀ a ∈ w, Valid a) (g : Gate) : Valid (gv w g) := by
  obtain ⟨o, l⟩ := g
  cases o with
  | and =>
    change Valid ((l.map (fun i => w.getD i zero)).foldr (bin false) one)
    induction l with
    | nil => exact valid_one
    | cons i l ih => exact valid_bin (valid_getD hw i) ih
  | or =>
    change Valid ((l.map (fun i => w.getD i zero)).foldr (bin true) zero)
    induction l with
    | nil => exact valid_zero
    | cons i l ih => exact valid_bin (valid_getD hw i) ih
  | not =>
    cases l with
    | nil => exact valid_neg valid_zero
    | cons i _ => exact valid_neg (valid_getD hw i)
  | mod _ => exact valid_zero
  | maj => exact valid_zero
def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬ proper v
lemma get_rep (w : List Sig) (i : Nat) : represented w (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact Or.inr (fun h => h.2.1 rfl)
  | some a => exact Or.inl (List.mem_of_getElem? h)
lemma operand_cases {w : List Sig} {a : Sig} (hva : Valid a) (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hva, hz, ho⟩), hva, hz, ho⟩)
def witness (w : List Sig) (z : Sig) : Prop :=
  (∃ a ∈ w, proper a ∧ z = neg a) ∨
  (∃ d a b, a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b)
lemma bin_rep {w a b} (d : Bool) (hva : Valid a) (hvb : Valid b)
    (ha : represented w a) (hb : represented w b) :
    represented w (bin d a b) ∨ witness w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.2.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2.2 rfl)
  obtain ⟨a1, a0, az, ao, aa, aa'⟩ := bin_laws hva
  obtain ⟨b1, b0, bz, bo, bb, bb'⟩ := bin_laws hvb
  rcases operand_cases hva ha with rfl | rfl | ⟨ham, hap⟩
  · rw [bin_comm]; cases d <;> simp_all
  · rw [bin_comm]; cases d <;> simp_all
  rcases operand_cases hvb hb with rfl | rfl | ⟨hbm, hbp⟩
  · cases d <;> simp_all
  · cases d <;> simp_all
  by_cases he : a = b
  · subst b; cases d <;> simp_all
  exact Or.inr (Or.inr ⟨d, a, b, ham, hbm, hap, hbp, he, rfl⟩)
lemma gate_rep {w : List Sig} (hw : ∀ a ∈ w, Valid a) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    represented w (gv w g) ∨ witness w (gv w g) := by
  obtain ⟨o, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
  obtain ⟨ho, hl⟩ := h
  have rz : represented w zero := Or.inr (fun h => h.2.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2.2 rfl)
  have nx (a : Sig) (hva : Valid a) (ha : represented w a) :
      represented w (neg a) ∨ witness w (neg a) := by
    rcases operand_cases hva ha with rfl | rfl | ⟨hm, hp⟩
    · exact Or.inl (neg_laws.1 ▸ ro)
    · exact Or.inl (neg_laws.2 ▸ rz)
    · exact Or.inr (Or.inl ⟨a, hm, hp, rfl⟩)
  cases l with
  | nil =>
    rcases ho with rfl | rfl | rfl
    · exact Or.inl ro
    · exact Or.inl rz
    · exact nx _ valid_zero rz
  | cons i l =>
    cases l with
    | nil =>
      rcases ho with rfl | rfl | rfl
      · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
          (bin_laws (valid_getD hw i)).1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
          (bin_laws (valid_getD hw i)).2.1] using Or.inl (b := witness w (w.getD i zero)) (get_rep w i)
      · exact nx _ (valid_getD hw i) (get_rep w i)
    | cons j l =>
      cases l with
      | cons _ _ => simp at hl
      | nil =>
        rcases ho with rfl | rfl | rfl
        · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
            (bin_laws (valid_getD hw j)).1] using
            bin_rep false (valid_getD hw i) (valid_getD hw j) (get_rep w i) (get_rep w j)
        · simpa only [gv, List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil,
            (bin_laws (valid_getD hw j)).2.1] using
            bin_rep true (valid_getD hw i) (valid_getD hw j) (get_rep w i) (get_rep w j)
        · exact nx _ (valid_getD hw i) (get_rep w i)
lemma pull_gate {w : List Sig} {z : Sig} {k t S} (h : Live k t S)
    (hz : represented w z ∨ witness w z) (sub : ∀ a ∈ S, a ∈ w ++ [z]) :
    ∃ k' t' S', k' ≤ k + 1 ∧ Live k' t' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k, t, S, by omega, h, ?_⟩
      intro a ha
      rcases (by simpa using sub a ha : a ∈ w ∨ a = z) with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | (⟨a, ha, hp', eq⟩ | ⟨d, a, b, ha, hb, pa, pb, hab, eq⟩)
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (neg a)
        have ht : Live k t (insert (neg a) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv; obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hm
        have hf : neg a ∉ insert a U := by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          · exact hw (hu _ u)
        exact ⟨_, _, _, Nat.le_refl _, Live.unary hp' hf ht, by simpa using And.intro ha hu⟩
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live k t (insert (bin d a b) U) := by simpa [U, Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv; obtain ⟨hne, hm⟩ := Finset.mem_erase.mp hv; simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh; rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_, _, _, Nat.le_refl _, Live.binary pa pb hab hf ht,
          by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k, t, S, by omega, h, ?_⟩
    intro a ha; have hn : a ≠ z := fun hh => hm (hh ▸ ha); simpa [hn] using sub a ha
lemma extract (gs : List Gate) (w : List Sig) (hw : ∀ a ∈ w, Valid a)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hout : target ∈ execute gs w) :
    ∃ k t S, k ≤ gs.length ∧ Live k t S ∧ ∀ a ∈ S, a ∈ w := by
  induction gs generalizing w with
  | nil => exact ⟨0, 0, {target}, by simp, Live.stop, by simpa [execute] using hout⟩
  | cons g gs ih =>
    have hw' : ∀ a ∈ w ++ [gv w g], Valid a := by
      intro a ha; rcases List.mem_append.mp ha with ha | ha
      · exact hw a ha
      · simp only [List.mem_singleton] at ha; exact ha ▸ gv_valid hw g
    obtain ⟨k, t, S, hk, ht, hs⟩ := ih (w ++ [gv w g]) hw' (fun a ha => legal a (by simp [ha])) hout
    obtain ⟨l, u, T, hl, hu, hT⟩ := pull_gate ht (gate_rep hw g (legal g (by simp))) hs
    exact ⟨l, u, T, by simp; omega, hu, hT⟩
def bit (side : Bool) (i : Fin 414) (a : Sig) : Bool :=
  (if side then a.1 else a.2).testBit i.val
lemma bit_zero (s i) : bit s i zero = false := by cases s <;> simp [bit, zero]
lemma bit_one (s i) : bit s i one = true := by
  cases s <;> simp [bit, one, testBit_top, i.isLt]
lemma bit_neg (s i) {a : Sig} (ha : Valid a) : bit s i (neg a) = !(bit s i a) := by
  cases s
  · simp [bit, neg, testBit_bnot ha.2, i.isLt]
  · simp [bit, neg, testBit_bnot ha.1, i.isLt]
lemma bit_bin (s i d) (a b : Sig) : bit s i (bin d a b) =
    (if d then bit s i a || bit s i b else bit s i a && bit s i b) := by
  cases s <;> cases d <;> simp [bit, bin, Nat.testBit_and, Nat.testBit_or]
lemma b_read (s i) (w : List Sig) (j : Nat) :
    (w.map (bit s i)).getD j false = bit s i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _ _).symm
  | some a => rfl
lemma run_bit (s i) (g : Gate) (w : List Sig) (hw : ∀ a ∈ w, Valid a)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    bit s i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit s i)).getD j false) := by
  obtain ⟨o, l⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _ _
    | cons a l ih =>
      change bit s i (bin false _ _) = (_ && _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _ _
    | cons a l ih =>
      change bit s i (bin true _ _) = (_ || _)
      rw [bit_bin]; exact congrArg (fun x => bit s i (w.getD a zero) || x) ih
  · cases l with
    | nil => exact (bit_neg s i valid_zero).trans (by rw [bit_zero]; rfl)
    | cons a l => exact bit_neg s i (valid_getD hw a)
lemma execute_bits (gs : List Gate) (s i) (w : List Sig) (hw : ∀ a ∈ w, Valid a)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit s i) =
    gs.foldl (fun (l : List Bool) g => l ++ [g.op.eval (g.inputs.map fun j => l.getD j false)])
      (w.map (bit s i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    have hw' : ∀ a ∈ w ++ [gv w g], Valid a := by
      intro a ha; rcases List.mem_append.mp ha with ha | ha
      · exact hw a ha
      · simp only [List.mem_singleton] at ha; exact ha ▸ gv_valid hw g
    change (execute gs (w ++ [gv w g])).map _ = _
    rw [ih _ hw' (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons, List.map_append, List.map_singleton, run_bit s i g w hw (hg g (by simp))]
lemma foldl_append_getD {α : Type} (f : List α → Gate → α) (gs : List Gate)
    (l : List α) (i : Nat) (hi : i < l.length) (d : α) :
    (gs.foldl (fun acc g => acc ++ [f acc g]) l).getD i d = l.getD i d := by
  induction gs generalizing l with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (l ++ [f l g]).length := by simp; omega
    rw [ih (l ++ [f l g]) hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
def raw0 : Sig := (0xc4000000000000000003fffffc000000003ffc210fe00847f007e01f83e01107e03e042084423f0fc3c08220842122287e3e0f, 0x15115115115115115115115115115115115100007e00003f003e00f83e00003e01e000000001f0fc3c00000000000003e3e07)
def raw1 : Sig := (0x10c000000000000003ffc000000000003ffffffe0f82017c010fc20208423f0fc21e208410884411044517e1f805f05e7c20279, 0x208e08e08e08e08e08e08e08e08e08e08e08fe0f80007c0007c00000001f0fc01e000000000000000007e1f801f01e7c00038)
def raw2 : Sig := (0x218000000000003ffc000000000003fffffc000421043f883ff880041084422084244fc027c3e022ffc0f84010be21e40847fd0, 0xc50c50c50c50c50c50c50c50c50c50c50c50000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0)
def raw3 : Sig := (0x430000000003ffc000000000003fffffc00000084208421082110448ffc0044fffe00109f90089ff08802085ffc800897ffc480, 0x1a41a41a41a41a41a41a41a41a41a41a41a400000000000000000ffc0000fffe00001f80001ff00000001ffc000007ffc000)
def raw4 : Sig := (0x60000000000000000000003fffffc000000003ff0101fffc400083f21081ff1084087fe4003fe441008fffe210001ff9088802, 0x2a4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4aa4bff0001fffc000003f00001ff0000007fe0003fe000000fffe000001ff8000000)
def raw5 : Sig := (0x2883ffc003ffc000000003ffc0000000000000010842084210822109042108882108917fffffc00802010fffffffffe000101004, 0x6c06c06c06c06c06c06c06c06c06c06c06c0000000000000000000000000000007fffffc00000000fffffffffe000000000)
def raw6 : Sig := (0x1100003ffc000000003ffc0000000000000000021084108421044213ffffff004001007ffffffffffffff0100400040102000020, 0x3703703703703703703703703703703703700000000000000003fffffe000000007ffffffffffffff0000000000000000000)
def raw7 : Sig := (0xa00000003ffc003ffc000000000000000000003ffffff0002080003ffffffffffffffa108211000041004208821085000002100, 0x3383383383383383383383383383383383383fffffe0000000003ffffffffffffff8000000000000000000000000000000000)
def raw8 : Sig := (0x3403fffffc003ffc000000000000000000000003fffffffffffffffe084210008210004210422110882228411042108004210000, 0x3c03c03c03c03c03c03c03c03c03c03c03c03fffffffffffffffc000000000000000000000000000000000000000000000000)
def raw : List Sig := [raw0, raw1, raw2, raw3, raw4, raw5, raw6, raw7, raw8]
def symKey1 : Nat := 0x32799cc653399bc965b2b9acee5e25108bc5a2b1488c66271887c3ab558afd7abb5cacd86b760abd5a9d4ca9d4aa350a6d569f54a5d2a3d1c91c8a43208ec963f248dc6afd7cc1e0b0380bee16ff84bddeae570bbddaeb74b8de6e778b7dba0d0485c2a130882c360f0c81c0a6d349dcea73389acf66f3c99cca552897cba5b2c94cc6573093c9acd64b5daad368b2db6cf6cb1d8b1588c7e3b1b8cc4e471790c3e1a8540a3d1a8b44a0d2687489fcf90a8342219046c351acda693a9cce87639168ac582b96cb2542914caae774391cae67192890492591c482211885b0d96a359aad76934d9ed0688c05c2f188b41a090582818080301d7cbd5fb0580bc5c2dd72bb5d2cd64b45b2d55cad57ac560aa54ab156803f1fd027d3319cd0653c9ecf07a3e1dcc26031190c65d2e178be70379c4dc4e27944a04c26bfa02ff803f54aa85329d489b4f2713e9d4d3d1eef57b3cd1c9047a35f2fc7d3edf0a15128d40964aa5d329848a492893773c9daf077bc5d2ec753ad148945a310e886fb89c0e16f108884521918821e1007c3a381d0ec723c1b85c32180d05996ce663359429150ac58280201406dd6db71b43f1f1007a1c0d8cc6a341b0c8241109854280e0784192c563b1990c46130c4c27128000202
def symKey2 : Nat := 0x32995cce6b3796c9e63399dcbe4a411f8ec6a43259247a471b8e48a592b94c9a5b31984aa5f27944bab95bacd5abb61b056abf57ac57ad167b2d8ad36db659ad763b25aae973b8dbaeb79bc5caef6fb85da71379acca733d9e4da77339a4ea291388c3a2b198c44a2f0f8845aa14fa6d2aa355aa53aa74ba654b017fbedeb0385c25fb077bbe60b198bc4e1b1b91c862b1f87c463a8943a0cfa8b49a450a8f3fa051a110782c0a130d8641a17038242972b85dae96eb459ad96ab24ba5932984aa71369e4fa75349248a51267b3d1e4f8773c188c26431980bc5d2f97076391c0e878371a8d066361904c24150a04430170c8682c0f070417ebe60b0178bd7fbfa03007ebe9f2fc7dbe14ca55429d48a250a8d40af572c560ad552b156a977bc1dcf278bb5eaf47bbd9e6ea74bb1d68b45231128e4823d1a87442110a864120cd66c369a4d4e57439dcce372124944b23920462410888fe80409f4fc6734194cce06fb89c2de6db75b8da219148444231047c3f200f43e1e10074381b3a1d4ec723995cb4582d964ac532a154a4d56cb59b0d76a341a6d268b3c5e30188b45c0a0682c1809038200c70389b8de4f289409c4d263198ec96431598cb6733594c26230c5629150b05026138940202000100a03
def posKey4 : Nat := 0x5dad9eeb158ab158f678bad3e9f4ca6528947a365b2d369bb5da7c3b1c4c85f2d96caa5567144a24d269349a4d269349a4d269349a3c1b35c6231160b190271389c4e271389c4e271389c4ed56806834150a84020100804020100804020100835196cb62b15747b3d9d56070382e166b74f278b45a2a1515a90480ec76981a8d4602b15a304c26130984c26130984c2613099369648a552a8e0683410080402010080402010080402112893a1d0743a3198ce6592c8a854502815cae532998032192b1489c05028140a05028140a05028140a38178bc6e140a0a4520c060a00402010080402010080402010082e0a0501c0e070381c0e070381c0e07038442209020100804020100804020100804000000000000000000000000000
def negKey4 : Nat := 0x5bac9e6ed56ba552f376ba5e69a76a55d29179bb5a8e967bcdda77391b8c05c6a1599e52653149cf376b5184b74d1dce456260df2437193519e2d650a18af376b5184b74d1dce4561b89724d467b282cc508bcddad4612dd3477391586e0ec93519eca653156eb23b9c95aa9372dd64b7592695a56549495aa946a686e95488c85a8d14225e6ed6a2dd34873b9c8ac3712e49349548a692a8d44825e6ed6a2dd34873b9c8ac37036491a893b9c8ee373b980e4722b1b8506e27180ac5c29180b8162b1489cf376b516e9a3b9c8ac4c1b80f2437190b46e32088b4502d048a1e6ed6a2dd3477391586e25006482c1104bcddad45ba68ee722b0dc1c06c9058220979bb5a8b74d1dce4561b818079279bb5a8b74d1dce4561b80c0192
def posKey0 : Nat := 0xf68011960702a38581a189545653038984c260ca389a35178984e080d1d0080526acc582a0d041582903bd120293ab406a742a8eca4cb1d89c542f1325136101889da0086981c4c8e56250aa31480bc0e05028146a8e13864a605268112874040984e38561c12810161500ef415950e6d00c9d0629e1834d3c4d3814c0a1a4d840aa4d68134aa10029c4a85369b2ce01a080984c260c9c408354a098102729a7c9a05020f0a8902981c52ac081d854ac7b3406a9f659ed9c553d8212094130bcf80769821a027188404c71148bd96d3152502005028146a71040643405021345e9f1389810b6148ac5e072a0b02076380b1eed00ca7da63a758c47404158680a533e01d9604
def negKey0 : Nat := 0xe076480d92c901984c2193285acf292a522b23bb3ca4b2391c994a91b9dc0603652c9e6774d0395237033cd1a2d3933c647229268a4f31bb08503216ba534cf67b3c1d920364b240661308b8e92933c5a280b0dceecf168dce472748a1647743a1dd237799dd340e142c80cf346948e4cf2e1c85a9a16bcd64c254970a4ca4d33d9ecf076498592c93080c0648949d2cf650a064374d33d943779bcca42859268984c290dce49a3b83850b2611c8dce979b3d22f3651dd9472590195291748b4eecf67b3c1d926164b24c2030182c2d6533dd2a92e2c934cf74ac9e6f316aa46e9a128945ab239268ee0e548dd847237329e6cf0b3cdd277749c86e061405994523bb3d9ecf
def rawPermCodes : Fin 12 → Nat := ![0x876543210, 0x267143850, 0x374268501, 0x364872105, 0x547068321, 0x146072385, 0x846375012, 0x247361058, 0x64175832, 0x74561238, 0x567840123, 0x176240583]
def perm1 : Fin 9 → Nat := ![0, 5, 8, 3, 4, 1, 7, 6, 2]
def perm2 : Fin 9 → Nat := ![1, 0, 5, 8, 6, 2, 4, 7, 3]
def gOfV : Fin 9 → Fin 12 := ![0, 2, 6, 10, 0, 4, 2, 4, 8]

def sample (s : Bool) (i : Fin 414) (j : Fin 9) : Bool :=
  bit s i (raw.getD j.val zero)
def edgeF (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)
set_option maxRecDepth 20000 in
lemma sample_ok : ∀ (s : Bool) (i : Fin 414), edgeF (sample s i) = s := by decide +kernel
lemma raw_id : List.ofFn (fun j : Fin 9 => raw.getD j.val zero) = raw := rfl
lemma sample_list (s i) : List.ofFn (sample s i) = raw.map (bit s i) := by
  calc
    _ = (List.ofFn (fun j : Fin 9 => raw.getD j.val zero)).map (bit s i) := by
      rw [List.map_ofFn]; rfl
    _ = _ := by rw [raw_id]
lemma raw_lt : raw.all (fun a => decide (a.1 ≤ top ∧ a.2 ≤ top)) = true := by decide +kernel
lemma raw_valid : ∀ a ∈ raw, Valid a := by
  intro a ha
  have h := of_decide_eq_true (List.all_eq_true.mp raw_lt a ha)
  exact ⟨valid1_of_le_top h.1, valid1_of_le_top h.2⟩
lemma raw_nd : raw.Nodup := by unfold raw; decide +kernel
lemma every_input : raw.all (fun a => unionSep true (raw.erase a) != top) = true := by decide +kernel
lemma necessary {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ raw) : raw.toFinset = S := by
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr => ?_, hs a⟩
  by_contra hn
  have fail := List.all_eq_true.mp every_input a hr
  have cov : unionSep true (raw.erase a) = top := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [testBit_top]
    by_cases hi : i < 414
    · simp only [hi, decide_true]
      obtain ⟨b, hb, h⟩ := live_sep l i hi
      have ba : b ≠ a := fun he => hn (he ▸ hb)
      have hm := (List.mem_erase_of_ne ba).mpr (hs _ hb)
      exact (mem_unionSep true _ _).2 ⟨b, hm, sep_weaken _ (live_proper l b hb).1 i hi h⟩
    · simp only [hi, decide_false]
      exact valid_unionSep (fun x hx => raw_valid x (List.mem_of_mem_erase hx)) i (by omega)
  simp [cov] at fail
lemma execute_valid (gs : List Gate) (w : List Sig) (hw : ∀ a ∈ w, Valid a) :
    ∀ a ∈ execute gs w, Valid a := by
  induction gs generalizing w with
  | nil => exact hw
  | cons g gs ih =>
    apply ih (w ++ [gv w g])
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hw a ha
    · simp only [List.mem_singleton] at ha; exact ha ▸ gv_valid hw g
lemma circuit_target (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (he : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = edgeF x) : target ∈ execute C.gates raw := by
  let w := execute C.gates raw
  have hwv : ∀ a ∈ w, Valid a := execute_valid C.gates raw raw_valid
  have hproj (s : Bool) (i : Fin 414) : bit s i (w.getD C.output zero) = s := by
    rw [← b_read]
    change ((execute C.gates raw).map _).getD C.output false = _
    rw [execute_bits _ _ _ _ raw_valid (fun g hg => (h g hg).1)]
    have eq := he (sample s i)
    rw [sample_list, sample_ok] at eq
    exact eq
  have hvout : Valid (w.getD C.output zero) := valid_getD hwv C.output
  have et : w.getD C.output zero = target := by
    apply Prod.ext
    · apply Nat.eq_of_testBit_eq; intro i
      rw [target, testBit_top]
      by_cases hi : i < 414
      · simpa [bit, hi] using hproj true ⟨i, hi⟩
      · rw [hvout.1 i (by omega)]; simp [hi]
    · apply Nat.eq_of_testBit_eq; intro i
      by_cases hi : i < 414
      · simpa [bit, target] using hproj false ⟨i, hi⟩
      · rw [hvout.2 i (by omega), target]; exact (Nat.zero_testBit i).symm
  have rep := get_rep w C.output
  rw [et] at rep
  exact rep.resolve_right (fun hn => hn target_proper)

def index9 (key : Nat) (j : Nat) : Nat := (key >>> (9 * j)) &&& 511
def reindexLoop (f : Fin 414 → Fin 414) (x : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 =>
    let rest := reindexLoop f x n
    if h : n < 414 then
      if x.testBit (f ⟨n, h⟩).val then rest ||| (1 <<< n) else rest
    else rest
def reindex (f : Fin 414 → Fin 414) (x : Nat) : Nat := reindexLoop f x 414
lemma reindexLoop_testBit (f : Fin 414 → Fin 414) (x : Nat) (m j : Nat) :
    (reindexLoop f x m).testBit j =
      if h : j < m ∧ j < 414 then x.testBit (f ⟨j, h.2⟩).val else false := by
  induction m with
  | zero => simp [reindexLoop]
  | succ n ih =>
    unfold reindexLoop
    dsimp only
    by_cases hn : n < 414
    · simp only [hn, dite_true]
      by_cases hx : x.testBit (f ⟨n, hn⟩).val = true
      · simp only [hx, ite_true, Nat.testBit_or, ih, Nat.testBit_shiftLeft]
        by_cases hj : j = n
        · subst j; simp [hn, hx]
        · have h1 : ¬ (j ≥ n ∧ (1 : Nat).testBit (j - n) = true) := by
            intro ⟨hge, htb⟩
            have hpos : 1 ≤ j - n := by omega
            have hlt2 : 1 < 2 ^ (j - n) := by
              have h2 : 2 ^ 1 ≤ 2 ^ (j - n) := Nat.pow_le_pow_right (by omega) hpos
              omega
            rw [Nat.testBit_lt_two_pow hlt2] at htb; contradiction
          have hbit : (decide (n ≤ j) && (1 : Nat).testBit (j - n)) = false := by
            cases hle : decide (n ≤ j)
            · rfl
            · cases ht : (1 : Nat).testBit (j - n)
              · rfl
              · exact (h1 ⟨of_decide_eq_true hle, ht⟩).elim
          rw [hbit, Bool.or_false]
          by_cases hlt : j < n
          · have hlt' : j < n + 1 := by omega
            have hj414 : j < 414 := by omega
            simp [hlt, hlt', hj414]
          · have hge : ¬ (j < n + 1) := by omega
            simp [hlt, hge]
      · have hxf : x.testBit (f ⟨n, hn⟩).val = false := Bool.eq_false_iff.mpr hx
        simp only [hxf, Bool.false_eq_true, ite_false, ih]
        by_cases hj : j = n
        · subst j; simp [hn, hxf]
        · by_cases hlt : j < n
          · simp [hlt, show j < n + 1 by omega, show j < 414 by omega]
          · simp [hlt, show ¬ (j < n + 1) by omega]
    · simp only [hn, dite_false, ih]
      by_cases hj : j < 414
      · have h1 : j < n := by omega
        have h2 : j < n + 1 := by omega
        simp [hj, h1, h2]
      · simp [hj]
lemma reindex_testBit (f : Fin 414 → Fin 414) (x : Nat) (j : Nat) :
    (reindex f x).testBit j = if h : j < 414 then x.testBit (f ⟨j, h⟩).val else false := by
  simpa [reindex] using reindexLoop_testBit f x 414 j
lemma reindex_valid1 (f : Fin 414 → Fin 414) (x : Nat) : Valid1 (reindex f x) := by
  intro j hj; rw [reindex_testBit]; simp [show ¬ j < 414 by omega]
lemma reindex_and (f : Fin 414 → Fin 414) (a b : Nat) :
    reindex f (a &&& b) = reindex f a &&& reindex f b := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_and, reindex_testBit, reindex_testBit, reindex_testBit]
  by_cases hj : j < 414 <;> simp [hj, Nat.testBit_and]
lemma reindex_or (f : Fin 414 → Fin 414) (a b : Nat) :
    reindex f (a ||| b) = reindex f a ||| reindex f b := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [Nat.testBit_or, reindex_testBit, reindex_testBit, reindex_testBit]
  by_cases hj : j < 414 <;> simp [hj, Nat.testBit_or]
lemma reindex_bnot (f : Fin 414 → Fin 414) {a : Nat} (ha : Valid1 a) :
    reindex f (bnot a) = bnot (reindex f a) := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [reindex_testBit, testBit_bnot (reindex_valid1 f a), reindex_testBit]
  by_cases hj : j < 414
  · simp [hj, testBit_bnot ha, (f ⟨j, hj⟩).isLt]
  · simp [hj]
lemma reindex_zero (f : Fin 414 → Fin 414) : reindex f 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro j; rw [reindex_testBit]; split <;> simp
lemma reindex_top (f : Fin 414 → Fin 414) : reindex f top = top := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [reindex_testBit, testBit_top]
  by_cases hj : j < 414
  · simp [hj, testBit_top, (f ⟨j, hj⟩).isLt]
  · simp [hj]
lemma reindex_comp (f g : Fin 414 → Fin 414) (x : Nat) :
    reindex f (reindex g x) = reindex (fun j => g (f j)) x := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [reindex_testBit, reindex_testBit]
  by_cases hj : j < 414
  · simp [hj, reindex_testBit, (f ⟨j, hj⟩).isLt]
  · simp [hj]
lemma reindex_id {x : Nat} (hx : Valid1 x) : reindex (fun j => j) x = x := by
  apply Nat.eq_of_testBit_eq; intro j
  rw [reindex_testBit]
  by_cases hj : j < 414
  · simp [hj]
  · simp [hj, hx j (by omega)]
structure SigHom where
  fn : Sig → Sig
  valid : ∀ a, Valid (fn a)
  hneg : ∀ {a}, Valid a → fn (neg a) = neg (fn a)
  hbin : ∀ d a b, fn (bin d a b) = bin d (fn a) (fn b)
  hzero : fn zero = zero
  hone : fn one = one
  htarget : fn target = target
def pairHom (fp fn : Fin 414 → Fin 414) : SigHom where
  fn a := (reindex fp a.1, reindex fn a.2)
  valid a := ⟨reindex_valid1 fp a.1, reindex_valid1 fn a.2⟩
  hneg ha := Prod.ext (reindex_bnot fp ha.1) (reindex_bnot fn ha.2)
  hbin d a b := by cases d <;> simp [bin, reindex_and, reindex_or]
  hzero := Prod.ext (reindex_zero fp) (reindex_zero fn)
  hone := Prod.ext (reindex_top fp) (reindex_top fn)
  htarget := Prod.ext (reindex_top fp) (reindex_zero fn)
def compHom (h1 h2 : SigHom) : SigHom where
  fn a := h1.fn (h2.fn a)
  valid a := h1.valid (h2.fn a)
  hneg ha := by rw [h2.hneg ha, h1.hneg (h2.valid _)]
  hbin d a b := by rw [h2.hbin, h1.hbin]
  hzero := by rw [h2.hzero, h1.hzero]
  hone := by rw [h2.hone, h1.hone]
  htarget := by rw [h2.htarget, h1.htarget]
def sym1 (j : Fin 414) : Fin 414 := Fin.ofNat 414 (index9 symKey1 j.val)
def sym2 (j : Fin 414) : Fin 414 := Fin.ofNat 414 (index9 symKey2 j.val)
set_option maxRecDepth 20000 in
lemma sym1_invol : ∀ j : Fin 414, sym1 (sym1 j) = j := by decide +kernel
set_option maxRecDepth 20000 in
lemma sym2_invol : ∀ j : Fin 414, sym2 (sym2 j) = j := by decide +kernel
set_option maxRecDepth 20000 in
lemma sym11_eq : ∀ j : Fin 414,
    sym1 (sym2 (sym1 (sym2 (sym1 (sym2 j))))) = sym2 (sym1 (sym2 (sym1 (sym2 (sym1 j))))) := by
  decide +kernel
def hom1 : SigHom := pairHom sym1 sym1
def hom2 : SigHom := pairHom sym2 sym2
abbrev action1 (a : Sig) : Sig := hom1.fn a
abbrev action2 (a : Sig) : Sig := hom2.fn a
lemma action1_invol {a : Sig} (ha : Valid a) : action1 (action1 a) = a := by
  apply Prod.ext <;> dsimp [action1, hom1, pairHom] <;> rw [reindex_comp] <;>
    simpa [sym1_invol] using reindex_id (by first | exact ha.1 | exact ha.2)
lemma action2_invol {a : Sig} (ha : Valid a) : action2 (action2 a) = a := by
  apply Prod.ext <;> dsimp [action2, hom2, pairHom] <;> rw [reindex_comp] <;>
    simpa [sym2_invol] using reindex_id (by first | exact ha.1 | exact ha.2)
lemma action11_swap (a : Sig) :
    action1 (action2 (action1 (action2 (action1 (action2 a))))) =
    action2 (action1 (action2 (action1 (action2 (action1 a))))) := by
  apply Prod.ext <;> dsimp [action1, action2, hom1, hom2, pairHom] <;>
    simp only [reindex_comp] <;>
    exact congrArg (fun f => reindex f _) (funext fun j => (sym11_eq j).symm)
def homG (g : Fin 12) : SigHom :=
  match g.val with
  | 0 => pairHom id id
  | 1 => hom1
  | 2 => hom2
  | 3 => compHom hom1 hom2
  | 4 => compHom hom2 hom1
  | 5 => compHom hom1 (compHom hom2 hom1)
  | 6 => compHom hom2 (compHom hom1 hom2)
  | 7 => compHom hom1 (compHom hom2 (compHom hom1 hom2))
  | 8 => compHom hom2 (compHom hom1 (compHom hom2 hom1))
  | 9 => compHom hom1 (compHom hom2 (compHom hom1 (compHom hom2 hom1)))
  | 10 => compHom hom2 (compHom hom1 (compHom hom2 (compHom hom1 hom2)))
  | _ => compHom hom1 (compHom hom2 (compHom hom1 (compHom hom2 (compHom hom1 hom2))))
abbrev action (g : Fin 12) (a : Sig) : Sig := (homG g).fn a
def invG (g : Fin 12) : Fin 12 :=
  ![0, 1, 2, 4, 3, 5, 6, 8, 7, 9, 10, 11] g
lemma action0_eq {a : Sig} (ha : Valid a) : action 0 a = a :=
  Prod.ext (reindex_id ha.1) (reindex_id ha.2)
lemma action_valid (g : Fin 12) (a : Sig) : Valid (action g a) := (homG g).valid a
lemma action_neg (g : Fin 12) {a : Sig} (ha : Valid a) : action g (neg a) = neg (action g a) :=
  (homG g).hneg ha
lemma action_bin (g : Fin 12) (d : Bool) (a b : Sig) :
    action g (bin d a b) = bin d (action g a) (action g b) := (homG g).hbin d a b
lemma action_zero (g : Fin 12) : action g zero = zero := (homG g).hzero
lemma action_one (g : Fin 12) : action g one = one := (homG g).hone
lemma action_target (g : Fin 12) : action g target = target := (homG g).htarget
lemma action_inv (g : Fin 12) {a : Sig} (ha : Valid a) :
    action (invG g) (action g a) = a := by
  fin_cases g
  · exact (action0_eq (action_valid 0 a)).trans (action0_eq ha)
  · exact action1_invol ha
  · exact action2_invol ha
  · change action2 (action1 (action1 (action2 a))) = a
    rw [action1_invol (hom2.valid a), action2_invol ha]
  · change action1 (action2 (action2 (action1 a))) = a
    rw [action2_invol (hom1.valid a), action1_invol ha]
  · change action1 (action2 (action1 (action1 (action2 (action1 a))))) = a
    rw [action1_invol (hom2.valid _), action2_invol (hom1.valid _), action1_invol ha]
  · change action2 (action1 (action2 (action2 (action1 (action2 a))))) = a
    rw [action2_invol (hom1.valid _), action1_invol (hom2.valid _), action2_invol ha]
  · change action2 (action1 (action2 (action1 (action1 (action2 (action1 (action2 a))))))) = a
    rw [action1_invol (hom2.valid _), action2_invol (hom1.valid _),
        action1_invol (hom2.valid _), action2_invol ha]
  · change action1 (action2 (action1 (action2 (action2 (action1 (action2 (action1 a))))))) = a
    rw [action2_invol (hom1.valid _), action1_invol (hom2.valid _),
        action2_invol (hom1.valid _), action1_invol ha]
  · change action1 (action2 (action1 (action2 (action1 (action1 (action2 (action1 (action2 (action1 a))))))))) = a
    rw [action1_invol (hom2.valid _), action2_invol (hom1.valid _),
        action1_invol (hom2.valid _), action2_invol (hom1.valid _), action1_invol ha]
  · change action2 (action1 (action2 (action1 (action2 (action2 (action1 (action2 (action1 (action2 a))))))))) = a
    rw [action2_invol (hom1.valid _), action1_invol (hom2.valid _),
        action2_invol (hom1.valid _), action1_invol (hom2.valid _), action2_invol ha]
  · change action1 (action2 (action1 (action2 (action1 (action2 (action1 (action2 (action1 (action2 (action1 (action2 a))))))))))) = a
    rw [action11_swap]
    rw [action1_invol (hom2.valid _), action2_invol (hom1.valid _),
        action1_invol (hom2.valid _), action2_invol (hom1.valid _),
        action1_invol (hom2.valid _), action2_invol ha]
lemma invG_inv (g : Fin 12) : invG (invG g) = g := by fin_cases g <;> rfl
lemma action_inj {g : Fin 12} {a b : Sig} (ha : Valid a) (hb : Valid b)
    (he : action g a = action g b) : a = b := by
  have := congrArg (action (invG g)) he
  rwa [action_inv g ha, action_inv g hb] at this
lemma action_proper (g : Fin 12) {a : Sig} (ha : proper a) : proper (action g a) := by
  refine ⟨action_valid g a, ?_, ?_⟩
  · intro h0; exact ha.2.1 (action_inj ha.1 valid_zero (h0.trans (action_zero g).symm))
  · intro h1; exact ha.2.2 (action_inj ha.1 valid_one (h1.trans (action_one g).symm))
def rawImage (g : Fin 12) (i : Fin 9) : Sig :=
  raw.getD ((rawPermCodes g >>> (4 * i.val)) &&& 15) zero
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma raw1_eq : ∀ i : Fin 9, raw.getD (perm1 i) zero = action1 (raw.getD i.val zero) := by
  decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma raw2_eq : ∀ i : Fin 9, raw.getD (perm2 i) zero = action2 (raw.getD i.val zero) := by
  decide +kernel
def p1 (i : Fin 9) : Fin 9 := Fin.ofNat 9 (perm1 i)
def p2 (i : Fin 9) : Fin 9 := Fin.ofNat 9 (perm2 i)
lemma rawImage_eq (g : Fin 12) (i : Fin 9) : rawImage g i = action g (raw.getD i.val zero) := by
  have h1 : ∀ j : Fin 9, hom1.fn (raw.getD j.val zero) = raw.getD (p1 j).val zero := fun j =>
    (raw1_eq j).symm.trans (by fin_cases j <;> rfl)
  have h2 : ∀ j : Fin 9, hom2.fn (raw.getD j.val zero) = raw.getD (p2 j).val zero := fun j =>
    (raw2_eq j).symm.trans (by fin_cases j <;> rfl)
  fin_cases g
  · have hr0 : rawImage ⟨0, by decide⟩ i = raw.getD i.val zero := by
      unfold rawImage; apply congrArg (fun k => raw.getD k zero); revert i; decide
    exact hr0.trans (action0_eq (valid_getD raw_valid i.val)).symm
  all_goals
    dsimp only [action, homG, compHom]
    simp only [h1, h2]
    unfold rawImage
    apply congrArg (fun k => raw.getD k zero)
    revert i; decide
lemma rawImage_mem (g : Fin 12) (i : Fin 9) : rawImage g i ∈ raw := by
  fin_cases g <;> fin_cases i <;> simp [rawImage, rawPermCodes, raw]
lemma action_raw_subset (g : Fin 12) : raw.toFinset.image (action g) ⊆ raw.toFinset := by
  intro a ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp ha
  rw [List.mem_toFinset] at hb ⊢
  have hex : ∃ i : Fin 9, raw.getD i.val zero = b := by
    simp only [raw, List.mem_cons, List.not_mem_nil, or_false] at hb
    rcases hb with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩
    · exact ⟨6, rfl⟩
    · exact ⟨7, rfl⟩
    · exact ⟨8, rfl⟩
  obtain ⟨i, rfl⟩ := hex
  rw [← rawImage_eq g i]
  exact rawImage_mem g i
def Feasible (H : SigHom) (k : Nat) (S : Finset Sig) : Prop :=
  ∃ m ≤ k, ∃ t T, Live m t T ∧ T ⊆ S.image H.fn
lemma feasible_mono {H : SigHom} {k k' : Nat} {S : Finset Sig}
    (h : Feasible H k S) (hk : k ≤ k') : Feasible H k' S := by
  obtain ⟨m, hm, t, T, hl, hs⟩ := h; exact ⟨m, hm.trans hk, t, T, hl, hs⟩
lemma feasible_subset {H : SigHom} {k : Nat} {S S' : Finset Sig}
    (h : Feasible H k S) (hsub : S.image H.fn ⊆ S'.image H.fn) : Feasible H k S' := by
  obtain ⟨m, hm, t, T, hl, hs⟩ := h; exact ⟨m, hm, t, T, hl, hs.trans hsub⟩
lemma neg_rep (w : List Sig) {a : Sig} (hva : Valid a) (ha : a ∈ w) :
    represented w (neg a) ∨ witness w (neg a) := by
  rcases operand_cases hva (Or.inl ha : represented w a) with rfl | rfl | ⟨hm, hp⟩
  · exact Or.inl (Or.inr (fun hh => hh.2.2 neg_laws.1))
  · exact Or.inl (Or.inr (fun hh => hh.2.1 neg_laws.2))
  · exact Or.inr (Or.inl ⟨a, hm, hp, rfl⟩)
lemma feasible_pull {H : SigHom} {q : Nat} {S S' : Finset Sig} {g : Sig}
    (hs : S' ⊆ insert g S)
    (hr : represented (S.image H.fn).toList (H.fn g) ∨ witness (S.image H.fn).toList (H.fn g))
    (h : Feasible H q S') : Feasible H (q + 1) S := by
  obtain ⟨m, hm, t, T, hl, ht⟩ := h
  have sub : ∀ a ∈ T, a ∈ (S.image H.fn).toList ++ [H.fn g] := by
    intro a ha
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (ht ha)
    rcases Finset.mem_insert.mp (hs hb) with rfl | hb
    · simp
    · exact List.mem_append_left _ (Finset.mem_toList.mpr (Finset.mem_image_of_mem _ hb))
  obtain ⟨m', t', T', hm', h', hT'⟩ := pull_gate hl hr sub
  exact ⟨m', by omega, t', T', h', fun a ha => Finset.mem_toList.mp (hT' _ ha)⟩
lemma feasible_free {H : SigHom} {q : Nat} {S S' : Finset Sig} {g : Sig}
    (hs : S' ⊆ insert g S)
    (hr : represented (S.image H.fn).toList (H.fn g))
    (h : Feasible H q S') : Feasible H q S := by
  obtain ⟨m, hm, t, T, hl, ht⟩ := h
  refine ⟨m, hm, t, T, hl, ?_⟩
  intro a ha
  obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp (ht ha)
  rcases Finset.mem_insert.mp (hs hb) with rfl | hb
  · exact Finset.mem_toList.mp (hr.resolve_right (fun hp => hp (live_proper hl _ ha)))
  · exact Finset.mem_image_of_mem _ hb
lemma pull_unary {H : SigHom} {q : Nat} {a : Sig} {U : Finset Sig} (hva : Valid a)
    (h : Feasible H q (insert (neg a) U)) : Feasible H (q + 1) (insert a U) := by
  apply feasible_pull (g := neg a) (by intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx <;> simp [hx]) _ h
  rw [H.hneg hva]
  exact neg_rep _ (H.valid a) (by simp)
lemma pull_binary {H : SigHom} {q : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (h : Feasible H q (insert (bin d a b) U)) : Feasible H (q + 1) (insert a (insert b U)) := by
  apply feasible_pull (g := bin d a b) (by intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx <;> simp [hx]) _ h
  rw [H.hbin]
  exact bin_rep _ (H.valid a) (H.valid b) (Or.inl (by simp)) (Or.inl (by simp))
lemma free_unary {H : SigHom} {q : Nat} {a : Sig} {U : Finset Sig} (hva : Valid a)
    (ha : ¬ proper (H.fn a)) (h : Feasible H q (insert (neg a) U)) :
    Feasible H q (insert a U) := by
  apply feasible_free (g := neg a) (by intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx <;> simp [hx]) _ h
  rcases operand_cases (H.valid a) (Or.inr ha : represented [] (H.fn a)) with hz | ho | hm
  · exact Or.inr (fun hp => hp.2.2 (by rw [H.hneg hva, hz, neg_laws.1]))
  · exact Or.inr (fun hp => hp.2.1 (by rw [H.hneg hva, ho, neg_laws.2]))
  · simp at hm
lemma free_binary_left {H : SigHom} {q : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (ha : ¬ proper (H.fn a)) (h : Feasible H q (insert (bin d a b) U)) :
    Feasible H q (insert a (insert b U)) := by
  apply feasible_free (g := bin d a b) (by intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx <;> simp [hx]) _ h
  rw [H.hbin, bin_comm]
  rcases operand_cases (H.valid a) (Or.inr ha : represented [] (H.fn a)) with hz | ho | hm
  · rw [hz]
    cases d
    · exact Or.inr (fun hp => hp.2.1 (bin_laws (H.valid b)).2.2.1)
    · rw [(bin_laws (H.valid b)).2.1]; exact Or.inl (by simp)
  · rw [ho]
    cases d
    · rw [(bin_laws (H.valid b)).1]; exact Or.inl (by simp)
    · exact Or.inr (fun hp => hp.2.2 (bin_laws (H.valid b)).2.2.2.1)
  · simp at hm
lemma free_binary_right {H : SigHom} {q : Nat} {a b : Sig} {d : Bool} {U : Finset Sig}
    (hb : ¬ proper (H.fn b)) (h : Feasible H q (insert (bin d a b) U)) :
    Feasible H q (insert a (insert b U)) := by
  rw [bin_comm] at h
  rw [Finset.insert_comm]
  exact free_binary_left hb h
lemma feasible_live {k t : Nat} {S : Finset Sig} (h : Live k t S) (H : SigHom) :
    Feasible H k S := by
  induction h with
  | stop => refine ⟨0, Nat.le_refl _, 0, {target}, Live.stop, ?_⟩; simp [H.htarget]
  | unary ha _ _ ih => exact pull_unary ha.1 ih
  | binary _ _ _ _ _ ih => exact pull_binary ih
lemma feasible_const {k t : Nat} {S : Finset Sig} (h : Live k t S) (H : SigHom)
    (a : Sig) (ha : a ∈ S) (hc : ¬ proper (H.fn a)) :
    ∃ q < k, Feasible H q S := by
  induction h with
  | stop =>
    have ht : a = target := Finset.mem_singleton.mp ha
    exact (hc (by rw [ht, H.htarget]; exact target_proper)).elim
  | @unary k t U b hp _ tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact ⟨k, by omega, free_unary hp.1 hc (feasible_live tail H)⟩
    · obtain ⟨q, hq, h⟩ := ih (Finset.mem_insert_of_mem ha)
      exact ⟨q + 1, by omega, pull_unary hp.1 h⟩
  | @binary k t U b c d _ _ _ _ tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | hU
    · exact ⟨k, by omega, free_binary_left hc (feasible_live tail H)⟩
    · rcases Finset.mem_insert.mp hU with rfl | hU
      · exact ⟨k, by omega, free_binary_right hc (feasible_live tail H)⟩
      · obtain ⟨q, hq, h⟩ := ih (Finset.mem_insert_of_mem hU)
        exact ⟨q + 1, by omega, pull_binary h⟩
lemma not_proper_bin_consts {H : SigHom} {a b : Sig} (d : Bool)
    (hca : ¬ proper (H.fn a)) (hcb : ¬ proper (H.fn b)) :
    ¬ proper (H.fn (bin d a b)) := by
  rw [H.hbin]
  rcases operand_cases (H.valid a) (Or.inr hca : represented [] (H.fn a)) with ha0 | ha1 | hm
  · rw [ha0, bin_comm]
    rcases operand_cases (H.valid b) (Or.inr hcb : represented [] (H.fn b)) with hb0 | hb1 | hm'
    · rw [hb0]; cases d
      · exact fun hp => hp.2.1 (bin_laws valid_zero).2.2.1
      · exact fun hp => hp.2.1 (bin_laws valid_zero).2.1
    · rw [hb1]; cases d
      · exact fun hp => hp.2.1 (bin_laws valid_one).2.2.1
      · exact fun hp => hp.2.2 (bin_laws valid_one).2.1
    · simp at hm'
  · rw [ha1, bin_comm]
    rcases operand_cases (H.valid b) (Or.inr hcb : represented [] (H.fn b)) with hb0 | hb1 | hm'
    · rw [hb0]; cases d
      · exact fun hp => hp.2.1 (bin_laws valid_zero).1
      · exact fun hp => hp.2.2 (bin_laws valid_zero).2.2.2.1
    · rw [hb1]; cases d
      · exact fun hp => hp.2.2 (bin_laws valid_one).1
      · exact fun hp => hp.2.2 (bin_laws valid_one).2.2.2.1
    · simp at hm'
  · simp at hm
lemma feasible_two_consts {k t : Nat} {S : Finset Sig} (h : Live k t S) (H : SigHom)
    (a b : Sig) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (hca : ¬ proper (H.fn a)) (hcb : ¬ proper (H.fn b)) :
    ∃ q, q + 2 ≤ k ∧ Feasible H q S := by
  induction h with
  | stop =>
    have e1 := Finset.mem_singleton.mp ha
    have e2 := Finset.mem_singleton.mp hb
    exact (hab (e1.trans e2.symm)).elim
  | @unary k t U c hpc _ tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | haU
    · have hbU : b ∈ U := (Finset.mem_insert.mp hb).resolve_left hab.symm
      obtain ⟨q, hq, hf⟩ := feasible_const tail H b (Finset.mem_insert_of_mem hbU) hcb
      exact ⟨q, by omega, free_unary hpc.1 hca hf⟩
    · rcases Finset.mem_insert.mp hb with rfl | hbU
      · obtain ⟨q, hq, hf⟩ := feasible_const tail H a (Finset.mem_insert_of_mem haU) hca
        exact ⟨q, by omega, free_unary hpc.1 hcb hf⟩
      · obtain ⟨q, hq, hf⟩ := ih (Finset.mem_insert_of_mem haU) (Finset.mem_insert_of_mem hbU)
        exact ⟨q + 1, by omega, pull_unary hpc.1 hf⟩
  | @binary k t U c e d _ _ _ _ tail ih =>
    rcases Finset.mem_insert.mp ha with rfl | ha1
    · rcases Finset.mem_insert.mp hb with hbEq | hb1
      · exact (hab hbEq.symm).elim
      · rcases Finset.mem_insert.mp hb1 with rfl | hbU
        · obtain ⟨q, hq, hf⟩ := feasible_const tail H (bin d a b) (Finset.mem_insert_self _ _)
            (not_proper_bin_consts d hca hcb)
          exact ⟨q, by omega, free_binary_left hca hf⟩
        · obtain ⟨q, hq, hf⟩ := feasible_const tail H b (Finset.mem_insert_of_mem hbU) hcb
          exact ⟨q, by omega, free_binary_left hca hf⟩
    · rcases Finset.mem_insert.mp ha1 with rfl | haU
      · rcases Finset.mem_insert.mp hb with rfl | hb1
        · obtain ⟨q, hq, hf⟩ := feasible_const tail H (bin d b a) (Finset.mem_insert_self _ _)
            (not_proper_bin_consts d hcb hca)
          exact ⟨q, by omega, free_binary_left hcb hf⟩
        · rcases Finset.mem_insert.mp hb1 with hbEq | hbU
          · exact (hab hbEq.symm).elim
          · obtain ⟨q, hq, hf⟩ := feasible_const tail H b (Finset.mem_insert_of_mem hbU) hcb
            exact ⟨q, by omega, free_binary_right hca hf⟩
      · rcases Finset.mem_insert.mp hb with rfl | hb1
        · obtain ⟨q, hq, hf⟩ := feasible_const tail H a (Finset.mem_insert_of_mem haU) hca
          exact ⟨q, by omega, free_binary_left hcb hf⟩
        · rcases Finset.mem_insert.mp hb1 with rfl | hbU
          · obtain ⟨q, hq, hf⟩ := feasible_const tail H a (Finset.mem_insert_of_mem haU) hca
            exact ⟨q, by omega, free_binary_right hcb hf⟩
          · obtain ⟨q, hq, hf⟩ := ih (Finset.mem_insert_of_mem haU) (Finset.mem_insert_of_mem hbU)
            exact ⟨q + 1, by omega, pull_binary hf⟩
def posIdx4 (j : Fin 414) : Fin 414 :=
  Fin.ofNat 414 (index9 posKey4 (if j.val < 252 then j.val else 0))
def negIdx4 (j : Fin 414) : Fin 414 :=
  Fin.ofNat 414 (index9 negKey4 (if j.val < 252 then j.val else 0))
def homProject4 : SigHom := pairHom posIdx4 negIdx4
abbrev project4 (a : Sig) : Sig := homProject4.fn a
def posIdx0 (j : Fin 414) : Fin 414 :=
  Fin.ofNat 414 (index9 posKey0 (if j.val < 232 then j.val else 232))
def negIdx0 (j : Fin 414) : Fin 414 :=
  Fin.ofNat 414 (index9 negKey0 (if j.val < 232 then j.val else 232))
def homProject0 : SigHom := pairHom posIdx0 negIdx0
abbrev project0 (a : Sig) : Sig := homProject0.fn a
def leafIdx (j : Fin 414) : Fin 414 :=
  if h : j.val < 232 then ⟨j.val, by omega⟩ else ⟨0, by omega⟩
def homProjectLeaf : SigHom := pairHom leafIdx leafIdx
abbrev projectLeaf (a : Sig) : Sig := homProjectLeaf.fn a
def homProject (i : Fin 9) : SigHom :=
  if i.val = 4 ∨ i.val = 6 ∨ i.val = 7 then compHom homProject4 (homG (gOfV i))
  else compHom homProject0 (homG (gOfV i))
abbrev project (i : Fin 9) (a : Sig) : Sig := (homProject i).fn a

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma project4_raw4 : homProject4.fn raw4 = zero := by decide +kernel
def raw1007Order : List Sig := [raw0, raw1, raw2, raw3, raw5, raw6, raw7, raw8]

def thetaOrder : List Sig := [raw2, raw8, raw3, raw1, raw6, raw7, raw5]
def thetaInputs : List Sig := thetaOrder.map (fun a => projectLeaf (project0 a))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma project0_raw0 : project0 raw0 = zero := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma projectLeaf_project0_raw4 : projectLeaf (project0 raw4) = zero := by decide +kernel

lemma project_raw_zero (i : Fin 9) : (homProject i).fn (raw.getD i.val zero) = zero := by
  have hact : ∀ g : Fin 12, (homG g).fn (raw.getD i.val zero) = rawImage g i :=
    fun g => (rawImage_eq g i).symm
  fin_cases i
  · change project0 ((homG (gOfV 0)).fn (raw.getD 0 zero)) = zero; rw [hact]; exact project0_raw0
  · change project0 ((homG (gOfV 1)).fn (raw.getD 1 zero)) = zero; rw [hact]; exact project0_raw0
  · change project0 ((homG (gOfV 2)).fn (raw.getD 2 zero)) = zero; rw [hact]; exact project0_raw0
  · change project0 ((homG (gOfV 3)).fn (raw.getD 3 zero)) = zero; rw [hact]; exact project0_raw0
  · change homProject4.fn ((homG (gOfV 4)).fn (raw.getD 4 zero)) = zero; rw [hact]; exact project4_raw4
  · change project0 ((homG (gOfV 5)).fn (raw.getD 5 zero)) = zero; rw [hact]; exact project0_raw0
  · change homProject4.fn ((homG (gOfV 6)).fn (raw.getD 6 zero)) = zero; rw [hact]; exact project4_raw4
  · change homProject4.fn ((homG (gOfV 7)).fn (raw.getD 7 zero)) = zero; rw [hact]; exact project4_raw4
  · change project0 ((homG (gOfV 8)).fn (raw.getD 8 zero)) = zero; rw [hact]; exact project0_raw0
inductive Tag where
  | tNone
  | tDeg3
  | tSpec0
  | tSpec1
  deriving DecidableEq, BEq
instance : LawfulBEq Tag where
  eq_of_beq {a b} h := by cases a <;> cases b <;> first | rfl | contradiction
  rfl {a} := by cases a <;> rfl
abbrev Wire := Sig × Tag
def Tag.toNat : Tag → Nat
  | .tNone => 0
  | .tDeg3 => 1
  | .tSpec0 => 2
  | .tSpec1 => 3
def tagOfNat : Nat → Tag
  | 0 => .tNone
  | 1 => .tDeg3
  | 2 => .tSpec0
  | _ => .tSpec1
def Tight (i : Fin 9) (k : Nat) (S : Finset Sig) : Prop :=
  ∀ q, q + 1 < k → ¬ Feasible (homProject i) q S
def Slack (i : Fin 9) (k : Nat) (S : Finset Sig) : Prop :=
  ∀ q, q + 2 < k → ¬ Feasible (homProject i) q S
def WireTagOk (k : Nat) (S : Finset Sig) (a : Sig) : Tag → Prop
  | .tNone => True
  | .tDeg3 => ∃ i : Fin 9, (homProject i).fn a = zero ∧ Slack i k S
  | .tSpec0 => ∃ i : Fin 9, (homProject i).fn a = zero ∧ Tight i k S
  | .tSpec1 => ∃ i : Fin 9, (homProject i).fn a = one ∧ Tight i k S
def TagOk (k : Nat) (S : Finset Sig) (τ : Sig → Tag) : Prop :=
  ∀ a ∈ S, WireTagOk k S a (τ a)
def updUnaryTag (τ : Sig → Tag) (a : Sig) (x : Sig) : Tag :=
  if x = neg a then (if τ a = .tDeg3 then .tSpec1 else .tNone) else τ x
def updAndTag (τ : Sig → Tag) (a b : Sig) (x : Sig) : Tag :=
  if x = bin false a b then (if τ a = .tDeg3 ∨ τ b = .tDeg3 then .tSpec0 else .tNone) else τ x
def updOrTag (τ : Sig → Tag) (a b : Sig) (x : Sig) : Tag :=
  if x = bin true a b then .tNone
  else if x = a ∧ τ a = .tDeg3 then .tSpec0
  else if x = b ∧ τ b = .tDeg3 then .tSpec0
  else τ x
inductive TRestricted : Nat → Nat → Finset Sig → (Sig → Tag) → Prop
  | stop {τ} : TRestricted 0 0 {target} τ
  | unary {k t : Nat} {U : Finset Sig} {a : Sig} {τ : Sig → Tag}
      (ha : proper a) (hf : neg a ∉ insert a U)
      (hr1 : τ a ≠ .tSpec0 ∧ τ a ≠ .tSpec1)
      (hr2 : τ a = .tDeg3 → a ∉ U)
      (tail : TRestricted k t (insert (neg a) U) (updUnaryTag τ a)) :
      TRestricted (k + 1) (t + 1) (insert a U) τ
  | binaryAnd {k t : Nat} {U : Finset Sig} {a b : Sig} {τ : Sig → Tag}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hf : bin false a b ∉ insert a (insert b U))
      (hra : τ a ≠ .tSpec0 ∧ (τ a ≠ .tNone → a ∉ U))
      (hrb : τ b ≠ .tSpec0 ∧ (τ b ≠ .tNone → b ∉ U))
      (tail : TRestricted k t (insert (bin false a b) U) (updAndTag τ a b)) :
      TRestricted (k + 1) t (insert a (insert b U)) τ
  | binaryOr {k t : Nat} {U : Finset Sig} {a b : Sig} {τ : Sig → Tag}
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hf : bin true a b ∉ insert a (insert b U))
      (hra : τ a ≠ .tSpec1 ∧ (τ a = .tSpec0 → a ∉ U))
      (hrb : τ b ≠ .tSpec1 ∧ (τ b = .tSpec0 → b ∉ U))
      (tail : TRestricted k t (insert (bin true a b) U) (updOrTag τ a b)) :
      TRestricted (k + 1) t (insert a (insert b U)) τ
lemma TRestricted.live {k t S τ} (h : TRestricted k t S τ) : Live k t S := by
  induction h with
  | stop => exact Live.stop
  | unary ha hf _ _ _ ih => exact Live.unary ha hf ih
  | binaryAnd ha hb hab hf _ _ _ ih => exact Live.binary ha hb hab hf ih
  | binaryOr ha hb hab hf _ _ _ ih => exact Live.binary ha hb hab hf ih
lemma wireTagOk_unary_step {k : Nat} {U : Finset Sig} {a x : Sig} {tg : Tag} (hva : Valid a)
    (h : WireTagOk (k + 1) (insert a U) x tg) : WireTagOk k (insert (neg a) U) x tg := by
  cases tg with
  | tNone => trivial
  | tDeg3 =>
    obtain ⟨i, hp, hs⟩ := h
    exact ⟨i, hp, fun q hq hf => hs (q + 1) (by omega) (pull_unary hva hf)⟩
  | tSpec0 =>
    obtain ⟨i, hp, ht⟩ := h
    exact ⟨i, hp, fun q hq hf => ht (q + 1) (by omega) (pull_unary hva hf)⟩
  | tSpec1 =>
    obtain ⟨i, hp, ht⟩ := h
    exact ⟨i, hp, fun q hq hf => ht (q + 1) (by omega) (pull_unary hva hf)⟩
lemma wireTagOk_binary_step {k : Nat} {U : Finset Sig} {a b x : Sig} {d : Bool} {tg : Tag}
    (h : WireTagOk (k + 1) (insert a (insert b U)) x tg) :
    WireTagOk k (insert (bin d a b) U) x tg := by
  cases tg with
  | tNone => trivial
  | tDeg3 =>
    obtain ⟨i, hp, hs⟩ := h
    exact ⟨i, hp, fun q hq hf => hs (q + 1) (by omega) (pull_binary hf)⟩
  | tSpec0 =>
    obtain ⟨i, hp, ht⟩ := h
    exact ⟨i, hp, fun q hq hf => ht (q + 1) (by omega) (pull_binary hf)⟩
  | tSpec1 =>
    obtain ⟨i, hp, ht⟩ := h
    exact ⟨i, hp, fun q hq hf => ht (q + 1) (by omega) (pull_binary hf)⟩
lemma restrict_live {k t S τ} (h : Live k t S) (ht : TagOk k S τ) : TRestricted k t S τ := by
  induction h generalizing τ with
  | stop => exact TRestricted.stop
  | @unary k t U a ha hf tail ih =>
    have hta := ht a (Finset.mem_insert_self _ _)
    have hr1 : τ a ≠ .tSpec0 ∧ τ a ≠ .tSpec1 := by
      constructor <;> intro heq <;> rw [heq] at hta
      · obtain ⟨i, hp0, hti⟩ := hta
        have hz : ¬ proper ((homProject i).fn a) := fun hp => hp.2.1 hp0
        have ho : ¬ proper ((homProject i).fn (neg a)) := fun hp =>
          hp.2.2 (by rw [(homProject i).hneg ha.1, hp0, neg_laws.1])
        obtain ⟨q, hq, hfe⟩ := feasible_const tail (homProject i) (neg a) (Finset.mem_insert_self _ _) ho
        exact hti q (by omega) (free_unary ha.1 hz hfe)
      · obtain ⟨i, hp1, hti⟩ := hta
        have ho : ¬ proper ((homProject i).fn a) := fun hp => hp.2.2 hp1
        have hz : ¬ proper ((homProject i).fn (neg a)) := fun hp =>
          hp.2.1 (by rw [(homProject i).hneg ha.1, hp1, neg_laws.2])
        obtain ⟨q, hq, hfe⟩ := feasible_const tail (homProject i) (neg a) (Finset.mem_insert_self _ _) hz
        exact hti q (by omega) (free_unary ha.1 ho hfe)
    have hr2 : τ a = .tDeg3 → a ∉ U := by
      intro heq haU
      rw [heq] at hta
      obtain ⟨i, hp0, hsl⟩ := hta
      have hz : ¬ proper ((homProject i).fn a) := fun hp => hp.2.1 hp0
      have ho : ¬ proper ((homProject i).fn (neg a)) := fun hp =>
        hp.2.2 (by rw [(homProject i).hneg ha.1, hp0, neg_laws.1])
      have hne : neg a ≠ a := fun e => by rw [e] at hf; exact hf (Finset.mem_insert_self _ _)
      obtain ⟨q, hq, hfe⟩ := feasible_two_consts tail (homProject i) (neg a) a
        (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem haU) hne ho hz
      exact hsl q (by omega) (free_unary ha.1 hz hfe)
    have ht' : TagOk k (insert (neg a) U) (updUnaryTag τ a) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxU
      · unfold updUnaryTag; simp only [ite_true]
        split
        · rename_i hd3
          rw [hd3] at hta
          obtain ⟨i, hp0, hsl⟩ := hta
          have hz : ¬ proper ((homProject i).fn a) := fun hp => hp.2.1 hp0
          refine ⟨i, by rw [(homProject i).hneg ha.1, hp0]; exact neg_laws.1, ?_⟩
          intro q hq hfe; exact hsl q (by omega) (free_unary ha.1 hz hfe)
        · trivial
      · have hne : x ≠ neg a := fun e => hf (e ▸ Finset.mem_insert_of_mem hxU)
        unfold updUnaryTag; simp only [hne, ite_false]
        exact wireTagOk_unary_step ha.1 (ht x (Finset.mem_insert_of_mem hxU))
    exact TRestricted.unary ha hf hr1 hr2 (ih ht')
  | @binary k t U a b d ha hb hab hf tail ih =>
    have hta := ht a (Finset.mem_insert_self _ _)
    have htb := ht b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    cases d with
    | false =>
      have sideAnd : ∀ {x y : Sig} (hx : Valid x) (hy : Valid y) (hxy : x ≠ y)
          (hfx : bin false x y ∉ insert x (insert y U))
          (tail' : Live k t (insert (bin false x y) U))
          (htx : WireTagOk (k + 1) (insert x (insert y U)) x (τ x)),
          τ x ≠ .tSpec0 ∧ (τ x ≠ .tNone → x ∉ U) := by
        intro x y _ _ _ hfx tail' htx
        constructor
        · intro heq; rw [heq] at htx
          obtain ⟨i, hp0, hti⟩ := htx
          have hz : ¬ proper ((homProject i).fn x) := fun hp => hp.2.1 hp0
          have hg0 : ¬ proper ((homProject i).fn (bin false x y)) := fun hp =>
            hp.2.1 (by rw [(homProject i).hbin, hp0, bin_comm]; exact (bin_laws ((homProject i).valid y)).2.2.1)
          obtain ⟨q, hq, hfe⟩ := feasible_const tail' (homProject i) (bin false x y) (Finset.mem_insert_self _ _) hg0
          exact hti q (by omega) (free_binary_left hz hfe)
        · intro hne hxU
          cases htxc : τ x with
          | tNone => exact hne htxc
          | tSpec0 =>
            rw [htxc] at htx
            obtain ⟨i, hp0, hti⟩ := htx
            have hz : ¬ proper ((homProject i).fn x) := fun hp => hp.2.1 hp0
            obtain ⟨q, hq, hfe⟩ := feasible_const tail' (homProject i) x (Finset.mem_insert_of_mem hxU) hz
            exact hti q (by omega) (free_binary_left hz hfe)
          | tSpec1 =>
            rw [htxc] at htx
            obtain ⟨i, hp1, hti⟩ := htx
            have ho : ¬ proper ((homProject i).fn x) := fun hp => hp.2.2 hp1
            obtain ⟨q, hq, hfe⟩ := feasible_const tail' (homProject i) x (Finset.mem_insert_of_mem hxU) ho
            exact hti q (by omega) (free_binary_left ho hfe)
          | tDeg3 =>
            rw [htxc] at htx
            obtain ⟨i, hp0, hsl⟩ := htx
            have hz : ¬ proper ((homProject i).fn x) := fun hp => hp.2.1 hp0
            have hg0 : ¬ proper ((homProject i).fn (bin false x y)) := fun hp =>
              hp.2.1 (by rw [(homProject i).hbin, hp0, bin_comm]; exact (bin_laws ((homProject i).valid y)).2.2.1)
            have hne' : bin false x y ≠ x := fun e => by rw [e] at hfx; exact hfx (Finset.mem_insert_self _ _)
            obtain ⟨q, hq, hfe⟩ := feasible_two_consts tail' (homProject i) (bin false x y) x
              (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hxU) hne' hg0 hz
            exact hsl q (by omega) (free_binary_left hz hfe)
      have hra := sideAnd ha.1 hb.1 hab hf tail hta
      have hrb : τ b ≠ .tSpec0 ∧ (τ b ≠ .tNone → b ∉ U) :=
        sideAnd hb.1 ha.1 hab.symm (by rwa [bin_comm, Finset.insert_comm])
          (by rwa [bin_comm]) (by rwa [Finset.insert_comm])
      have ht' : TagOk k (insert (bin false a b) U) (updAndTag τ a b) := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxU
        · unfold updAndTag; simp only [ite_true]
          split
          · rename_i hd
            rcases hd with hda | hdb
            · rw [hda] at hta
              obtain ⟨i, hp0, hsl⟩ := hta
              have hz : ¬ proper ((homProject i).fn a) := fun hp => hp.2.1 hp0
              refine ⟨i, by rw [(homProject i).hbin, hp0, bin_comm]; exact (bin_laws ((homProject i).valid b)).2.2.1, ?_⟩
              intro q hq hfe; exact hsl q (by omega) (free_binary_left hz hfe)
            · rw [hdb] at htb
              obtain ⟨i, hp0, hsl⟩ := htb
              have hz : ¬ proper ((homProject i).fn b) := fun hp => hp.2.1 hp0
              refine ⟨i, by rw [(homProject i).hbin, hp0]; exact (bin_laws ((homProject i).valid a)).2.2.1, ?_⟩
              intro q hq hfe; exact hsl q (by omega) (free_binary_right hz hfe)
          · trivial
        · have hne : x ≠ bin false a b := fun e => hf (e ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU))
          unfold updAndTag; simp only [hne, ite_false]
          exact wireTagOk_binary_step (ht x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU)))
      exact TRestricted.binaryAnd ha hb hab hf hra hrb (ih ht')
    | true =>
      have sideOr : ∀ {x y : Sig}
          (tail' : Live k t (insert (bin true x y) U))
          (htx : WireTagOk (k + 1) (insert x (insert y U)) x (τ x)),
          τ x ≠ .tSpec1 ∧ (τ x = .tSpec0 → x ∉ U) := by
        intro x y tail' htx
        constructor
        · intro heq; rw [heq] at htx
          obtain ⟨i, hp1, hti⟩ := htx
          have ho : ¬ proper ((homProject i).fn x) := fun hp => hp.2.2 hp1
          have hg1 : ¬ proper ((homProject i).fn (bin true x y)) := fun hp =>
            hp.2.2 (by rw [(homProject i).hbin, hp1, bin_comm]; exact (bin_laws ((homProject i).valid y)).2.2.2.1)
          obtain ⟨q, hq, hfe⟩ := feasible_const tail' (homProject i) (bin true x y) (Finset.mem_insert_self _ _) hg1
          exact hti q (by omega) (free_binary_left ho hfe)
        · intro heq hxU; rw [heq] at htx
          obtain ⟨i, hp0, hti⟩ := htx
          have hz : ¬ proper ((homProject i).fn x) := fun hp => hp.2.1 hp0
          obtain ⟨q, hq, hfe⟩ := feasible_const tail' (homProject i) x (Finset.mem_insert_of_mem hxU) hz
          exact hti q (by omega) (free_binary_left hz hfe)
      have hra := sideOr tail hta
      have hrb : τ b ≠ .tSpec1 ∧ (τ b = .tSpec0 → b ∉ U) :=
        sideOr (by rwa [bin_comm]) (by rwa [Finset.insert_comm])
      have ht' : TagOk k (insert (bin true a b) U) (updOrTag τ a b) := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxU
        · unfold updOrTag; simp only [ite_true]; trivial
        · have hne : x ≠ bin true a b := fun e => hf (e ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU))
          unfold updOrTag; simp only [hne, ite_false]
          by_cases hxa : x = a ∧ τ a = .tDeg3
          · simp only [hxa]
            obtain ⟨rfl, hd3⟩ := hxa
            rw [hd3] at hta
            obtain ⟨i, hp0, hsl⟩ := hta
            have hz : ¬ proper ((homProject i).fn x) := fun hp => hp.2.1 hp0
            refine ⟨i, hp0, fun q hq hfe => hsl q (by omega) (free_binary_left hz hfe)⟩
          · simp only [hxa, ite_false]
            by_cases hxb : x = b ∧ τ b = .tDeg3
            · simp only [hxb]
              obtain ⟨rfl, hd3⟩ := hxb
              rw [hd3] at htb
              obtain ⟨i, hp0, hsl⟩ := htb
              have hz : ¬ proper ((homProject i).fn x) := fun hp => hp.2.1 hp0
              refine ⟨i, hp0, fun q hq hfe => hsl q (by omega) (free_binary_right hz hfe)⟩
            · simp only [hxb, ite_false]
              exact wireTagOk_binary_step (ht x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU)))
      exact TRestricted.binaryOr ha hb hab hf hra hrb (ih ht')

def rootTag (a : Sig) : Tag :=
  if a = raw4 ∨ a = raw6 ∨ a = raw7 then .tSpec0
  else if a ∈ raw then .tDeg3
  else .tNone
def rootWires : List Wire :=
  [(raw0, .tDeg3), (raw1, .tDeg3), (raw2, .tDeg3), (raw3, .tDeg3),
   (raw4, .tSpec0), (raw5, .tDeg3), (raw6, .tSpec0), (raw7, .tSpec0), (raw8, .tDeg3)]

def sigsOf (v : List Wire) : List Sig := v.map Prod.fst
def Represents (v : List Wire) (S : Finset Sig) (τ : Sig → Tag) : Prop :=
  (sigsOf v).Nodup ∧ (sigsOf v).toFinset = S ∧ ∀ w ∈ v, w.2 = τ w.1
def droppedW (del : List Sig) (v : List Wire) : List Wire :=
  v.filter (fun w => !(del.contains w.1))
def unionSepW (d : Bool) : List Wire → Nat
  | [] => 0
  | w :: l => sep d w.1 ||| unionSepW d l
def coverageW (d : Bool) (v : List Wire) : Cov :=
  v.foldr (fun w c => covAdd (sep d w.1) c) (0, 0, 0)
lemma sigsOf_droppedW (del : List Sig) (v : List Wire) :
    sigsOf (droppedW del v) = dropped del (sigsOf v) := by
  induction v with
  | nil => rfl
  | cons w l ih =>
    unfold sigsOf droppedW dropped at ih ⊢
    simp only [List.map_cons, List.filter_cons]
    cases del.contains w.1
    · simp only [Bool.not_false, ite_true, List.map_cons, ih]
    · simp only [Bool.not_true, Bool.false_eq_true, ite_false, ih]
lemma unionSepW_eq (d : Bool) (v : List Wire) : unionSepW d v = unionSep d (sigsOf v) := by
  induction v with
  | nil => rfl
  | cons w l ih => simp [unionSepW, unionSep, sigsOf, ih]
lemma coverageW_eq (d : Bool) (v : List Wire) : coverageW d v = coverage d (sigsOf v) := by
  induction v with
  | nil => rfl
  | cons w l ih =>
    change covAdd (sep d w.1) (coverageW d l) = covAdd (sep d w.1) (coverage d (sigsOf l))
    rw [ih]
lemma sigsOf_length (v : List Wire) : (sigsOf v).length = v.length := List.length_map ..
lemma mem_sigsOf_iff {v : List Wire} {a : Sig} {τ : Sig → Tag}
    (ht : ∀ w ∈ v, w.2 = τ w.1) : (a, τ a) ∈ v ↔ a ∈ sigsOf v := by
  constructor
  · intro h; exact List.mem_map.mpr ⟨(a, τ a), h, rfl⟩
  · intro h; obtain ⟨w, hw, heq⟩ := List.mem_map.mp h
    have htag := ht w hw
    have : w = (a, τ a) := Prod.ext heq (by rw [htag, heq])
    rwa [← this]
def tagEq : Tag → Tag → Bool
  | .tNone, .tNone => true
  | .tDeg3, .tDeg3 => true
  | .tSpec0, .tSpec0 => true
  | .tSpec1, .tSpec1 => true
  | _, _ => false
lemma tagEq_iff {a b : Tag} : tagEq a b = true ↔ a = b := by
  cases a <;> cases b <;> simp [tagEq]
def isNotSpec0 : Tag → Bool | .tSpec0 => false | _ => true
def isNotSpec1 : Tag → Bool | .tSpec1 => false | _ => true
def isNoneTag : Tag → Bool | .tNone => true | _ => false
def isDeg3Tag : Tag → Bool | .tDeg3 => true | _ => false
def sigEq (a b : Sig) : Bool := Nat.beq a.1 b.1 && Nat.beq a.2 b.2
lemma sigEq_iff {a b : Sig} : sigEq a b = true ↔ a = b := by
  obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  simp only [sigEq, Bool.and_eq_true, Nat.beq_eq, Prod.mk.injEq]
lemma nat_beq_false {a b : Nat} (h : a ≠ b) : Nat.beq a b = false :=
  Bool.eq_false_iff.mpr fun e => h (Nat.beq_eq.mp e)
def gateAvail (g : Sig) : List Wire → Bool
  | [] => !sigEq g zero && !sigEq g one
  | w :: l => !sigEq w.1 g && gateAvail g l
lemma gateAvail_eq_true {v : List Wire} {g : Sig} (hg : g ∉ sigsOf v) (hp : proper g) :
    gateAvail g v = true := by
  induction v with
  | nil =>
    simp only [gateAvail, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, sigEq_iff]
    exact ⟨hp.2.1, hp.2.2⟩
  | cons w l ih =>
    simp only [sigsOf, List.map_cons, List.mem_cons, not_or] at hg
    simp only [gateAvail, Bool.and_eq_true, Bool.not_eq_true', Bool.eq_false_iff, ne_eq, sigEq_iff]
    exact ⟨Ne.symm hg.1, ih hg.2⟩
def dropOne (a : Sig) : List Wire → List Wire
  | [] => []
  | w :: l => if sigEq w.1 a then dropOne a l else w :: dropOne a l
lemma dropOne_eq (a : Sig) (v : List Wire) : dropOne a v = droppedW [a] v := by
  induction v with
  | nil => rfl
  | cons w l ih =>
    simp only [dropOne, droppedW, List.filter_cons, List.contains_eq_mem, List.mem_singleton, ih]
    by_cases h : w.1 = a
    · have hs : sigEq w.1 a = true := sigEq_iff.mpr h
      rw [hs]; simp [h]
    · have hs : sigEq w.1 a = false := Bool.eq_false_iff.mpr (fun e => h (sigEq_iff.mp e))
      rw [hs]; simp [h]
def dropTwo (a b : Sig) : List Wire → List Wire
  | [] => []
  | w :: l => if sigEq w.1 a || sigEq w.1 b then dropTwo a b l else w :: dropTwo a b l
lemma dropTwo_eq (a b : Sig) (v : List Wire) : dropTwo a b v = droppedW [a, b] v := by
  induction v with
  | nil => rfl
  | cons w l ih =>
    simp only [dropTwo, droppedW, List.filter_cons, List.contains_eq_mem, List.mem_cons,
      List.not_mem_nil, or_false, ih]
    by_cases h1 : w.1 = a
    · have hs1 : sigEq w.1 a = true := sigEq_iff.mpr h1
      rw [hs1]; simp [h1]
    · have hs1 : sigEq w.1 a = false := Bool.eq_false_iff.mpr (fun e => h1 (sigEq_iff.mp e))
      by_cases h2 : w.1 = b
      · have hs2 : sigEq w.1 b = true := sigEq_iff.mpr h2
        rw [hs1, hs2]; simp [h2]
      · have hs2 : sigEq w.1 b = false := Bool.eq_false_iff.mpr (fun e => h2 (sigEq_iff.mp e))
        rw [hs1, hs2]; simp [h1, h2]
def sep0 (a : Sig) : Nat := Nat.land a.1 (Nat.xor a.2 top)
def sep1 (a : Sig) : Nat := Nat.xor a.1 a.2
lemma sep0_eq (a : Sig) : sep0 a = sep false a := rfl
lemma sep1_eq (a : Sig) : sep1 a = sep true a := rfl
lemma bin_false_eq (a b : Sig) : bin false a b = (Nat.land a.1 b.1, Nat.land a.2 b.2) := rfl
lemma bin_true_eq (a b : Sig) : bin true a b = (Nat.lor a.1 b.1, Nat.lor a.2 b.2) := rfl
structure WSep where
  w : Wire
  p : Nat
  n : Nat
  tg : Tag
  s : Nat
def mkSep0 (w : Wire) : WSep := ⟨w, w.1.1, w.1.2, w.2, sep0 w.1⟩
def mkSep1 (w : Wire) : WSep := ⟨w, w.1.1, w.1.2, w.2, sep1 w.1⟩
def buildSeps0 : List Wire → List WSep × Cov
  | [] => ([], (0, 0, 0))
  | w :: l =>
    let (ls, c) := buildSeps0 l
    let s := sep0 w.1
    (⟨w, w.1.1, w.1.2, w.2, s⟩ :: ls, covAdd s c)
def buildSeps1 : List Wire → List WSep × Cov
  | [] => ([], (0, 0, 0))
  | w :: l =>
    let (ls, c) := buildSeps1 l
    let s := sep1 w.1
    (⟨w, w.1.1, w.1.2, w.2, s⟩ :: ls, covAdd s c)
lemma buildSeps0_eq (v : List Wire) : buildSeps0 v = (v.map mkSep0, coverageW false v) := by
  induction v with
  | nil => rfl
  | cons w l ih => simp only [buildSeps0, ih, List.map_cons, mkSep0]; rfl
lemma buildSeps1_eq (v : List Wire) : buildSeps1 v = (v.map mkSep1, coverageW true v) := by
  induction v with
  | nil => rfl
  | cons w l ih => simp only [buildSeps1, ih, List.map_cons, mkSep1]; rfl
structure WAct0 where
  w : Wire
  p : Nat
  n : Nat
  tg : Tag
  s : Nat
  u : Nat
def mkAct0 (uMask : Nat) (w : Wire) : WAct0 :=
  let s := sep0 w.1
  ⟨w, w.1.1, w.1.2, w.2, s, Nat.land uMask s⟩
def buildActs0 (uMask : Nat) : List WSep → List WAct0
  | [] => []
  | a :: l => ⟨a.w, a.p, a.n, a.tg, a.s, Nat.land uMask a.s⟩ :: buildActs0 uMask l
lemma buildActs0_map (uMask : Nat) (v : List Wire) :
    buildActs0 uMask (v.map mkSep0) = v.map (mkAct0 uMask) := by
  induction v with
  | nil => rfl
  | cons w l ih => simp only [List.map_cons, buildActs0, mkSep0, mkAct0, ih]
structure WAct1 where
  w : Wire
  p : Nat
  n : Nat
  tg : Tag
  s : Nat
  up : Nat
  un : Nat
def mkAct1 (uMask : Nat) (w : Wire) : WAct1 :=
  let s := sep1 w.1
  let u := Nat.land uMask s
  ⟨w, w.1.1, w.1.2, w.2, s, Nat.land u w.1.1, Nat.land u w.1.2⟩
def buildActs1 (uMask : Nat) : List WSep → List WAct1
  | [] => []
  | a :: l =>
    let u := Nat.land uMask a.s
    ⟨a.w, a.p, a.n, a.tg, a.s, Nat.land u a.p, Nat.land u a.n⟩ :: buildActs1 uMask l
lemma buildActs1_map (uMask : Nat) (v : List Wire) :
    buildActs1 uMask (v.map mkSep1) = v.map (mkAct1 uMask) := by
  induction v with
  | nil => rfl
  | cons w l ih => simp only [List.map_cons, buildActs1, mkSep1, mkAct1, ih]
def fastPair0 (r : List Wire → Bool) (v : List Wire) (c : Cov) (a b : WAct0) : Bool :=
  let tryAnd :=
    isNotSpec0 a.tg && isNotSpec0 b.tg &&
    Nat.beq (Nat.land a.u b.p) a.u && Nat.beq (Nat.land b.u a.p) b.u &&
    let gp := Nat.land a.p b.p
    let gn := Nat.land a.n b.n
    let g : Sig := (gp, gn)
    Nat.beq (Nat.lor (Nat.land gp (Nat.xor gn top)) (takeTwo c a.s b.s)) top &&
    gateAvail g v &&
    let gt := if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone
    r ((g, gt) :: dropTwo a.w.1 b.w.1 v)
  let tryOr :=
    isNotSpec1 a.tg && isNotSpec1 b.tg &&
    Nat.beq (Nat.land a.u b.n) 0 && Nat.beq (Nat.land b.u a.n) 0 &&
    let gp := Nat.lor a.p b.p
    let gn := Nat.lor a.n b.n
    let g : Sig := (gp, gn)
    Nat.beq (Nat.lor (Nat.land gp (Nat.xor gn top)) (takeTwo c a.s b.s)) top &&
    gateAvail g v &&
    r ((g, .tNone) :: dropTwo a.w.1 b.w.1 v)
  tryAnd || tryOr
def fastPair1 (r : List Wire → Bool) (v : List Wire) (c : Cov) (a b : WAct1) : Bool :=
  let tryAnd :=
    isNotSpec0 a.tg && isNotSpec0 b.tg &&
    Nat.beq (Nat.land a.up b.p) a.up && Nat.beq (Nat.land b.up a.p) b.up &&
    Nat.beq (Nat.land a.un b.n) a.un && Nat.beq (Nat.land b.un a.n) b.un &&
    let gp := Nat.land a.p b.p
    let gn := Nat.land a.n b.n
    let g : Sig := (gp, gn)
    Nat.beq (Nat.lor (Nat.xor gp gn) (takeTwo c a.s b.s)) top &&
    gateAvail g v &&
    let gt := if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone
    r ((g, gt) :: dropTwo a.w.1 b.w.1 v)
  let tryOr :=
    isNotSpec1 a.tg && isNotSpec1 b.tg &&
    Nat.beq (Nat.land a.up b.n) 0 && Nat.beq (Nat.land b.up a.n) 0 &&
    Nat.beq (Nat.land a.un b.p) 0 && Nat.beq (Nat.land b.un a.p) 0 &&
    let gp := Nat.lor a.p b.p
    let gn := Nat.lor a.n b.n
    let g : Sig := (gp, gn)
    Nat.beq (Nat.lor (Nat.xor gp gn) (takeTwo c a.s b.s)) top &&
    gateAvail g v &&
    r ((g, .tNone) :: dropTwo a.w.1 b.w.1 v)
  tryAnd || tryOr
def tryKeeps1 (r : List Wire → Bool) (v : List Wire) (a b : Sig)
    (base sa sb : Nat) (g wa wb : Wire) (ka kb ua ub : Bool) : Bool :=
  let ok0 := ua && ub && Nat.beq base top
  let okA := ka && ub && Nat.beq (Nat.lor base sa) top
  let okB := kb && ua && Nat.beq (Nat.lor base sb) top
  (ok0 || okA || okB) && gateAvail g.1 v &&
    let rest := dropTwo a b v
    ((ok0 && r (g :: rest)) ||
     (okA && r (g :: wa :: rest)) ||
     (okB && r (g :: wb :: rest)))
def tryKeeps2 (r : List Wire → Bool) (v : List Wire) (a b : Sig)
    (base sa sb : Nat) (g wa wb : Wire) (ka kb : Bool) : Bool :=
  let ok0 := Nat.beq base top
  let okA := ka && Nat.beq (Nat.lor base sa) top
  let okB := kb && Nat.beq (Nat.lor base sb) top
  let okAB := ka && kb && Nat.beq (Nat.lor (Nat.lor base sa) sb) top
  (ok0 || okA || okB || okAB) && gateAvail g.1 v &&
    let rest := dropTwo a b v
    ((ok0 && r (g :: rest)) ||
     (okA && r (g :: wa :: rest)) ||
     (okB && r (g :: wb :: rest)) ||
     (okAB && r (g :: wa :: wb :: rest)))
def slow1Pair0 (r : List Wire → Bool) (v : List Wire) (c : Cov) (a b : WAct0) : Bool :=
  let tryAnd :=
    isNotSpec0 a.tg && isNotSpec0 b.tg &&
    let ka := isNoneTag a.tg
    let kb := isNoneTag b.tg
    let ua := Nat.beq (Nat.land a.u b.p) a.u
    let ub := Nat.beq (Nat.land b.u a.p) b.u
    (ua || ub) && (ua || ka) && (ub || kb) &&
    let gp := Nat.land a.p b.p
    let gn := Nat.land a.n b.n
    let base := Nat.lor (Nat.land gp (Nat.xor gn top)) (takeTwo c a.s b.s)
    let gt := if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone
    tryKeeps1 r v a.w.1 b.w.1 base a.s b.s ((gp, gn), gt) a.w b.w ka kb ua ub
  let tryOr :=
    isNotSpec1 a.tg && isNotSpec1 b.tg &&
    let ka := isNotSpec0 a.tg
    let kb := isNotSpec0 b.tg
    let ua := Nat.beq (Nat.land a.u b.n) 0
    let ub := Nat.beq (Nat.land b.u a.n) 0
    (ua || ub) && (ua || ka) && (ub || kb) &&
    let gp := Nat.lor a.p b.p
    let gn := Nat.lor a.n b.n
    let base := Nat.lor (Nat.land gp (Nat.xor gn top)) (takeTwo c a.s b.s)
    let wa : Wire := (a.w.1, if isDeg3Tag a.tg then .tSpec0 else .tNone)
    let wb : Wire := (b.w.1, if isDeg3Tag b.tg then .tSpec0 else .tNone)
    tryKeeps1 r v a.w.1 b.w.1 base a.s b.s ((gp, gn), .tNone) wa wb ka kb ua ub
  tryAnd || tryOr
def slow1Pair1 (r : List Wire → Bool) (v : List Wire) (c : Cov) (a b : WAct1) : Bool :=
  let tryAnd :=
    isNotSpec0 a.tg && isNotSpec0 b.tg &&
    let ka := isNoneTag a.tg
    let kb := isNoneTag b.tg
    let ua := Nat.beq (Nat.land a.up b.p) a.up && Nat.beq (Nat.land a.un b.n) a.un
    let ub := Nat.beq (Nat.land b.up a.p) b.up && Nat.beq (Nat.land b.un a.n) b.un
    (ua || ub) && (ua || ka) && (ub || kb) &&
    let gp := Nat.land a.p b.p
    let gn := Nat.land a.n b.n
    let base := Nat.lor (Nat.xor gp gn) (takeTwo c a.s b.s)
    let gt := if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone
    tryKeeps1 r v a.w.1 b.w.1 base a.s b.s ((gp, gn), gt) a.w b.w ka kb ua ub
  let tryOr :=
    isNotSpec1 a.tg && isNotSpec1 b.tg &&
    let ka := isNotSpec0 a.tg
    let kb := isNotSpec0 b.tg
    let ua := Nat.beq (Nat.land a.up b.n) 0 && Nat.beq (Nat.land a.un b.p) 0
    let ub := Nat.beq (Nat.land b.up a.n) 0 && Nat.beq (Nat.land b.un a.p) 0
    (ua || ub) && (ua || ka) && (ub || kb) &&
    let gp := Nat.lor a.p b.p
    let gn := Nat.lor a.n b.n
    let base := Nat.lor (Nat.xor gp gn) (takeTwo c a.s b.s)
    let wa : Wire := (a.w.1, if isDeg3Tag a.tg then .tSpec0 else .tNone)
    let wb : Wire := (b.w.1, if isDeg3Tag b.tg then .tSpec0 else .tNone)
    tryKeeps1 r v a.w.1 b.w.1 base a.s b.s ((gp, gn), .tNone) wa wb ka kb ua ub
  tryAnd || tryOr
def slow2Pair0 (r : List Wire → Bool) (v : List Wire) (c : Cov) (a b : WAct0) : Bool :=
  let tryAnd :=
    isNotSpec0 a.tg && isNotSpec0 b.tg &&
    let ka := isNoneTag a.tg
    let kb := isNoneTag b.tg
    (ka || Nat.beq (Nat.land a.u b.p) a.u) && (kb || Nat.beq (Nat.land b.u a.p) b.u) &&
    let gp := Nat.land a.p b.p
    let gn := Nat.land a.n b.n
    let base := Nat.lor (Nat.land gp (Nat.xor gn top)) (takeTwo c a.s b.s)
    let gt := if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone
    tryKeeps2 r v a.w.1 b.w.1 base a.s b.s ((gp, gn), gt) a.w b.w ka kb
  let tryOr :=
    isNotSpec1 a.tg && isNotSpec1 b.tg &&
    let ka := isNotSpec0 a.tg
    let kb := isNotSpec0 b.tg
    (ka || Nat.beq (Nat.land a.u b.n) 0) && (kb || Nat.beq (Nat.land b.u a.n) 0) &&
    let gp := Nat.lor a.p b.p
    let gn := Nat.lor a.n b.n
    let base := Nat.lor (Nat.land gp (Nat.xor gn top)) (takeTwo c a.s b.s)
    let wa : Wire := (a.w.1, if isDeg3Tag a.tg then .tSpec0 else .tNone)
    let wb : Wire := (b.w.1, if isDeg3Tag b.tg then .tSpec0 else .tNone)
    tryKeeps2 r v a.w.1 b.w.1 base a.s b.s ((gp, gn), .tNone) wa wb ka kb
  tryAnd || tryOr
def slow2Pair1 (r : List Wire → Bool) (v : List Wire) (c : Cov) (a b : WAct1) : Bool :=
  let tryAnd :=
    isNotSpec0 a.tg && isNotSpec0 b.tg &&
    let ka := isNoneTag a.tg
    let kb := isNoneTag b.tg
    (ka || (Nat.beq (Nat.land a.up b.p) a.up && Nat.beq (Nat.land a.un b.n) a.un)) &&
    (kb || (Nat.beq (Nat.land b.up a.p) b.up && Nat.beq (Nat.land b.un a.n) b.un)) &&
    let gp := Nat.land a.p b.p
    let gn := Nat.land a.n b.n
    let base := Nat.lor (Nat.xor gp gn) (takeTwo c a.s b.s)
    let gt := if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone
    tryKeeps2 r v a.w.1 b.w.1 base a.s b.s ((gp, gn), gt) a.w b.w ka kb
  let tryOr :=
    isNotSpec1 a.tg && isNotSpec1 b.tg &&
    let ka := isNotSpec0 a.tg
    let kb := isNotSpec0 b.tg
    (ka || (Nat.beq (Nat.land a.up b.n) 0 && Nat.beq (Nat.land a.un b.p) 0)) &&
    (kb || (Nat.beq (Nat.land b.up a.n) 0 && Nat.beq (Nat.land b.un a.p) 0)) &&
    let gp := Nat.lor a.p b.p
    let gn := Nat.lor a.n b.n
    let base := Nat.lor (Nat.xor gp gn) (takeTwo c a.s b.s)
    let wa : Wire := (a.w.1, if isDeg3Tag a.tg then .tSpec0 else .tNone)
    let wb : Wire := (b.w.1, if isDeg3Tag b.tg then .tSpec0 else .tNone)
    tryKeeps2 r v a.w.1 b.w.1 base a.s b.s ((gp, gn), .tNone) wa wb ka kb
  tryAnd || tryOr
def scanFast0One (r : List Wire → Bool) (v : List Wire) (c : Cov) (a : WAct0) : List WAct0 → Bool
  | [] => false
  | b :: l => fastPair0 r v c a b || scanFast0One r v c a l
def scanFast0 (r : List Wire → Bool) (v : List Wire) (c : Cov) : List WAct0 → Bool
  | [] => false
  | a :: l => scanFast0One r v c a l || scanFast0 r v c l
def scanFast1One (r : List Wire → Bool) (v : List Wire) (c : Cov) (a : WAct1) : List WAct1 → Bool
  | [] => false
  | b :: l => fastPair1 r v c a b || scanFast1One r v c a l
def scanFast1 (r : List Wire → Bool) (v : List Wire) (c : Cov) : List WAct1 → Bool
  | [] => false
  | a :: l => scanFast1One r v c a l || scanFast1 r v c l
def scanSlow10One (r : List Wire → Bool) (v : List Wire) (c : Cov) (a : WAct0) : List WAct0 → Bool
  | [] => false
  | b :: l => slow1Pair0 r v c a b || scanSlow10One r v c a l
def scanSlow10 (r : List Wire → Bool) (v : List Wire) (c : Cov) : List WAct0 → Bool
  | [] => false
  | a :: l => scanSlow10One r v c a l || scanSlow10 r v c l
def scanSlow11One (r : List Wire → Bool) (v : List Wire) (c : Cov) (a : WAct1) : List WAct1 → Bool
  | [] => false
  | b :: l => slow1Pair1 r v c a b || scanSlow11One r v c a l
def scanSlow11 (r : List Wire → Bool) (v : List Wire) (c : Cov) : List WAct1 → Bool
  | [] => false
  | a :: l => scanSlow11One r v c a l || scanSlow11 r v c l
def scanSlow20One (r : List Wire → Bool) (v : List Wire) (c : Cov) (a : WAct0) : List WAct0 → Bool
  | [] => false
  | b :: l => slow2Pair0 r v c a b || scanSlow20One r v c a l
def scanSlow20 (r : List Wire → Bool) (v : List Wire) (c : Cov) : List WAct0 → Bool
  | [] => false
  | a :: l => scanSlow20One r v c a l || scanSlow20 r v c l
def scanSlow21One (r : List Wire → Bool) (v : List Wire) (c : Cov) (a : WAct1) : List WAct1 → Bool
  | [] => false
  | b :: l => slow2Pair1 r v c a b || scanSlow21One r v c a l
def scanSlow21 (r : List Wire → Bool) (v : List Wire) (c : Cov) : List WAct1 → Bool
  | [] => false
  | a :: l => scanSlow21One r v c a l || scanSlow21 r v c l
def unaryScan0 (lim n : Nat) (r : List Wire → Bool) (v : List Wire) (c : Cov) : List WSep → Bool
  | [] => false
  | a :: l =>
    (isNotSpec0 a.tg && isNotSpec1 a.tg &&
      let gp := Nat.xor a.p top
      let gn := Nat.xor a.n top
      let base := Nat.lor (Nat.land gp (Nat.xor gn top)) (takeOne c a.s)
      let ka := !isDeg3Tag a.tg && Nat.ble (n + 2) lim
      let ok0 := Nat.beq base top
      let okA := ka && Nat.beq (Nat.lor base a.s) top
      (ok0 || okA) && gateAvail (gp, gn) v &&
        let gt := if isDeg3Tag a.tg then Tag.tSpec1 else Tag.tNone
        let rest := dropOne a.w.1 v
        ((ok0 && r (((gp, gn), gt) :: rest)) ||
         (okA && r (((gp, gn), gt) :: a.w :: rest)))) ||
    unaryScan0 lim n r v c l
def unaryScan1 (lim n : Nat) (r : List Wire → Bool) (v : List Wire) (c : Cov) : List WSep → Bool
  | [] => false
  | a :: l =>
    (isNotSpec0 a.tg && isNotSpec1 a.tg &&
      let gp := Nat.xor a.p top
      let gn := Nat.xor a.n top
      let base := Nat.lor (Nat.xor gp gn) (takeOne c a.s)
      let ka := !isDeg3Tag a.tg && Nat.ble (n + 2) lim
      let ok0 := Nat.beq base top
      let okA := ka && Nat.beq (Nat.lor base a.s) top
      (ok0 || okA) && gateAvail (gp, gn) v &&
        let gt := if isDeg3Tag a.tg then Tag.tSpec1 else Tag.tNone
        let rest := dropOne a.w.1 v
        ((ok0 && r (((gp, gn), gt) :: rest)) ||
         (okA && r (((gp, gn), gt) :: a.w :: rest)))) ||
    unaryScan1 lim n r v c l
def binaryMoves (k t len : Nat) (r : List Wire → Bool) (v : List Wire) : Bool :=
  let lim := k - t + 1
  if Nat.beq t 0 then
    let (seps, c) := buildSeps0 v
    let acts := buildActs0 c.2.1 seps
    if Nat.beq len (lim + 1) then scanFast0 r v c acts
    else if Nat.beq len lim then scanSlow10 r v c acts
    else scanSlow20 r v c acts
  else
    let (seps, c) := buildSeps1 v
    let acts := buildActs1 c.2.1 seps
    if Nat.beq len (lim + 1) then scanFast1 r v c acts
    else if Nat.beq len lim then scanSlow11 r v c acts
    else scanSlow21 r v c acts
def unaryMoves (k t len : Nat) (r : List Wire → Bool) (v : List Wire) : Bool :=
  if Nat.beq t 0 then
    let (seps, c) := buildSeps0 v
    unaryScan0 (k - t + 1) (len - 1) r v c seps
  else
    let (seps, c) := buildSeps1 v
    unaryScan1 (k - t + 1) (len - 1) r v c seps
def stepTest (k t : Nat) (v : List Wire) (u b : List Wire → Bool) : Bool :=
  let len := v.length
  if Nat.blt (k + 1) t || Nat.blt (k + 1 - t + 1) len then false else
    (match v with | [w] => sigEq w.1 target | _ => false) ||
    (Nat.blt 0 t && unaryMoves k (t - 1) len u v) ||
    binaryMoves k t len b v
def search : Nat → Nat → List Wire → Bool
  | 0, _, v => match v with | [w] => sigEq w.1 target | _ => false
  | k + 1, t, v => stepTest k t v (search k (t - 1)) (search k t)
def scanPairs {α : Type} (p : α → α → Bool) : List α → Bool
  | [] => false
  | a :: t => t.any (p a) || scanPairs p t
lemma scanPairs_complete {α : Type} (p : α → α → Bool) {a b : α} {v : List α}
    (ha : a ∈ v) (hb : b ∈ v) (hne : a ≠ b)
    (hab : p a b = true) (hba : p b a = true) : scanPairs p v = true := by
  induction v with
  | nil => simp at ha
  | cons h v ih =>
    simp only [scanPairs, Bool.or_eq_true]
    by_cases eqA : a = h
    · subst h; exact Or.inl (List.any_eq_true.mpr ⟨b, (List.mem_cons.mp hb).resolve_left (Ne.symm hne), hab⟩)
    · have ha' := (List.mem_cons.mp ha).resolve_left eqA
      by_cases eqB : b = h
      · subst h; exact Or.inl (List.any_eq_true.mpr ⟨a, ha', hba⟩)
      · exact Or.inr (ih ha' ((List.mem_cons.mp hb).resolve_left eqB))
lemma scanFast0One_eq (r v c a l) : scanFast0One r v c a l = l.any (fastPair0 r v c a) := by
  induction l with | nil => rfl | cons b l ih => simp [scanFast0One, ih]
lemma scanFast0_eq (r v c l) : scanFast0 r v c l = scanPairs (fastPair0 r v c) l := by
  induction l with | nil => rfl | cons a l ih => simp [scanFast0, scanPairs, scanFast0One_eq, ih]
lemma scanFast1One_eq (r v c a l) : scanFast1One r v c a l = l.any (fastPair1 r v c a) := by
  induction l with | nil => rfl | cons b l ih => simp [scanFast1One, ih]
lemma scanFast1_eq (r v c l) : scanFast1 r v c l = scanPairs (fastPair1 r v c) l := by
  induction l with | nil => rfl | cons a l ih => simp [scanFast1, scanPairs, scanFast1One_eq, ih]
lemma scanSlow10One_eq (r v c a l) : scanSlow10One r v c a l = l.any (slow1Pair0 r v c a) := by
  induction l with | nil => rfl | cons b l ih => simp [scanSlow10One, ih]
lemma scanSlow10_eq (r v c l) : scanSlow10 r v c l = scanPairs (slow1Pair0 r v c) l := by
  induction l with | nil => rfl | cons a l ih => simp [scanSlow10, scanPairs, scanSlow10One_eq, ih]
lemma scanSlow11One_eq (r v c a l) : scanSlow11One r v c a l = l.any (slow1Pair1 r v c a) := by
  induction l with | nil => rfl | cons b l ih => simp [scanSlow11One, ih]
lemma scanSlow11_eq (r v c l) : scanSlow11 r v c l = scanPairs (slow1Pair1 r v c) l := by
  induction l with | nil => rfl | cons a l ih => simp [scanSlow11, scanPairs, scanSlow11One_eq, ih]
lemma scanSlow20One_eq (r v c a l) : scanSlow20One r v c a l = l.any (slow2Pair0 r v c a) := by
  induction l with | nil => rfl | cons b l ih => simp [scanSlow20One, ih]
lemma scanSlow20_eq (r v c l) : scanSlow20 r v c l = scanPairs (slow2Pair0 r v c) l := by
  induction l with | nil => rfl | cons a l ih => simp [scanSlow20, scanPairs, scanSlow20One_eq, ih]
lemma scanSlow21One_eq (r v c a l) : scanSlow21One r v c a l = l.any (slow2Pair1 r v c a) := by
  induction l with | nil => rfl | cons b l ih => simp [scanSlow21One, ih]
lemma scanSlow21_eq (r v c l) : scanSlow21 r v c l = scanPairs (slow2Pair1 r v c) l := by
  induction l with | nil => rfl | cons a l ih => simp [scanSlow21, scanPairs, scanSlow21One_eq, ih]
lemma unique_and_0 {c : Cov} {a b : Sig} {extra : Nat} (hc : ValidCov c)
    (hex : Nat.land (Nat.land c.2.1 (sep0 a)) extra = 0)
    (h : Nat.lor (Nat.lor (sep0 (bin false a b)) (takeTwo c (sep0 a) (sep0 b))) extra = top) :
    Nat.land (Nat.land c.2.1 (sep0 a)) b.1 = Nat.land c.2.1 (sep0 a) := by
  apply Nat.eq_of_testBit_eq; intro i
  have hh := congrArg (fun z : Nat => z.testBit i) h
  have hx := congrArg (fun z : Nat => z.testBit i) hex
  have h1 := hc.2.2.2.1 i
  by_cases hi : i < 414
  · simp only [sep0, bin, takeTwo, testBit_land, testBit_lor, testBit_lxor, testBit_top,
      Nat.testBit_and, hi, decide_true, Nat.zero_testBit, Bool.false_eq_true, ite_false] at hh hx ⊢
    revert hh hx h1
    cases a.1.testBit i <;> cases a.2.testBit i <;> cases b.1.testBit i <;>
      cases b.2.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;>
      cases extra.testBit i <;> simp
  · simp [hc.2.1 i (by omega)]
lemma unique_or_0 {c : Cov} {a b : Sig} {extra : Nat} (hc : ValidCov c)
    (hex : Nat.land (Nat.land c.2.1 (sep0 a)) extra = 0)
    (h : Nat.lor (Nat.lor (sep0 (bin true a b)) (takeTwo c (sep0 a) (sep0 b))) extra = top) :
    Nat.land (Nat.land c.2.1 (sep0 a)) b.2 = 0 := by
  apply Nat.eq_of_testBit_eq; intro i
  have hh := congrArg (fun z : Nat => z.testBit i) h
  have hx := congrArg (fun z : Nat => z.testBit i) hex
  have h1 := hc.2.2.2.1 i
  by_cases hi : i < 414
  · simp only [sep0, bin, takeTwo, testBit_land, testBit_lor, testBit_lxor, testBit_top,
      Nat.testBit_or, hi, decide_true, Nat.zero_testBit, ite_true] at hh hx ⊢
    revert hh hx h1
    cases a.1.testBit i <;> cases a.2.testBit i <;> cases b.1.testBit i <;>
      cases b.2.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;>
      cases extra.testBit i <;> simp
  · simp [hc.2.1 i (by omega)]
lemma unique_and_1 {c : Cov} {a b : Sig} {extra : Nat} (hc : ValidCov c)
    (hex : Nat.land (Nat.land c.2.1 (sep1 a)) extra = 0)
    (h : Nat.lor (Nat.lor (sep1 (bin false a b)) (takeTwo c (sep1 a) (sep1 b))) extra = top) :
    Nat.land (Nat.land (Nat.land c.2.1 (sep1 a)) a.1) b.1 = Nat.land (Nat.land c.2.1 (sep1 a)) a.1 ∧
    Nat.land (Nat.land (Nat.land c.2.1 (sep1 a)) a.2) b.2 = Nat.land (Nat.land c.2.1 (sep1 a)) a.2 := by
  constructor <;> (
    apply Nat.eq_of_testBit_eq; intro i
    have hh := congrArg (fun z : Nat => z.testBit i) h
    have hx := congrArg (fun z : Nat => z.testBit i) hex
    have h1 := hc.2.2.2.1 i
    by_cases hi : i < 414
    · simp only [sep1, bin, takeTwo, testBit_land, testBit_lor, testBit_lxor, testBit_top,
        Nat.testBit_and, hi, decide_true, Nat.zero_testBit, Bool.false_eq_true, ite_false] at hh hx ⊢
      revert hh hx h1
      cases a.1.testBit i <;> cases a.2.testBit i <;> cases b.1.testBit i <;>
        cases b.2.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;>
        cases extra.testBit i <;> simp
    · simp [hc.2.1 i (by omega)])
lemma unique_or_1 {c : Cov} {a b : Sig} {extra : Nat} (hc : ValidCov c)
    (hex : Nat.land (Nat.land c.2.1 (sep1 a)) extra = 0)
    (h : Nat.lor (Nat.lor (sep1 (bin true a b)) (takeTwo c (sep1 a) (sep1 b))) extra = top) :
    Nat.land (Nat.land (Nat.land c.2.1 (sep1 a)) a.1) b.2 = 0 ∧
    Nat.land (Nat.land (Nat.land c.2.1 (sep1 a)) a.2) b.1 = 0 := by
  constructor <;> (
    apply Nat.eq_of_testBit_eq; intro i
    have hh := congrArg (fun z : Nat => z.testBit i) h
    have hx := congrArg (fun z : Nat => z.testBit i) hex
    have h1 := hc.2.2.2.1 i
    by_cases hi : i < 414
    · simp only [sep1, bin, takeTwo, testBit_land, testBit_lor, testBit_lxor, testBit_top,
        Nat.testBit_or, hi, decide_true, Nat.zero_testBit, ite_true] at hh hx ⊢
      revert hh hx h1
      cases a.1.testBit i <;> cases a.2.testBit i <;> cases b.1.testBit i <;>
        cases b.2.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;>
        cases extra.testBit i <;> simp
    · simp [hc.2.1 i (by omega)])
lemma unaryScan0_mem {lim n : Nat} {r : List Wire → Bool} {v : List Wire} {c : Cov}
    {a : WSep} {l : List WSep} (ha : a ∈ l)
    (hok : (isNotSpec0 a.tg && isNotSpec1 a.tg &&
      let gp := Nat.xor a.p top; let gn := Nat.xor a.n top
      let base := Nat.lor (Nat.land gp (Nat.xor gn top)) (takeOne c a.s)
      let ka := !isDeg3Tag a.tg && Nat.ble (n + 2) lim
      let ok0 := Nat.beq base top
      let okA := ka && Nat.beq (Nat.lor base a.s) top
      (ok0 || okA) && gateAvail (gp, gn) v &&
        let gt := if isDeg3Tag a.tg then Tag.tSpec1 else Tag.tNone
        let rest := dropOne a.w.1 v
        ((ok0 && r (((gp, gn), gt) :: rest)) || (okA && r (((gp, gn), gt) :: a.w :: rest)))) = true) :
    unaryScan0 lim n r v c l = true := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    simp only [unaryScan0, Bool.or_eq_true]
    rcases List.mem_cons.mp ha with rfl | hx
    · exact Or.inl hok
    · exact Or.inr (ih hx)
lemma unaryScan1_mem {lim n : Nat} {r : List Wire → Bool} {v : List Wire} {c : Cov}
    {a : WSep} {l : List WSep} (ha : a ∈ l)
    (hok : (isNotSpec0 a.tg && isNotSpec1 a.tg &&
      let gp := Nat.xor a.p top; let gn := Nat.xor a.n top
      let base := Nat.lor (Nat.xor gp gn) (takeOne c a.s)
      let ka := !isDeg3Tag a.tg && Nat.ble (n + 2) lim
      let ok0 := Nat.beq base top
      let okA := ka && Nat.beq (Nat.lor base a.s) top
      (ok0 || okA) && gateAvail (gp, gn) v &&
        let gt := if isDeg3Tag a.tg then Tag.tSpec1 else Tag.tNone
        let rest := dropOne a.w.1 v
        ((ok0 && r (((gp, gn), gt) :: rest)) || (okA && r (((gp, gn), gt) :: a.w :: rest)))) = true) :
    unaryScan1 lim n r v c l = true := by
  induction l with
  | nil => simp at ha
  | cons x l ih =>
    simp only [unaryScan1, Bool.or_eq_true]
    rcases List.mem_cons.mp ha with rfl | hx
    · exact Or.inl hok
    · exact Or.inr (ih hx)
lemma unary_found {m t k : Nat} {U : Finset Sig} {a : Sig} {τ : Sig → Tag} {v : List Wire}
    {r : List Wire → Bool}
    (ha : proper a) (hrep : Represents v (insert a U) τ) (hle : m ≤ k)
    (fresh : neg a ∉ insert a U)
    (hr1 : τ a ≠ .tSpec0 ∧ τ a ≠ .tSpec1) (hr2 : τ a = .tDeg3 → a ∉ U)
    (l : TRestricted m t (insert (neg a) U) (updUnaryTag τ a))
    (ih : ∀ w : List Wire, Represents w (insert (neg a) U) (updUnaryTag τ a) → r w = true) :
    unaryMoves k t v.length r v = true := by
  obtain ⟨hndS, heS, htag⟩ := hrep
  have hval : ∀ x ∈ sigsOf v, Valid x := by
    intro x hx
    rcases Finset.mem_insert.mp (heS ▸ List.mem_toFinset.mpr hx) with rfl | hxU
    · exact ha.1
    · exact (live_proper l.live x (Finset.mem_insert_of_mem hxU)).1
  have ahS : a ∈ sigsOf v := List.mem_toFinset.mp (heS.symm ▸ Finset.mem_insert_self _ _)
  have ah : (a, τ a) ∈ v := (mem_sigsOf_iff htag).mpr ahS
  let rest := droppedW [a] v
  let gTag : Tag := if isDeg3Tag (τ a) then .tSpec1 else .tNone
  let g : Wire := (neg a, gTag)
  let h : List Wire := if a ∈ U then [(a, τ a)] else []
  have hSigsH : sigsOf h = keepOf U [a] := by by_cases hm : a ∈ U <;> simp [h, sigsOf, keepOf, hm]
  obtain ⟨hn, eq⟩ := edit_list (del := [a]) (U := U) hndS (by simp) (by simpa using heS)
  have hSigsHR : sigsOf (h ++ rest) = keepOf U [a] ++ dropped [a] (sigsOf v) := by
    change (h ++ rest).map Prod.fst = _
    rw [List.map_append, show h.map Prod.fst = keepOf U [a] from hSigsH,
      show rest.map Prod.fst = dropped [a] (sigsOf v) from sigsOf_droppedW [a] v]
  have nn : neg a ∉ sigsOf v := fun hm => fresh (heS ▸ List.mem_toFinset.mpr hm)
  have nz : neg a ∉ U := fun hm => fresh (Finset.mem_insert_of_mem hm)
  have hnd : (sigsOf (g :: (h ++ rest))).Nodup := by
    change (neg a :: sigsOf (h ++ rest)).Nodup; rw [hSigsHR]
    exact List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm), hn⟩
  have e : (sigsOf (g :: (h ++ rest))).toFinset = insert (neg a) U := by
    change (neg a :: sigsOf (h ++ rest)).toFinset = _; rw [List.toFinset_cons, hSigsHR, eq]
  have htag' : ∀ w ∈ g :: (h ++ rest), w.2 = updUnaryTag τ a w.1 := by
    intro w hw; rcases List.mem_cons.mp hw with rfl | hw'
    · simp only [g, gTag, updUnaryTag, ite_true]; cases τ a <;> rfl
    · have hwV : w ∈ v := by
        rcases List.mem_append.mp hw' with hh | hr
        · by_cases hm : a ∈ U
          · simp only [h, hm, ite_true, List.mem_singleton] at hh; exact hh ▸ ah
          · simp [h, hm] at hh
        · exact List.mem_of_mem_filter hr
      have hwNe : w.1 ≠ neg a := fun heq => nn (heq ▸ List.mem_map_of_mem hwV)
      simp [updUnaryTag, hwNe, htag w hwV]
  have hr := ih _ ⟨hnd, e, htag'⟩
  obtain ⟨ht, hc⟩ := live_size l.live
  rw [← e, List.toFinset_card_of_nodup hnd] at hc
  simp only [sigsOf, List.map_cons, List.map_append, List.length_cons, List.length_append,
    List.length_map] at hc
  have hav : gateAvail (neg a) v = true :=
    gateAvail_eq_true nn (live_proper l.live _ (Finset.mem_insert_self _ _))
  have hns0 : isNotSpec0 (τ a) = true := by cases hta : τ a <;> simp [isNotSpec0]; exact hr1.1 hta
  have hns1 : isNotSpec1 (τ a) = true := by cases hta : τ a <;> simp [isNotSpec1]; exact hr1.2 hta
  have cv := live_cover l.live e
  simp only [sigsOf, List.map_cons, List.map_append, unionSep, union_append] at cv
  have hcv' : (sep (decide (0 < t)) (neg a) ||| unionSep (decide (0 < t)) (sigsOf rest)) |||
      unionSepW (decide (0 < t)) h = top := by
    rw [unionSepW_eq, ← cv]; unfold sigsOf; ac_rfl
  obtain ⟨hlen, hmask⟩ := one_rest (decide (0 < t)) hndS hval ahS
  rw [sigsOf_length, ← sigsOf_droppedW, sigsOf_length] at hlen
  change v.length - 1 = rest.length at hlen
  rw [← sigsOf_droppedW] at hmask
  change takeOne (coverage (decide (0 < t)) (sigsOf v)) (sep (decide (0 < t)) a) =
    unionSep (decide (0 < t)) (sigsOf rest) at hmask
  have hdrop : dropOne a v = rest := dropOne_eq a v
  unfold unaryMoves
  by_cases ht0 : t = 0
  · subst ht0
    have hdt0 : decide (0 < 0) = false := rfl
    rw [hdt0] at hcv' hmask
    simp only [Nat.beq_refl, ite_true, buildSeps0_eq]
    apply unaryScan0_mem (a := mkSep0 (a, τ a)) (List.mem_map_of_mem ah)
    simp only [mkSep0, coverageW_eq]
    change (isNotSpec0 (τ a) && isNotSpec1 (τ a) &&
      let base := Nat.lor (sep false (neg a)) (takeOne (coverage false (sigsOf v)) (sep false a))
      let ka := !isDeg3Tag (τ a) && Nat.ble (v.length - 1 + 2) (k - 0 + 1)
      let ok0 := Nat.beq base top
      let okA := ka && Nat.beq (Nat.lor base (sep false a)) top
      (ok0 || okA) && gateAvail (neg a) v &&
        let rest' := dropOne a v
        ((ok0 && r (g :: rest')) || (okA && r (g :: (a, τ a) :: rest')))) = true
    rw [hmask, hdrop]
    by_cases haU : a ∈ U
    · have hnd3 : (!isDeg3Tag (τ a)) = true := by
        cases hta : τ a <;> simp [isDeg3Tag]; exact hr2 hta haU
      have hlenH : h.length = 1 := by simp [h, haU]
      have hle' : Nat.ble (v.length - 1 + 2) (k - 0 + 1) = true := Nat.ble_eq.mpr (by omega)
      have hcovA : Nat.lor (Nat.lor (sep false (neg a)) (unionSep false (sigsOf rest))) (sep false a) = top := by
        simpa [h, haU, unionSepW] using hcv'
      have hrA : r (g :: (a, τ a) :: rest) = true := by simpa [h, haU] using hr
      simp only [hns0, hns1, hnd3, hle', hcovA, Nat.beq_refl, hav, hrA, Bool.true_and, Bool.or_true]
    · have hcov0 : Nat.lor (sep false (neg a)) (unionSep false (sigsOf rest)) = top := by
        simpa [h, haU, unionSepW] using hcv'
      have hr0 : r (g :: rest) = true := by simpa [h, haU] using hr
      simp only [hns0, hns1, hcov0, Nat.beq_refl, hav, hr0, Bool.true_and, Bool.true_or]
  · have hbf : Nat.beq t 0 = false := nat_beq_false ht0
    have hdt : decide (0 < t) = true := decide_eq_true (by omega)
    rw [hdt] at hcv' hmask
    simp only [hbf, Bool.false_eq_true, ite_false, buildSeps1_eq]
    apply unaryScan1_mem (a := mkSep1 (a, τ a)) (List.mem_map_of_mem ah)
    simp only [mkSep1, coverageW_eq]
    change (isNotSpec0 (τ a) && isNotSpec1 (τ a) &&
      let base := Nat.lor (sep true (neg a)) (takeOne (coverage true (sigsOf v)) (sep true a))
      let ka := !isDeg3Tag (τ a) && Nat.ble (v.length - 1 + 2) (k - t + 1)
      let ok0 := Nat.beq base top
      let okA := ka && Nat.beq (Nat.lor base (sep true a)) top
      (ok0 || okA) && gateAvail (neg a) v &&
        let rest' := dropOne a v
        ((ok0 && r (g :: rest')) || (okA && r (g :: (a, τ a) :: rest')))) = true
    rw [hmask, hdrop]
    by_cases haU : a ∈ U
    · have hnd3 : (!isDeg3Tag (τ a)) = true := by
        cases hta : τ a <;> simp [isDeg3Tag]; exact hr2 hta haU
      have hlenH : h.length = 1 := by simp [h, haU]
      have hle' : Nat.ble (v.length - 1 + 2) (k - t + 1) = true := Nat.ble_eq.mpr (by omega)
      have hcovA : Nat.lor (Nat.lor (sep true (neg a)) (unionSep true (sigsOf rest))) (sep true a) = top := by
        simpa [h, haU, unionSepW] using hcv'
      have hrA : r (g :: (a, τ a) :: rest) = true := by simpa [h, haU] using hr
      simp only [hns0, hns1, hnd3, hle', hcovA, Nat.beq_refl, hav, hrA, Bool.true_and, Bool.or_true]
    · have hcov0 : Nat.lor (sep true (neg a)) (unionSep true (sigsOf rest)) = top := by
        simpa [h, haU, unionSepW] using hcv'
      have hr0 : r (g :: rest) = true := by simpa [h, haU] using hr
      simp only [hns0, hns1, hcov0, Nat.beq_refl, hav, hr0, Bool.true_and, Bool.true_or]
lemma bor_l {p q : Bool} (h : p = true) : (p || q) = true := by simp [h]
lemma bor_r {p q : Bool} (h : q = true) : (p || q) = true := by simp [h]
lemma band2 {p q : Bool} (hp : p = true) (hq : q = true) : (p && q) = true := by simp [hp, hq]
lemma tryKeeps1_guard {r v a b base sa sb g wa wb ka kb ua ub}
    (h : tryKeeps1 r v a b base sa sb g wa wb ka kb ua ub = true) :
    (ua || ub) = true ∧ (ua || ka) = true ∧ (ub || kb) = true := by
  cases ka <;> cases kb <;> cases ua <;> cases ub <;> simp_all [tryKeeps1]
lemma tryKeeps1_0 {r v a b base sa sb g wa wb ka kb ua ub}
    (h1 : ua = true) (h2 : ub = true) (h3 : base = top)
    (h4 : gateAvail g.1 v = true) (h5 : r (g :: dropTwo a b v) = true) :
    tryKeeps1 r v a b base sa sb g wa wb ka kb ua ub = true := by
  simp only [tryKeeps1, h1, h2, h3, Nat.beq_refl, h4, h5, Bool.true_and, Bool.true_or]
lemma tryKeeps1_A {r v a b base sa sb g wa wb ka kb ua ub}
    (h1 : ka = true) (h2 : ub = true) (h3 : Nat.lor base sa = top)
    (h4 : gateAvail g.1 v = true) (h5 : r (g :: wa :: dropTwo a b v) = true) :
    tryKeeps1 r v a b base sa sb g wa wb ka kb ua ub = true := by
  simp only [tryKeeps1, h1, h2, h3, Nat.beq_refl, h4, h5, Bool.true_and, Bool.true_or, Bool.or_true]
lemma tryKeeps1_B {r v a b base sa sb g wa wb ka kb ua ub}
    (h1 : kb = true) (h2 : ua = true) (h3 : Nat.lor base sb = top)
    (h4 : gateAvail g.1 v = true) (h5 : r (g :: wb :: dropTwo a b v) = true) :
    tryKeeps1 r v a b base sa sb g wa wb ka kb ua ub = true := by
  simp only [tryKeeps1, h1, h2, h3, Nat.beq_refl, h4, h5, Bool.true_and, Bool.or_true]
lemma tryKeeps2_0 {r v a b base sa sb g wa wb ka kb}
    (h3 : base = top) (h4 : gateAvail g.1 v = true) (h5 : r (g :: dropTwo a b v) = true) :
    tryKeeps2 r v a b base sa sb g wa wb ka kb = true := by
  simp only [tryKeeps2, h3, Nat.beq_refl, h4, h5, Bool.true_and, Bool.true_or]
lemma tryKeeps2_A {r v a b base sa sb g wa wb ka kb}
    (h1 : ka = true) (h3 : Nat.lor base sa = top)
    (h4 : gateAvail g.1 v = true) (h5 : r (g :: wa :: dropTwo a b v) = true) :
    tryKeeps2 r v a b base sa sb g wa wb ka kb = true := by
  simp only [tryKeeps2, h1, h3, Nat.beq_refl, h4, h5, Bool.true_and, Bool.true_or, Bool.or_true]
lemma tryKeeps2_B {r v a b base sa sb g wa wb ka kb}
    (h1 : kb = true) (h3 : Nat.lor base sb = top)
    (h4 : gateAvail g.1 v = true) (h5 : r (g :: wb :: dropTwo a b v) = true) :
    tryKeeps2 r v a b base sa sb g wa wb ka kb = true := by
  simp only [tryKeeps2, h1, h3, Nat.beq_refl, h4, h5, Bool.true_and, Bool.true_or, Bool.or_true]
lemma tryKeeps2_AB {r v a b base sa sb g wa wb ka kb}
    (h1 : ka = true) (h2 : kb = true) (h3 : Nat.lor (Nat.lor base sa) sb = top)
    (h4 : gateAvail g.1 v = true) (h5 : r (g :: wa :: wb :: dropTwo a b v) = true) :
    tryKeeps2 r v a b base sa sb g wa wb ka kb = true := by
  simp only [tryKeeps2, h1, h2, h3, Nat.beq_refl, h4, h5, Bool.true_and, Bool.or_true]
lemma fastPair0_and {r v c a b}
    (h1 : isNotSpec0 a.tg = true) (h2 : isNotSpec0 b.tg = true)
    (h3 : Nat.land a.u b.p = a.u) (h4 : Nat.land b.u a.p = b.u)
    (h5 : Nat.lor (Nat.land (Nat.land a.p b.p) (Nat.xor (Nat.land a.n b.n) top)) (takeTwo c a.s b.s) = top)
    (h6 : gateAvail (Nat.land a.p b.p, Nat.land a.n b.n) v = true)
    (h7 : r (((Nat.land a.p b.p, Nat.land a.n b.n),
      if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone) :: dropTwo a.w.1 b.w.1 v) = true) :
    fastPair0 r v c a b = true := by
  simp only [fastPair0, h1, h2, h3, h4, h5, Nat.beq_refl, h6, h7, Bool.true_and, Bool.true_or]
lemma fastPair0_or {r v c a b}
    (h1 : isNotSpec1 a.tg = true) (h2 : isNotSpec1 b.tg = true)
    (h3 : Nat.land a.u b.n = 0) (h4 : Nat.land b.u a.n = 0)
    (h5 : Nat.lor (Nat.land (Nat.lor a.p b.p) (Nat.xor (Nat.lor a.n b.n) top)) (takeTwo c a.s b.s) = top)
    (h6 : gateAvail (Nat.lor a.p b.p, Nat.lor a.n b.n) v = true)
    (h7 : r (((Nat.lor a.p b.p, Nat.lor a.n b.n), .tNone) :: dropTwo a.w.1 b.w.1 v) = true) :
    fastPair0 r v c a b = true := by
  simp only [fastPair0, h1, h2, h3, h4, h5, Nat.beq_refl, h6, h7, Bool.true_and, Bool.or_true]
lemma fastPair1_and {r v c a b}
    (h1 : isNotSpec0 a.tg = true) (h2 : isNotSpec0 b.tg = true)
    (h3a : Nat.land a.up b.p = a.up) (h3b : Nat.land b.up a.p = b.up)
    (h4a : Nat.land a.un b.n = a.un) (h4b : Nat.land b.un a.n = b.un)
    (h5 : Nat.lor (Nat.xor (Nat.land a.p b.p) (Nat.land a.n b.n)) (takeTwo c a.s b.s) = top)
    (h6 : gateAvail (Nat.land a.p b.p, Nat.land a.n b.n) v = true)
    (h7 : r (((Nat.land a.p b.p, Nat.land a.n b.n),
      if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone) :: dropTwo a.w.1 b.w.1 v) = true) :
    fastPair1 r v c a b = true := by
  simp only [fastPair1, h1, h2, h3a, h3b, h4a, h4b, h5, Nat.beq_refl, h6, h7, Bool.true_and, Bool.true_or]
lemma fastPair1_or {r v c a b}
    (h1 : isNotSpec1 a.tg = true) (h2 : isNotSpec1 b.tg = true)
    (h3a : Nat.land a.up b.n = 0) (h3b : Nat.land b.up a.n = 0)
    (h4a : Nat.land a.un b.p = 0) (h4b : Nat.land b.un a.p = 0)
    (h5 : Nat.lor (Nat.xor (Nat.lor a.p b.p) (Nat.lor a.n b.n)) (takeTwo c a.s b.s) = top)
    (h6 : gateAvail (Nat.lor a.p b.p, Nat.lor a.n b.n) v = true)
    (h7 : r (((Nat.lor a.p b.p, Nat.lor a.n b.n), .tNone) :: dropTwo a.w.1 b.w.1 v) = true) :
    fastPair1 r v c a b = true := by
  simp only [fastPair1, h1, h2, h3a, h3b, h4a, h4b, h5, Nat.beq_refl, h6, h7, Bool.true_and, Bool.or_true]
lemma slow1Pair0_and {r v c a b}
    (h1 : isNotSpec0 a.tg = true) (h2 : isNotSpec0 b.tg = true)
    (ht : tryKeeps1 r v a.w.1 b.w.1
      (Nat.lor (Nat.land (Nat.land a.p b.p) (Nat.xor (Nat.land a.n b.n) top)) (takeTwo c a.s b.s))
      a.s b.s ((Nat.land a.p b.p, Nat.land a.n b.n),
        if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone)
      a.w b.w (isNoneTag a.tg) (isNoneTag b.tg)
      (Nat.beq (Nat.land a.u b.p) a.u) (Nat.beq (Nat.land b.u a.p) b.u) = true) :
    slow1Pair0 r v c a b = true := by
  obtain ⟨g1, g2, g3⟩ := tryKeeps1_guard ht
  simp only [slow1Pair0, h1, h2, g1, g2, g3, ht, Bool.true_and, Bool.true_or]
lemma slow1Pair0_or {r v c a b}
    (h1 : isNotSpec1 a.tg = true) (h2 : isNotSpec1 b.tg = true)
    (ht : tryKeeps1 r v a.w.1 b.w.1
      (Nat.lor (Nat.land (Nat.lor a.p b.p) (Nat.xor (Nat.lor a.n b.n) top)) (takeTwo c a.s b.s))
      a.s b.s ((Nat.lor a.p b.p, Nat.lor a.n b.n), .tNone)
      (a.w.1, if isDeg3Tag a.tg then .tSpec0 else .tNone)
      (b.w.1, if isDeg3Tag b.tg then .tSpec0 else .tNone)
      (isNotSpec0 a.tg) (isNotSpec0 b.tg)
      (Nat.beq (Nat.land a.u b.n) 0) (Nat.beq (Nat.land b.u a.n) 0) = true) :
    slow1Pair0 r v c a b = true := by
  obtain ⟨g1, g2, g3⟩ := tryKeeps1_guard ht
  simp only [slow1Pair0, h1, h2, g1, g2, g3, ht, Bool.true_and, Bool.or_true]
lemma slow1Pair1_and {r v c a b}
    (h1 : isNotSpec0 a.tg = true) (h2 : isNotSpec0 b.tg = true)
    (ht : tryKeeps1 r v a.w.1 b.w.1
      (Nat.lor (Nat.xor (Nat.land a.p b.p) (Nat.land a.n b.n)) (takeTwo c a.s b.s))
      a.s b.s ((Nat.land a.p b.p, Nat.land a.n b.n),
        if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone)
      a.w b.w (isNoneTag a.tg) (isNoneTag b.tg)
      (Nat.beq (Nat.land a.up b.p) a.up && Nat.beq (Nat.land a.un b.n) a.un)
      (Nat.beq (Nat.land b.up a.p) b.up && Nat.beq (Nat.land b.un a.n) b.un) = true) :
    slow1Pair1 r v c a b = true := by
  obtain ⟨g1, g2, g3⟩ := tryKeeps1_guard ht
  simp only [slow1Pair1, h1, h2, g1, g2, g3, ht, Bool.true_and, Bool.true_or]
lemma slow1Pair1_or {r v c a b}
    (h1 : isNotSpec1 a.tg = true) (h2 : isNotSpec1 b.tg = true)
    (ht : tryKeeps1 r v a.w.1 b.w.1
      (Nat.lor (Nat.xor (Nat.lor a.p b.p) (Nat.lor a.n b.n)) (takeTwo c a.s b.s))
      a.s b.s ((Nat.lor a.p b.p, Nat.lor a.n b.n), .tNone)
      (a.w.1, if isDeg3Tag a.tg then .tSpec0 else .tNone)
      (b.w.1, if isDeg3Tag b.tg then .tSpec0 else .tNone)
      (isNotSpec0 a.tg) (isNotSpec0 b.tg)
      (Nat.beq (Nat.land a.up b.n) 0 && Nat.beq (Nat.land a.un b.p) 0)
      (Nat.beq (Nat.land b.up a.n) 0 && Nat.beq (Nat.land b.un a.p) 0) = true) :
    slow1Pair1 r v c a b = true := by
  obtain ⟨g1, g2, g3⟩ := tryKeeps1_guard ht
  simp only [slow1Pair1, h1, h2, g1, g2, g3, ht, Bool.true_and, Bool.or_true]
lemma slow2Pair0_and {r v c a b}
    (h1 : isNotSpec0 a.tg = true) (h2 : isNotSpec0 b.tg = true)
    (ga : (isNoneTag a.tg || Nat.beq (Nat.land a.u b.p) a.u) = true)
    (gb : (isNoneTag b.tg || Nat.beq (Nat.land b.u a.p) b.u) = true)
    (ht : tryKeeps2 r v a.w.1 b.w.1
      (Nat.lor (Nat.land (Nat.land a.p b.p) (Nat.xor (Nat.land a.n b.n) top)) (takeTwo c a.s b.s))
      a.s b.s ((Nat.land a.p b.p, Nat.land a.n b.n),
        if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone)
      a.w b.w (isNoneTag a.tg) (isNoneTag b.tg) = true) :
    slow2Pair0 r v c a b = true := by
  simp only [slow2Pair0, h1, h2, ga, gb, ht, Bool.true_and, Bool.true_or]
lemma slow2Pair0_or {r v c a b}
    (h1 : isNotSpec1 a.tg = true) (h2 : isNotSpec1 b.tg = true)
    (ga : (isNotSpec0 a.tg || Nat.beq (Nat.land a.u b.n) 0) = true)
    (gb : (isNotSpec0 b.tg || Nat.beq (Nat.land b.u a.n) 0) = true)
    (ht : tryKeeps2 r v a.w.1 b.w.1
      (Nat.lor (Nat.land (Nat.lor a.p b.p) (Nat.xor (Nat.lor a.n b.n) top)) (takeTwo c a.s b.s))
      a.s b.s ((Nat.lor a.p b.p, Nat.lor a.n b.n), .tNone)
      (a.w.1, if isDeg3Tag a.tg then .tSpec0 else .tNone)
      (b.w.1, if isDeg3Tag b.tg then .tSpec0 else .tNone)
      (isNotSpec0 a.tg) (isNotSpec0 b.tg) = true) :
    slow2Pair0 r v c a b = true := by
  simp only [slow2Pair0, h1, h2, ga, gb, ht, Bool.true_and, Bool.or_true]
lemma slow2Pair1_and {r v c a b}
    (h1 : isNotSpec0 a.tg = true) (h2 : isNotSpec0 b.tg = true)
    (ga : (isNoneTag a.tg || (Nat.beq (Nat.land a.up b.p) a.up && Nat.beq (Nat.land a.un b.n) a.un)) = true)
    (gb : (isNoneTag b.tg || (Nat.beq (Nat.land b.up a.p) b.up && Nat.beq (Nat.land b.un a.n) b.un)) = true)
    (ht : tryKeeps2 r v a.w.1 b.w.1
      (Nat.lor (Nat.xor (Nat.land a.p b.p) (Nat.land a.n b.n)) (takeTwo c a.s b.s))
      a.s b.s ((Nat.land a.p b.p, Nat.land a.n b.n),
        if isDeg3Tag a.tg || isDeg3Tag b.tg then Tag.tSpec0 else Tag.tNone)
      a.w b.w (isNoneTag a.tg) (isNoneTag b.tg) = true) :
    slow2Pair1 r v c a b = true := by
  simp only [slow2Pair1, h1, h2, ga, gb, ht, Bool.true_and, Bool.true_or]
lemma slow2Pair1_or {r v c a b}
    (h1 : isNotSpec1 a.tg = true) (h2 : isNotSpec1 b.tg = true)
    (ga : (isNotSpec0 a.tg || (Nat.beq (Nat.land a.up b.n) 0 && Nat.beq (Nat.land a.un b.p) 0)) = true)
    (gb : (isNotSpec0 b.tg || (Nat.beq (Nat.land b.up a.n) 0 && Nat.beq (Nat.land b.un a.p) 0)) = true)
    (ht : tryKeeps2 r v a.w.1 b.w.1
      (Nat.lor (Nat.xor (Nat.lor a.p b.p) (Nat.lor a.n b.n)) (takeTwo c a.s b.s))
      a.s b.s ((Nat.lor a.p b.p, Nat.lor a.n b.n), .tNone)
      (a.w.1, if isDeg3Tag a.tg then .tSpec0 else .tNone)
      (b.w.1, if isDeg3Tag b.tg then .tSpec0 else .tNone)
      (isNotSpec0 a.tg) (isNotSpec0 b.tg) = true) :
    slow2Pair1 r v c a b = true := by
  simp only [slow2Pair1, h1, h2, ga, gb, ht, Bool.true_and, Bool.or_true]
lemma pair_and_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {τ : Sig → Tag} {v : List Wire}
    {r : List Wire → Bool}
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hrep : Represents v (insert a (insert b U)) τ) (hle : m ≤ k)
    (fresh : bin false a b ∉ insert a (insert b U))
    (hra : τ a ≠ .tSpec0 ∧ (τ a ≠ .tNone → a ∉ U))
    (hrb : τ b ≠ .tSpec0 ∧ (τ b ≠ .tNone → b ∉ U))
    (l : TRestricted m t (insert (bin false a b) U) (updAndTag τ a b))
    (ih : ∀ w : List Wire, Represents w (insert (bin false a b) U) (updAndTag τ a b) → r w = true) :
    let lim := k - t + 1
    let c0 := coverageW false v
    let c1 := coverageW true v
    (t = 0 →
      (v.length = lim + 1 → fastPair0 r v c0 (mkAct0 c0.2.1 (a, τ a)) (mkAct0 c0.2.1 (b, τ b)) = true) ∧
      (v.length = lim → slow1Pair0 r v c0 (mkAct0 c0.2.1 (a, τ a)) (mkAct0 c0.2.1 (b, τ b)) = true) ∧
      slow2Pair0 r v c0 (mkAct0 c0.2.1 (a, τ a)) (mkAct0 c0.2.1 (b, τ b)) = true) ∧
    (t ≠ 0 →
      (v.length = lim + 1 → fastPair1 r v c1 (mkAct1 c1.2.1 (a, τ a)) (mkAct1 c1.2.1 (b, τ b)) = true) ∧
      (v.length = lim → slow1Pair1 r v c1 (mkAct1 c1.2.1 (a, τ a)) (mkAct1 c1.2.1 (b, τ b)) = true) ∧
      slow2Pair1 r v c1 (mkAct1 c1.2.1 (a, τ a)) (mkAct1 c1.2.1 (b, τ b)) = true) := by
  obtain ⟨hndS, heS, htag⟩ := hrep
  have hval : ∀ x ∈ sigsOf v, Valid x := by
    intro x hx
    rcases Finset.mem_insert.mp (heS ▸ List.mem_toFinset.mpr hx) with rfl | hx1
    · exact ha.1
    rcases Finset.mem_insert.mp hx1 with rfl | hxU
    · exact hb.1
    · exact (live_proper l.live x (Finset.mem_insert_of_mem hxU)).1
  have ahS : a ∈ sigsOf v := List.mem_toFinset.mp (heS.symm ▸ Finset.mem_insert_self _ _)
  have bhS : b ∈ sigsOf v := List.mem_toFinset.mp (heS.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have ah : (a, τ a) ∈ v := (mem_sigsOf_iff htag).mpr ahS
  have bh : (b, τ b) ∈ v := (mem_sigsOf_iff htag).mpr bhS
  let rest := droppedW [a, b] v
  let gTag : Tag := if isDeg3Tag (τ a) || isDeg3Tag (τ b) then .tSpec0 else .tNone
  let g : Wire := (bin false a b, gTag)
  let h : List Wire := (if a ∈ U then [(a, τ a)] else []) ++ (if b ∈ U then [(b, τ b)] else [])
  have hSigsH : sigsOf h = keepOf U [a, b] := by
    by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U <;> simp [h, sigsOf, keepOf, haU, hbU]
  obtain ⟨hn, eq⟩ := edit_list (del := [a, b]) (U := U) hndS (by simp [hab]) (by simpa using heS)
  have hSigsHR : sigsOf (h ++ rest) = keepOf U [a, b] ++ dropped [a, b] (sigsOf v) := by
    change (h ++ rest).map Prod.fst = _
    rw [List.map_append, show h.map Prod.fst = keepOf U [a, b] from hSigsH,
      show rest.map Prod.fst = dropped [a, b] (sigsOf v) from sigsOf_droppedW [a, b] v]
  have nn : bin false a b ∉ sigsOf v := fun hm => fresh (heS ▸ List.mem_toFinset.mpr hm)
  have nz : bin false a b ∉ U := fun hm => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
  have hnd : (sigsOf (g :: (h ++ rest))).Nodup := by
    change (bin false a b :: sigsOf (h ++ rest)).Nodup; rw [hSigsHR]
    exact List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm), hn⟩
  have e : (sigsOf (g :: (h ++ rest))).toFinset = insert (bin false a b) U := by
    change (bin false a b :: sigsOf (h ++ rest)).toFinset = _; rw [List.toFinset_cons, hSigsHR, eq]
  have htag' : ∀ w ∈ g :: (h ++ rest), w.2 = updAndTag τ a b w.1 := by
    intro w hw; rcases List.mem_cons.mp hw with rfl | hw'
    · simp only [g, gTag, updAndTag, ite_true]; cases τ a <;> cases τ b <;> rfl
    · have hwV : w ∈ v := by
        rcases List.mem_append.mp hw' with hh | hr
        · rcases List.mem_append.mp hh with h1 | h2
          · by_cases haU : a ∈ U
            · simp only [haU, ite_true, List.mem_singleton] at h1; exact h1 ▸ ah
            · simp [haU] at h1
          · by_cases hbU : b ∈ U
            · simp only [hbU, ite_true, List.mem_singleton] at h2; exact h2 ▸ bh
            · simp [hbU] at h2
        · exact List.mem_of_mem_filter hr
      have hwNe : w.1 ≠ bin false a b := fun heq => nn (heq ▸ List.mem_map_of_mem hwV)
      simp [updAndTag, hwNe, htag w hwV]
  have hr := ih _ ⟨hnd, e, htag'⟩
  obtain ⟨ht, hc⟩ := live_size l.live
  rw [← e, List.toFinset_card_of_nodup hnd] at hc
  simp only [sigsOf, List.map_cons, List.map_append, List.length_cons, List.length_append,
    List.length_map] at hc
  have hav : gateAvail (bin false a b) v = true :=
    gateAvail_eq_true nn (live_proper l.live _ (Finset.mem_insert_self _ _))
  have hnsa : isNotSpec0 (τ a) = true := by cases hta : τ a <;> simp [isNotSpec0]; exact hra.1 hta
  have hnsb : isNotSpec0 (τ b) = true := by cases htb : τ b <;> simp [isNotSpec0]; exact hrb.1 htb
  have hka : a ∈ U → isNoneTag (τ a) = true := fun hm => by
    cases hta : τ a <;> simp [isNoneTag]; all_goals exact hra.2 (by simp [hta]) hm
  have hkb : b ∈ U → isNoneTag (τ b) = true := fun hm => by
    cases htb : τ b <;> simp [isNoneTag]; all_goals exact hrb.2 (by simp [htb]) hm
  have hdrop : dropTwo a b v = rest := dropTwo_eq a b v
  have cv := live_cover l.live e
  simp only [sigsOf, List.map_cons, List.map_append, unionSep, union_append] at cv
  have hcv' : (sep (decide (0 < t)) (bin false a b) ||| unionSep (decide (0 < t)) (sigsOf rest)) |||
      unionSepW (decide (0 < t)) h = top := by
    rw [unionSepW_eq, ← cv]; unfold sigsOf; ac_rfl
  obtain ⟨hlen, hmask⟩ := two_rest (decide (0 < t)) hndS hval ahS bhS hab
  rw [sigsOf_length, ← sigsOf_droppedW, sigsOf_length] at hlen
  change v.length - 2 = rest.length at hlen
  rw [← sigsOf_droppedW] at hmask
  change takeTwo (coverage (decide (0 < t)) (sigsOf v)) (sep (decide (0 < t)) a) (sep (decide (0 < t)) b) =
    unionSep (decide (0 < t)) (sigsOf rest) at hmask
  have hdisjAB := two_rest_disj (decide (0 < t)) hndS hval ahS bhS hab
  have hdisjBA := two_rest_disj (decide (0 < t)) hndS hval bhS ahS hab.symm
  have hvc := validCov_coverage (decide (0 < t)) hval
  constructor
  · intro ht0; subst ht0
    have hdt0 : decide (0 < 0) = false := rfl
    rw [hdt0] at hcv' hmask hdisjAB hdisjBA hvc
    have hcv0 : Nat.lor (Nat.lor (sep0 (bin false a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b)))
        (unionSepW false h) = top := by simpa [hmask, sep0_eq] using hcv'
    have h0zero : ∀ x : Nat, Nat.land x 0 = 0 := fun x => Nat.and_zero x
    have huA0 : a ∉ U → Nat.land (Nat.land (coverage false (sigsOf v)).2.1 (sep0 a)) b.1 =
        Nat.land (coverage false (sigsOf v)).2.1 (sep0 a) := fun hna => by
      by_cases hbU : b ∈ U
      · exact unique_and_0 hvc (by simpa [sep0_eq] using hdisjAB) (by simpa [h, hna, hbU, unionSepW, sep0_eq] using hcv0)
      · exact unique_and_0 hvc (h0zero _) (by simpa [h, hna, hbU, unionSepW] using hcv0)
    have huB0 : b ∉ U → Nat.land (Nat.land (coverage false (sigsOf v)).2.1 (sep0 b)) a.1 =
        Nat.land (coverage false (sigsOf v)).2.1 (sep0 b) := fun hnb => by
      have hcomm : Nat.lor (Nat.lor (sep0 (bin false b a)) (takeTwo (coverage false (sigsOf v)) (sep0 b) (sep0 a)))
          (unionSepW false h) = top := by
        rw [bin_comm]; simpa [takeTwo, Nat.or_comm, Nat.and_comm] using hcv0
      by_cases haU : a ∈ U
      · exact unique_and_0 hvc (by simpa [sep0_eq] using hdisjBA) (by simpa [h, haU, hnb, unionSepW, sep0_eq] using hcomm)
      · exact unique_and_0 hvc (h0zero _) (by simpa [h, haU, hnb, unionSepW] using hcomm)
    refine ⟨?_, ?_, ?_⟩
    · intro hlv
      have hh0 : h.length = 0 := by omega
      have hna : a ∉ U := fun hm => by simp [h, hm] at hh0
      have hnb : b ∉ U := fun hm => by simp [h, hm] at hh0
      have htop : Nat.lor (sep0 (bin false a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b)) = top := by
        simpa [h, hna, hnb, unionSepW] using hcv0
      have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, hna, hnb] using hr
      rw [coverageW_eq]
      exact fastPair0_and hnsa hnsb (huA0 hna) (huB0 hnb) htop hav hr0
    · intro hlv
      have hh1 : h.length ≤ 1 := by omega
      rw [coverageW_eq]
      apply slow1Pair0_and hnsa hnsb
      by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U
      · simp [h, haU, hbU] at hh1
      · have htopA : Nat.lor (Nat.lor (sep0 (bin false a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b))) (sep0 a) = top := by
          simpa [h, haU, hbU, unionSepW, sep0_eq] using hcv0
        have hrA : r (g :: (a, τ a) :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact tryKeeps1_A (hka haU) (Nat.beq_eq.mpr (huB0 hbU)) htopA hav hrA
      · have htopB : Nat.lor (Nat.lor (sep0 (bin false a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b))) (sep0 b) = top := by
          simpa [h, haU, hbU, unionSepW, sep0_eq] using hcv0
        have hrB : r (g :: (b, τ b) :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact tryKeeps1_B (hkb hbU) (Nat.beq_eq.mpr (huA0 haU)) htopB hav hrB
      · have htop : Nat.lor (sep0 (bin false a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b)) = top := by
          simpa [h, haU, hbU, unionSepW] using hcv0
        have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact tryKeeps1_0 (Nat.beq_eq.mpr (huA0 haU)) (Nat.beq_eq.mpr (huB0 hbU)) htop hav hr0
    · rw [coverageW_eq]
      by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U
      · have htopAB : Nat.lor (Nat.lor (Nat.lor (sep0 (bin false a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b))) (sep0 a)) (sep0 b) = top := by
          have : unionSepW false h = sep0 a ||| sep0 b := by simp [h, haU, hbU, unionSepW, sep0_eq]
          rw [this] at hcv0; exact (Nat.or_assoc _ _ _).trans hcv0
        have hrAB : r (g :: (a, τ a) :: (b, τ b) :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact slow2Pair0_and hnsa hnsb (bor_l (hka haU)) (bor_l (hkb hbU)) (tryKeeps2_AB (hka haU) (hkb hbU) htopAB hav hrAB)
      · have htopA : Nat.lor (Nat.lor (sep0 (bin false a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b))) (sep0 a) = top := by
          simpa [h, haU, hbU, unionSepW, sep0_eq] using hcv0
        have hrA : r (g :: (a, τ a) :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact slow2Pair0_and hnsa hnsb (bor_l (hka haU)) (bor_r (Nat.beq_eq.mpr (huB0 hbU))) (tryKeeps2_A (hka haU) htopA hav hrA)
      · have htopB : Nat.lor (Nat.lor (sep0 (bin false a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b))) (sep0 b) = top := by
          simpa [h, haU, hbU, unionSepW, sep0_eq] using hcv0
        have hrB : r (g :: (b, τ b) :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact slow2Pair0_and hnsa hnsb (bor_r (Nat.beq_eq.mpr (huA0 haU))) (bor_l (hkb hbU)) (tryKeeps2_B (hkb hbU) htopB hav hrB)
      · have htop : Nat.lor (sep0 (bin false a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b)) = top := by
          simpa [h, haU, hbU, unionSepW] using hcv0
        have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact slow2Pair0_and hnsa hnsb (bor_r (Nat.beq_eq.mpr (huA0 haU))) (bor_r (Nat.beq_eq.mpr (huB0 hbU))) (tryKeeps2_0 htop hav hr0)
  · intro ht0
    have hdt : decide (0 < t) = true := decide_eq_true (by omega)
    rw [hdt] at hcv' hmask hdisjAB hdisjBA hvc
    have hcv1 : Nat.lor (Nat.lor (sep1 (bin false a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b)))
        (unionSepW true h) = top := by simpa [hmask, sep1_eq] using hcv'
    have h0zero : ∀ x : Nat, Nat.land x 0 = 0 := fun x => Nat.and_zero x
    have huA1 : a ∉ U →
        Nat.land (Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 a)) a.1) b.1 =
          Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 a)) a.1 ∧
        Nat.land (Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 a)) a.2) b.2 =
          Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 a)) a.2 := fun hna => by
      by_cases hbU : b ∈ U
      · exact unique_and_1 hvc (by simpa [sep1_eq] using hdisjAB) (by simpa [h, hna, hbU, unionSepW, sep1_eq] using hcv1)
      · exact unique_and_1 hvc (h0zero _) (by simpa [h, hna, hbU, unionSepW] using hcv1)
    have huB1 : b ∉ U →
        Nat.land (Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 b)) b.1) a.1 =
          Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 b)) b.1 ∧
        Nat.land (Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 b)) b.2) a.2 =
          Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 b)) b.2 := fun hnb => by
      have hcomm : Nat.lor (Nat.lor (sep1 (bin false b a)) (takeTwo (coverage true (sigsOf v)) (sep1 b) (sep1 a)))
          (unionSepW true h) = top := by
        rw [bin_comm]; simpa [takeTwo, Nat.or_comm, Nat.and_comm] using hcv1
      by_cases haU : a ∈ U
      · exact unique_and_1 hvc (by simpa [sep1_eq] using hdisjBA) (by simpa [h, haU, hnb, unionSepW, sep1_eq] using hcomm)
      · exact unique_and_1 hvc (h0zero _) (by simpa [h, haU, hnb, unionSepW] using hcomm)
    refine ⟨?_, ?_, ?_⟩
    · intro hlv
      have hh0 : h.length = 0 := by omega
      have hna : a ∉ U := fun hm => by simp [h, hm] at hh0
      have hnb : b ∉ U := fun hm => by simp [h, hm] at hh0
      have htop : Nat.lor (sep1 (bin false a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b)) = top := by
        simpa [h, hna, hnb, unionSepW] using hcv1
      have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, hna, hnb] using hr
      have ⟨u1, u2⟩ := huA1 hna; have ⟨v1, v2⟩ := huB1 hnb
      rw [coverageW_eq]
      exact fastPair1_and hnsa hnsb u1 v1 u2 v2 htop hav hr0
    · intro hlv
      have hh1 : h.length ≤ 1 := by omega
      rw [coverageW_eq]
      apply slow1Pair1_and hnsa hnsb
      by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U
      · simp [h, haU, hbU] at hh1
      · have htopA : Nat.lor (Nat.lor (sep1 (bin false a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b))) (sep1 a) = top := by
          simpa [h, haU, hbU, unionSepW, sep1_eq] using hcv1
        have hrA : r (g :: (a, τ a) :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨v1, v2⟩ := huB1 hbU
        exact tryKeeps1_A (hka haU) (band2 (Nat.beq_eq.mpr v1) (Nat.beq_eq.mpr v2)) htopA hav hrA
      · have htopB : Nat.lor (Nat.lor (sep1 (bin false a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b))) (sep1 b) = top := by
          simpa [h, haU, hbU, unionSepW, sep1_eq] using hcv1
        have hrB : r (g :: (b, τ b) :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨u1, u2⟩ := huA1 haU
        exact tryKeeps1_B (hkb hbU) (band2 (Nat.beq_eq.mpr u1) (Nat.beq_eq.mpr u2)) htopB hav hrB
      · have htop : Nat.lor (sep1 (bin false a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b)) = top := by
          simpa [h, haU, hbU, unionSepW] using hcv1
        have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨u1, u2⟩ := huA1 haU; have ⟨v1, v2⟩ := huB1 hbU
        exact tryKeeps1_0 (band2 (Nat.beq_eq.mpr u1) (Nat.beq_eq.mpr u2)) (band2 (Nat.beq_eq.mpr v1) (Nat.beq_eq.mpr v2)) htop hav hr0
    · rw [coverageW_eq]
      by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U
      · have htopAB : Nat.lor (Nat.lor (Nat.lor (sep1 (bin false a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b))) (sep1 a)) (sep1 b) = top := by
          have : unionSepW true h = sep1 a ||| sep1 b := by simp [h, haU, hbU, unionSepW, sep1_eq]
          rw [this] at hcv1; exact (Nat.or_assoc _ _ _).trans hcv1
        have hrAB : r (g :: (a, τ a) :: (b, τ b) :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact slow2Pair1_and hnsa hnsb (bor_l (hka haU)) (bor_l (hkb hbU)) (tryKeeps2_AB (hka haU) (hkb hbU) htopAB hav hrAB)
      · have htopA : Nat.lor (Nat.lor (sep1 (bin false a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b))) (sep1 a) = top := by
          simpa [h, haU, hbU, unionSepW, sep1_eq] using hcv1
        have hrA : r (g :: (a, τ a) :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨v1, v2⟩ := huB1 hbU
        exact slow2Pair1_and hnsa hnsb (bor_l (hka haU)) (bor_r (band2 (Nat.beq_eq.mpr v1) (Nat.beq_eq.mpr v2))) (tryKeeps2_A (hka haU) htopA hav hrA)
      · have htopB : Nat.lor (Nat.lor (sep1 (bin false a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b))) (sep1 b) = top := by
          simpa [h, haU, hbU, unionSepW, sep1_eq] using hcv1
        have hrB : r (g :: (b, τ b) :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨u1, u2⟩ := huA1 haU
        exact slow2Pair1_and hnsa hnsb (bor_r (band2 (Nat.beq_eq.mpr u1) (Nat.beq_eq.mpr u2))) (bor_l (hkb hbU)) (tryKeeps2_B (hkb hbU) htopB hav hrB)
      · have htop : Nat.lor (sep1 (bin false a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b)) = top := by
          simpa [h, haU, hbU, unionSepW] using hcv1
        have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨u1, u2⟩ := huA1 haU; have ⟨v1, v2⟩ := huB1 hbU
        exact slow2Pair1_and hnsa hnsb (bor_r (band2 (Nat.beq_eq.mpr u1) (Nat.beq_eq.mpr u2))) (bor_r (band2 (Nat.beq_eq.mpr v1) (Nat.beq_eq.mpr v2))) (tryKeeps2_0 htop hav hr0)
lemma pair_or_found {m t k : Nat} {U : Finset Sig} {a b : Sig} {τ : Sig → Tag} {v : List Wire}
    {r : List Wire → Bool}
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hrep : Represents v (insert a (insert b U)) τ) (hle : m ≤ k)
    (fresh : bin true a b ∉ insert a (insert b U))
    (hra : τ a ≠ .tSpec1 ∧ (τ a = .tSpec0 → a ∉ U))
    (hrb : τ b ≠ .tSpec1 ∧ (τ b = .tSpec0 → b ∉ U))
    (l : TRestricted m t (insert (bin true a b) U) (updOrTag τ a b))
    (ih : ∀ w : List Wire, Represents w (insert (bin true a b) U) (updOrTag τ a b) → r w = true) :
    let lim := k - t + 1
    let c0 := coverageW false v
    let c1 := coverageW true v
    (t = 0 →
      (v.length = lim + 1 → fastPair0 r v c0 (mkAct0 c0.2.1 (a, τ a)) (mkAct0 c0.2.1 (b, τ b)) = true) ∧
      (v.length = lim → slow1Pair0 r v c0 (mkAct0 c0.2.1 (a, τ a)) (mkAct0 c0.2.1 (b, τ b)) = true) ∧
      slow2Pair0 r v c0 (mkAct0 c0.2.1 (a, τ a)) (mkAct0 c0.2.1 (b, τ b)) = true) ∧
    (t ≠ 0 →
      (v.length = lim + 1 → fastPair1 r v c1 (mkAct1 c1.2.1 (a, τ a)) (mkAct1 c1.2.1 (b, τ b)) = true) ∧
      (v.length = lim → slow1Pair1 r v c1 (mkAct1 c1.2.1 (a, τ a)) (mkAct1 c1.2.1 (b, τ b)) = true) ∧
      slow2Pair1 r v c1 (mkAct1 c1.2.1 (a, τ a)) (mkAct1 c1.2.1 (b, τ b)) = true) := by
  obtain ⟨hndS, heS, htag⟩ := hrep
  have hval : ∀ x ∈ sigsOf v, Valid x := by
    intro x hx
    rcases Finset.mem_insert.mp (heS ▸ List.mem_toFinset.mpr hx) with rfl | hx1
    · exact ha.1
    rcases Finset.mem_insert.mp hx1 with rfl | hxU
    · exact hb.1
    · exact (live_proper l.live x (Finset.mem_insert_of_mem hxU)).1
  have ahS : a ∈ sigsOf v := List.mem_toFinset.mp (heS.symm ▸ Finset.mem_insert_self _ _)
  have bhS : b ∈ sigsOf v := List.mem_toFinset.mp (heS.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  let rest := droppedW [a, b] v
  let g : Wire := (bin true a b, .tNone)
  let wa : Wire := (a, if isDeg3Tag (τ a) then .tSpec0 else .tNone)
  let wb : Wire := (b, if isDeg3Tag (τ b) then .tSpec0 else .tNone)
  let h : List Wire := (if a ∈ U then [wa] else []) ++ (if b ∈ U then [wb] else [])
  have hSigsH : sigsOf h = keepOf U [a, b] := by
    by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U <;> simp [h, wa, wb, sigsOf, keepOf, haU, hbU]
  obtain ⟨hn, eq⟩ := edit_list (del := [a, b]) (U := U) hndS (by simp [hab]) (by simpa using heS)
  have hSigsHR : sigsOf (h ++ rest) = keepOf U [a, b] ++ dropped [a, b] (sigsOf v) := by
    change (h ++ rest).map Prod.fst = _
    rw [List.map_append, show h.map Prod.fst = keepOf U [a, b] from hSigsH,
      show rest.map Prod.fst = dropped [a, b] (sigsOf v) from sigsOf_droppedW [a, b] v]
  have nn : bin true a b ∉ sigsOf v := fun hm => fresh (heS ▸ List.mem_toFinset.mpr hm)
  have nz : bin true a b ∉ U := fun hm => fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
  have hnd : (sigsOf (g :: (h ++ rest))).Nodup := by
    change (bin true a b :: sigsOf (h ++ rest)).Nodup; rw [hSigsHR]
    exact List.nodup_cons.mpr ⟨fun hm => nz (eq ▸ List.mem_toFinset.mpr hm), hn⟩
  have e : (sigsOf (g :: (h ++ rest))).toFinset = insert (bin true a b) U := by
    change (bin true a b :: sigsOf (h ++ rest)).toFinset = _; rw [List.toFinset_cons, hSigsHR, eq]
  have htag' : ∀ w ∈ g :: (h ++ rest), w.2 = updOrTag τ a b w.1 := by
    intro w hw; rcases List.mem_cons.mp hw with rfl | hw'
    · simp [g, updOrTag]
    · rcases List.mem_append.mp hw' with hh | hr
      · rcases List.mem_append.mp hh with h1 | h2
        · by_cases haU : a ∈ U
          · simp only [haU, ite_true, List.mem_singleton] at h1; subst w
            have hneG : a ≠ bin true a b := fun eq' => fresh (eq' ▸ Finset.mem_insert_self _ _)
            have hna0 : τ a ≠ .tSpec0 := fun h0 => hra.2 h0 haU
            simp only [wa, updOrTag, hneG, ite_false]
            cases hta : τ a <;> simp_all [isDeg3Tag]
          · simp [haU] at h1
        · by_cases hbU : b ∈ U
          · simp only [hbU, ite_true, List.mem_singleton] at h2; subst w
            have hneG : b ≠ bin true a b := fun eq' =>
              fresh (eq' ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
            have hnb0 : τ b ≠ .tSpec0 := fun h0 => hrb.2 h0 hbU
            simp only [wb, updOrTag, hneG, hab.symm, false_and, ite_false]
            cases htb : τ b <;> simp_all [isDeg3Tag]
          · simp [hbU] at h2
      · have hwV := List.mem_of_mem_filter hr
        have hnot : w.1 ≠ a ∧ w.1 ≠ b := by
          have hf := (List.mem_filter.mp hr).2
          simp only [Bool.not_eq_true', List.contains_eq_mem, decide_eq_false_iff_not,
            List.mem_cons, List.not_mem_nil, or_false, not_or] at hf
          exact hf
        have hneG : w.1 ≠ bin true a b := fun eq' => nn (eq' ▸ List.mem_map_of_mem hwV)
        simp [updOrTag, hneG, hnot.1, hnot.2, htag w hwV]
  have hr := ih _ ⟨hnd, e, htag'⟩
  obtain ⟨ht, hc⟩ := live_size l.live
  rw [← e, List.toFinset_card_of_nodup hnd] at hc
  simp only [sigsOf, List.map_cons, List.map_append, List.length_cons, List.length_append,
    List.length_map] at hc
  have hav : gateAvail (bin true a b) v = true :=
    gateAvail_eq_true nn (live_proper l.live _ (Finset.mem_insert_self _ _))
  have hnsa : isNotSpec1 (τ a) = true := by cases hta : τ a <;> simp [isNotSpec1]; exact hra.1 hta
  have hnsb : isNotSpec1 (τ b) = true := by cases htb : τ b <;> simp [isNotSpec1]; exact hrb.1 htb
  have hka : a ∈ U → isNotSpec0 (τ a) = true := fun hm => by
    cases hta : τ a <;> simp [isNotSpec0]; exact hra.2 hta hm
  have hkb : b ∈ U → isNotSpec0 (τ b) = true := fun hm => by
    cases htb : τ b <;> simp [isNotSpec0]; exact hrb.2 htb hm
  have hdrop : dropTwo a b v = rest := dropTwo_eq a b v
  have cv := live_cover l.live e
  simp only [sigsOf, List.map_cons, List.map_append, unionSep, union_append] at cv
  have hcv' : (sep (decide (0 < t)) (bin true a b) ||| unionSep (decide (0 < t)) (sigsOf rest)) |||
      unionSepW (decide (0 < t)) h = top := by
    rw [unionSepW_eq, ← cv]; unfold sigsOf; ac_rfl
  obtain ⟨hlen, hmask⟩ := two_rest (decide (0 < t)) hndS hval ahS bhS hab
  rw [sigsOf_length, ← sigsOf_droppedW, sigsOf_length] at hlen
  change v.length - 2 = rest.length at hlen
  rw [← sigsOf_droppedW] at hmask
  change takeTwo (coverage (decide (0 < t)) (sigsOf v)) (sep (decide (0 < t)) a) (sep (decide (0 < t)) b) =
    unionSep (decide (0 < t)) (sigsOf rest) at hmask
  have hdisjAB := two_rest_disj (decide (0 < t)) hndS hval ahS bhS hab
  have hdisjBA := two_rest_disj (decide (0 < t)) hndS hval bhS ahS hab.symm
  have hvc := validCov_coverage (decide (0 < t)) hval
  constructor
  · intro ht0; subst ht0
    have hdt0 : decide (0 < 0) = false := rfl
    rw [hdt0] at hcv' hmask hdisjAB hdisjBA hvc
    have hcv0 : Nat.lor (Nat.lor (sep0 (bin true a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b)))
        (unionSepW false h) = top := by simpa [hmask, sep0_eq] using hcv'
    have h0zero : ∀ x : Nat, Nat.land x 0 = 0 := fun x => Nat.and_zero x
    have huA0 : a ∉ U → Nat.land (Nat.land (coverage false (sigsOf v)).2.1 (sep0 a)) b.2 = 0 := fun hna => by
      by_cases hbU : b ∈ U
      · exact unique_or_0 hvc (by simpa [sep0_eq] using hdisjAB) (by simpa [h, wa, wb, hna, hbU, unionSepW, sep0_eq] using hcv0)
      · exact unique_or_0 hvc (h0zero _) (by simpa [h, hna, hbU, unionSepW] using hcv0)
    have huB0 : b ∉ U → Nat.land (Nat.land (coverage false (sigsOf v)).2.1 (sep0 b)) a.2 = 0 := fun hnb => by
      have hcomm : Nat.lor (Nat.lor (sep0 (bin true b a)) (takeTwo (coverage false (sigsOf v)) (sep0 b) (sep0 a)))
          (unionSepW false h) = top := by
        rw [bin_comm]; simpa [takeTwo, Nat.or_comm, Nat.and_comm] using hcv0
      by_cases haU : a ∈ U
      · exact unique_or_0 hvc (by simpa [sep0_eq] using hdisjBA) (by simpa [h, wa, wb, haU, hnb, unionSepW, sep0_eq] using hcomm)
      · exact unique_or_0 hvc (h0zero _) (by simpa [h, haU, hnb, unionSepW] using hcomm)
    refine ⟨?_, ?_, ?_⟩
    · intro hlv
      have hh0 : h.length = 0 := by omega
      have hna : a ∉ U := fun hm => by simp [h, hm] at hh0
      have hnb : b ∉ U := fun hm => by simp [h, hm] at hh0
      have htop : Nat.lor (sep0 (bin true a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b)) = top := by
        simpa [h, hna, hnb, unionSepW] using hcv0
      have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, hna, hnb] using hr
      rw [coverageW_eq]
      exact fastPair0_or hnsa hnsb (huA0 hna) (huB0 hnb) htop hav hr0
    · intro hlv
      have hh1 : h.length ≤ 1 := by omega
      rw [coverageW_eq]
      apply slow1Pair0_or hnsa hnsb
      by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U
      · simp [h, haU, hbU] at hh1
      · have htopA : Nat.lor (Nat.lor (sep0 (bin true a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b))) (sep0 a) = top := by
          simpa [h, wa, haU, hbU, unionSepW, sep0_eq] using hcv0
        have hrA : r (g :: wa :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact tryKeeps1_A (hka haU) (Nat.beq_eq.mpr (huB0 hbU)) htopA hav hrA
      · have htopB : Nat.lor (Nat.lor (sep0 (bin true a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b))) (sep0 b) = top := by
          simpa [h, wb, haU, hbU, unionSepW, sep0_eq] using hcv0
        have hrB : r (g :: wb :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact tryKeeps1_B (hkb hbU) (Nat.beq_eq.mpr (huA0 haU)) htopB hav hrB
      · have htop : Nat.lor (sep0 (bin true a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b)) = top := by
          simpa [h, haU, hbU, unionSepW] using hcv0
        have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact tryKeeps1_0 (Nat.beq_eq.mpr (huA0 haU)) (Nat.beq_eq.mpr (huB0 hbU)) htop hav hr0
    · rw [coverageW_eq]
      by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U
      · have htopAB : Nat.lor (Nat.lor (Nat.lor (sep0 (bin true a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b))) (sep0 a)) (sep0 b) = top := by
          have : unionSepW false h = sep0 a ||| sep0 b := by simp [h, wa, wb, haU, hbU, unionSepW, sep0_eq]
          rw [this] at hcv0; exact (Nat.or_assoc _ _ _).trans hcv0
        have hrAB : r (g :: wa :: wb :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact slow2Pair0_or hnsa hnsb (bor_l (hka haU)) (bor_l (hkb hbU)) (tryKeeps2_AB (hka haU) (hkb hbU) htopAB hav hrAB)
      · have htopA : Nat.lor (Nat.lor (sep0 (bin true a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b))) (sep0 a) = top := by
          simpa [h, wa, haU, hbU, unionSepW, sep0_eq] using hcv0
        have hrA : r (g :: wa :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact slow2Pair0_or hnsa hnsb (bor_l (hka haU)) (bor_r (Nat.beq_eq.mpr (huB0 hbU))) (tryKeeps2_A (hka haU) htopA hav hrA)
      · have htopB : Nat.lor (Nat.lor (sep0 (bin true a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b))) (sep0 b) = top := by
          simpa [h, wb, haU, hbU, unionSepW, sep0_eq] using hcv0
        have hrB : r (g :: wb :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact slow2Pair0_or hnsa hnsb (bor_r (Nat.beq_eq.mpr (huA0 haU))) (bor_l (hkb hbU)) (tryKeeps2_B (hkb hbU) htopB hav hrB)
      · have htop : Nat.lor (sep0 (bin true a b)) (takeTwo (coverage false (sigsOf v)) (sep0 a) (sep0 b)) = top := by
          simpa [h, haU, hbU, unionSepW] using hcv0
        have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact slow2Pair0_or hnsa hnsb (bor_r (Nat.beq_eq.mpr (huA0 haU))) (bor_r (Nat.beq_eq.mpr (huB0 hbU))) (tryKeeps2_0 htop hav hr0)
  · intro ht0
    have hdt : decide (0 < t) = true := decide_eq_true (by omega)
    rw [hdt] at hcv' hmask hdisjAB hdisjBA hvc
    have hcv1 : Nat.lor (Nat.lor (sep1 (bin true a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b)))
        (unionSepW true h) = top := by simpa [hmask, sep1_eq] using hcv'
    have h0zero : ∀ x : Nat, Nat.land x 0 = 0 := fun x => Nat.and_zero x
    have huA1 : a ∉ U →
        Nat.land (Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 a)) a.1) b.2 = 0 ∧
        Nat.land (Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 a)) a.2) b.1 = 0 := fun hna => by
      by_cases hbU : b ∈ U
      · exact unique_or_1 hvc (by simpa [sep1_eq] using hdisjAB) (by simpa [h, wa, wb, hna, hbU, unionSepW, sep1_eq] using hcv1)
      · exact unique_or_1 hvc (h0zero _) (by simpa [h, hna, hbU, unionSepW] using hcv1)
    have huB1 : b ∉ U →
        Nat.land (Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 b)) b.1) a.2 = 0 ∧
        Nat.land (Nat.land (Nat.land (coverage true (sigsOf v)).2.1 (sep1 b)) b.2) a.1 = 0 := fun hnb => by
      have hcomm : Nat.lor (Nat.lor (sep1 (bin true b a)) (takeTwo (coverage true (sigsOf v)) (sep1 b) (sep1 a)))
          (unionSepW true h) = top := by
        rw [bin_comm]; simpa [takeTwo, Nat.or_comm, Nat.and_comm] using hcv1
      by_cases haU : a ∈ U
      · exact unique_or_1 hvc (by simpa [sep1_eq] using hdisjBA) (by simpa [h, wa, wb, haU, hnb, unionSepW, sep1_eq] using hcomm)
      · exact unique_or_1 hvc (h0zero _) (by simpa [h, haU, hnb, unionSepW] using hcomm)
    refine ⟨?_, ?_, ?_⟩
    · intro hlv
      have hh0 : h.length = 0 := by omega
      have hna : a ∉ U := fun hm => by simp [h, hm] at hh0
      have hnb : b ∉ U := fun hm => by simp [h, hm] at hh0
      have htop : Nat.lor (sep1 (bin true a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b)) = top := by
        simpa [h, hna, hnb, unionSepW] using hcv1
      have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, hna, hnb] using hr
      have ⟨u1, u2⟩ := huA1 hna; have ⟨v1, v2⟩ := huB1 hnb
      rw [coverageW_eq]
      exact fastPair1_or hnsa hnsb u1 v1 u2 v2 htop hav hr0
    · intro hlv
      have hh1 : h.length ≤ 1 := by omega
      rw [coverageW_eq]
      apply slow1Pair1_or hnsa hnsb
      by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U
      · simp [h, haU, hbU] at hh1
      · have htopA : Nat.lor (Nat.lor (sep1 (bin true a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b))) (sep1 a) = top := by
          simpa [h, wa, haU, hbU, unionSepW, sep1_eq] using hcv1
        have hrA : r (g :: wa :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨v1, v2⟩ := huB1 hbU
        exact tryKeeps1_A (hka haU) (band2 (Nat.beq_eq.mpr v1) (Nat.beq_eq.mpr v2)) htopA hav hrA
      · have htopB : Nat.lor (Nat.lor (sep1 (bin true a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b))) (sep1 b) = top := by
          simpa [h, wb, haU, hbU, unionSepW, sep1_eq] using hcv1
        have hrB : r (g :: wb :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨u1, u2⟩ := huA1 haU
        exact tryKeeps1_B (hkb hbU) (band2 (Nat.beq_eq.mpr u1) (Nat.beq_eq.mpr u2)) htopB hav hrB
      · have htop : Nat.lor (sep1 (bin true a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b)) = top := by
          simpa [h, haU, hbU, unionSepW] using hcv1
        have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨u1, u2⟩ := huA1 haU; have ⟨v1, v2⟩ := huB1 hbU
        exact tryKeeps1_0 (band2 (Nat.beq_eq.mpr u1) (Nat.beq_eq.mpr u2)) (band2 (Nat.beq_eq.mpr v1) (Nat.beq_eq.mpr v2)) htop hav hr0
    · rw [coverageW_eq]
      by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U
      · have htopAB : Nat.lor (Nat.lor (Nat.lor (sep1 (bin true a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b))) (sep1 a)) (sep1 b) = top := by
          have : unionSepW true h = sep1 a ||| sep1 b := by simp [h, wa, wb, haU, hbU, unionSepW, sep1_eq]
          rw [this] at hcv1; exact (Nat.or_assoc _ _ _).trans hcv1
        have hrAB : r (g :: wa :: wb :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        exact slow2Pair1_or hnsa hnsb (bor_l (hka haU)) (bor_l (hkb hbU)) (tryKeeps2_AB (hka haU) (hkb hbU) htopAB hav hrAB)
      · have htopA : Nat.lor (Nat.lor (sep1 (bin true a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b))) (sep1 a) = top := by
          simpa [h, wa, haU, hbU, unionSepW, sep1_eq] using hcv1
        have hrA : r (g :: wa :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨v1, v2⟩ := huB1 hbU
        exact slow2Pair1_or hnsa hnsb (bor_l (hka haU)) (bor_r (band2 (Nat.beq_eq.mpr v1) (Nat.beq_eq.mpr v2))) (tryKeeps2_A (hka haU) htopA hav hrA)
      · have htopB : Nat.lor (Nat.lor (sep1 (bin true a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b))) (sep1 b) = top := by
          simpa [h, wb, haU, hbU, unionSepW, sep1_eq] using hcv1
        have hrB : r (g :: wb :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨u1, u2⟩ := huA1 haU
        exact slow2Pair1_or hnsa hnsb (bor_r (band2 (Nat.beq_eq.mpr u1) (Nat.beq_eq.mpr u2))) (bor_l (hkb hbU)) (tryKeeps2_B (hkb hbU) htopB hav hrB)
      · have htop : Nat.lor (sep1 (bin true a b)) (takeTwo (coverage true (sigsOf v)) (sep1 a) (sep1 b)) = top := by
          simpa [h, haU, hbU, unionSepW] using hcv1
        have hr0 : r (g :: dropTwo a b v) = true := by rw [hdrop]; simpa [h, haU, hbU] using hr
        have ⟨u1, u2⟩ := huA1 haU; have ⟨v1, v2⟩ := huB1 hbU
        exact slow2Pair1_or hnsa hnsb (bor_r (band2 (Nat.beq_eq.mpr u1) (Nat.beq_eq.mpr u2))) (bor_r (band2 (Nat.beq_eq.mpr v1) (Nat.beq_eq.mpr v2))) (tryKeeps2_0 htop hav hr0)
lemma trestricted_congr {k t S τ₁ τ₂} (h : TRestricted k t S τ₁)
    (he : ∀ x ∈ S, τ₁ x = τ₂ x) : TRestricted k t S τ₂ := by
  induction h generalizing τ₂ with
  | stop => exact TRestricted.stop
  | @unary k t U a τ₁ ha hf hr1 hr2 tail ih =>
    have hae := he a (Finset.mem_insert_self _ _)
    refine TRestricted.unary ha hf (hae ▸ hr1) (hae ▸ hr2) (ih ?_)
    intro x hx; unfold updUnaryTag
    rcases Finset.mem_insert.mp hx with rfl | hxU
    · simp [hae]
    · have hne : x ≠ neg a := fun e => hf (e ▸ Finset.mem_insert_of_mem hxU)
      simp [hne, he x (Finset.mem_insert_of_mem hxU)]
  | @binaryAnd k t U a b τ₁ ha hb hab hf hra hrb tail ih =>
    have hae := he a (Finset.mem_insert_self _ _)
    have hbe := he b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    refine TRestricted.binaryAnd ha hb hab hf (hae ▸ hra) (hbe ▸ hrb) (ih ?_)
    intro x hx; unfold updAndTag
    rcases Finset.mem_insert.mp hx with rfl | hxU
    · simp [hae, hbe]
    · have hne : x ≠ bin false a b := fun e => hf (e ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU))
      simp [hne, he x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU))]
  | @binaryOr k t U a b τ₁ ha hb hab hf hra hrb tail ih =>
    have hae := he a (Finset.mem_insert_self _ _)
    have hbe := he b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    refine TRestricted.binaryOr ha hb hab hf (hae ▸ hra) (hbe ▸ hrb) (ih ?_)
    intro x hx; unfold updOrTag
    rcases Finset.mem_insert.mp hx with rfl | hxU
    · simp
    · have hne : x ≠ bin true a b := fun e => hf (e ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU))
      simp [hne, hae, hbe, he x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU))]
lemma binary_dispatch {k t : Nat} {a b : Wire} {v : List Wire} {r : List Wire → Bool}
    (ha : a ∈ v) (hb : b ∈ v) (hne : a ≠ b)
    (h1 : let lim := k - t + 1; let c0 := coverageW false v; let c1 := coverageW true v
      (t = 0 →
        (v.length = lim + 1 → fastPair0 r v c0 (mkAct0 c0.2.1 a) (mkAct0 c0.2.1 b) = true) ∧
        (v.length = lim → slow1Pair0 r v c0 (mkAct0 c0.2.1 a) (mkAct0 c0.2.1 b) = true) ∧
        slow2Pair0 r v c0 (mkAct0 c0.2.1 a) (mkAct0 c0.2.1 b) = true) ∧
      (t ≠ 0 →
        (v.length = lim + 1 → fastPair1 r v c1 (mkAct1 c1.2.1 a) (mkAct1 c1.2.1 b) = true) ∧
        (v.length = lim → slow1Pair1 r v c1 (mkAct1 c1.2.1 a) (mkAct1 c1.2.1 b) = true) ∧
        slow2Pair1 r v c1 (mkAct1 c1.2.1 a) (mkAct1 c1.2.1 b) = true))
    (h2 : let lim := k - t + 1; let c0 := coverageW false v; let c1 := coverageW true v
      (t = 0 →
        (v.length = lim + 1 → fastPair0 r v c0 (mkAct0 c0.2.1 b) (mkAct0 c0.2.1 a) = true) ∧
        (v.length = lim → slow1Pair0 r v c0 (mkAct0 c0.2.1 b) (mkAct0 c0.2.1 a) = true) ∧
        slow2Pair0 r v c0 (mkAct0 c0.2.1 b) (mkAct0 c0.2.1 a) = true) ∧
      (t ≠ 0 →
        (v.length = lim + 1 → fastPair1 r v c1 (mkAct1 c1.2.1 b) (mkAct1 c1.2.1 a) = true) ∧
        (v.length = lim → slow1Pair1 r v c1 (mkAct1 c1.2.1 b) (mkAct1 c1.2.1 a) = true) ∧
        slow2Pair1 r v c1 (mkAct1 c1.2.1 b) (mkAct1 c1.2.1 a) = true)) :
    binaryMoves k t v.length r v = true := by
  unfold binaryMoves; dsimp only
  by_cases ht0 : t = 0
  · subst ht0
    simp only [Nat.beq_refl, ite_true, buildSeps0_eq, buildActs0_map]
    have hne0 : mkAct0 (coverageW false v).2.1 a ≠ mkAct0 (coverageW false v).2.1 b :=
      fun e => hne (congrArg WAct0.w e)
    have ⟨hf1, hs11, hs21⟩ := h1.1 rfl
    have ⟨hf2, hs12, hs22⟩ := h2.1 rfl
    by_cases hl1 : v.length = k - 0 + 1 + 1
    · simp only [hl1, Nat.beq_refl, ite_true, scanFast0_eq]
      exact scanPairs_complete _ (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) hne0 (hf1 hl1) (hf2 hl1)
    · have hb1 : Nat.beq v.length (k - 0 + 1 + 1) = false := nat_beq_false hl1
      simp only [hb1, Bool.false_eq_true, ite_false]
      by_cases hl2 : v.length = k - 0 + 1
      · simp only [hl2, Nat.beq_refl, ite_true, scanSlow10_eq]
        exact scanPairs_complete _ (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) hne0 (hs11 hl2) (hs12 hl2)
      · have hb2 : Nat.beq v.length (k - 0 + 1) = false := nat_beq_false hl2
        simp only [hb2, Bool.false_eq_true, ite_false, scanSlow20_eq]
        exact scanPairs_complete _ (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) hne0 hs21 hs22
  · have hbf : Nat.beq t 0 = false := nat_beq_false ht0
    simp only [hbf, Bool.false_eq_true, ite_false, buildSeps1_eq, buildActs1_map]
    have hne1 : mkAct1 (coverageW true v).2.1 a ≠ mkAct1 (coverageW true v).2.1 b :=
      fun e => hne (congrArg WAct1.w e)
    have ⟨hf1, hs11, hs21⟩ := h1.2 ht0
    have ⟨hf2, hs12, hs22⟩ := h2.2 ht0
    by_cases hl1 : v.length = k - t + 1 + 1
    · simp only [hl1, Nat.beq_refl, ite_true, scanFast1_eq]
      exact scanPairs_complete _ (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) hne1 (hf1 hl1) (hf2 hl1)
    · have hb1 : Nat.beq v.length (k - t + 1 + 1) = false := nat_beq_false hl1
      simp only [hb1, Bool.false_eq_true, ite_false]
      by_cases hl2 : v.length = k - t + 1
      · simp only [hl2, Nat.beq_refl, ite_true, scanSlow11_eq]
        exact scanPairs_complete _ (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) hne1 (hs11 hl2) (hs12 hl2)
      · have hb2 : Nat.beq v.length (k - t + 1) = false := nat_beq_false hl2
        simp only [hb2, Bool.false_eq_true, ite_false, scanSlow21_eq]
        exact scanPairs_complete _ (List.mem_map_of_mem ha) (List.mem_map_of_mem hb) hne1 hs21 hs22
lemma binary_found_and {m t k : Nat} {U : Finset Sig} {a b : Sig} {τ : Sig → Tag} {v : List Wire}
    {r : List Wire → Bool}
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hrep : Represents v (insert a (insert b U)) τ) (hle : m ≤ k)
    (fresh : bin false a b ∉ insert a (insert b U))
    (hra : τ a ≠ .tSpec0 ∧ (τ a ≠ .tNone → a ∉ U))
    (hrb : τ b ≠ .tSpec0 ∧ (τ b ≠ .tNone → b ∉ U))
    (l : TRestricted m t (insert (bin false a b) U) (updAndTag τ a b))
    (ih : ∀ w : List Wire, Represents w (insert (bin false a b) U) (updAndTag τ a b) → r w = true) :
    binaryMoves k t v.length r v = true := by
  have ahS : a ∈ sigsOf v := List.mem_toFinset.mp (hrep.2.1.symm ▸ Finset.mem_insert_self _ _)
  have bhS : b ∈ sigsOf v := List.mem_toFinset.mp (hrep.2.1.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have ah : (a, τ a) ∈ v := (mem_sigsOf_iff hrep.2.2).mpr ahS
  have bh : (b, τ b) ∈ v := (mem_sigsOf_iff hrep.2.2).mpr bhS
  have h1 := pair_and_found ha hb hab hrep hle fresh hra hrb l ih
  have hrep' : Represents v (insert b (insert a U)) τ :=
    ⟨hrep.1, by rw [Finset.insert_comm b a]; exact hrep.2.1, hrep.2.2⟩
  have hf' : bin false b a ∉ insert b (insert a U) := by rwa [bin_comm false b a, Finset.insert_comm b a]
  have htagEq : ∀ x, updAndTag τ b a x = updAndTag τ a b x := by
    intro x; unfold updAndTag; rw [bin_comm false b a]; simp only [or_comm]
  have l' : TRestricted m t (insert (bin false b a) U) (updAndTag τ b a) := by
    rw [bin_comm false b a]; exact trestricted_congr l (fun x _ => (htagEq x).symm)
  have ih' : ∀ w : List Wire, Represents w (insert (bin false b a) U) (updAndTag τ b a) → r w = true := by
    intro w hw; apply ih w; rw [bin_comm false b a] at hw
    exact ⟨hw.1, hw.2.1, fun x hx => (hw.2.2 x hx).trans (htagEq x.1)⟩
  have h2 := pair_and_found hb ha hab.symm hrep' hle hf' hrb hra l' ih'
  exact binary_dispatch ah bh (fun e => hab (congrArg Prod.fst e)) h1 h2
lemma binary_found_or {m t k : Nat} {U : Finset Sig} {a b : Sig} {τ : Sig → Tag} {v : List Wire}
    {r : List Wire → Bool}
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hrep : Represents v (insert a (insert b U)) τ) (hle : m ≤ k)
    (fresh : bin true a b ∉ insert a (insert b U))
    (hra : τ a ≠ .tSpec1 ∧ (τ a = .tSpec0 → a ∉ U))
    (hrb : τ b ≠ .tSpec1 ∧ (τ b = .tSpec0 → b ∉ U))
    (l : TRestricted m t (insert (bin true a b) U) (updOrTag τ a b))
    (ih : ∀ w : List Wire, Represents w (insert (bin true a b) U) (updOrTag τ a b) → r w = true) :
    binaryMoves k t v.length r v = true := by
  have ahS : a ∈ sigsOf v := List.mem_toFinset.mp (hrep.2.1.symm ▸ Finset.mem_insert_self _ _)
  have bhS : b ∈ sigsOf v := List.mem_toFinset.mp (hrep.2.1.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have ah : (a, τ a) ∈ v := (mem_sigsOf_iff hrep.2.2).mpr ahS
  have bh : (b, τ b) ∈ v := (mem_sigsOf_iff hrep.2.2).mpr bhS
  have h1 := pair_or_found ha hb hab hrep hle fresh hra hrb l ih
  have hrep' : Represents v (insert b (insert a U)) τ :=
    ⟨hrep.1, by rw [Finset.insert_comm b a]; exact hrep.2.1, hrep.2.2⟩
  have hf' : bin true b a ∉ insert b (insert a U) := by rwa [bin_comm true b a, Finset.insert_comm b a]
  have htagEq : ∀ x, updOrTag τ b a x = updOrTag τ a b x := by
    intro x; unfold updOrTag; rw [bin_comm true b a]
    by_cases hg : x = bin true a b
    · simp [hg]
    · by_cases hxa : x = a <;> by_cases hxb : x = b <;> simp_all
  have l' : TRestricted m t (insert (bin true b a) U) (updOrTag τ b a) := by
    rw [bin_comm true b a]; exact trestricted_congr l (fun x _ => (htagEq x).symm)
  have ih' : ∀ w : List Wire, Represents w (insert (bin true b a) U) (updOrTag τ b a) → r w = true := by
    intro w hw; apply ih w; rw [bin_comm true b a] at hw
    exact ⟨hw.1, hw.2.1, fun x hx => (hw.2.2 x hx).trans (htagEq x.1)⟩
  have h2 := pair_or_found hb ha hab.symm hrep' hle hf' hrb hra l' ih'
  exact binary_dispatch ah bh (fun e => hab (congrArg Prod.fst e)) h1 h2
lemma reduced_step {m t S : Nat} {s : Finset Sig} {τ : Sig → Tag} {v : List Wire}
    {u b : List Wire → Bool}
    (h : TRestricted m t s τ) (hb : m ≤ S + 1) (hrep : Represents v s τ)
    (hu : ∀ w, ∀ s' τ', Represents w s' τ' → ∀ l ≤ S, TRestricted l (t - 1) s' τ' → u w = true)
    (hb' : ∀ w, ∀ s' τ', Represents w s' τ' → ∀ l ≤ S, TRestricted l t s' τ' → b w = true) :
    stepTest S t v u b = true := by
  have size := live_size h.live
  rw [← hrep.2.1, List.toFinset_card_of_nodup hrep.1, sigsOf_length] at size
  have h1 : Nat.blt (S + 1) t = false := Bool.eq_false_iff.mpr fun e => by rw [Nat.blt_eq] at e; omega
  have h2 : Nat.blt (S + 1 - t + 1) v.length = false := Bool.eq_false_iff.mpr fun e => by rw [Nat.blt_eq] at e; omega
  simp only [stepTest, h1, h2, Bool.or_self, Bool.false_eq_true, ite_false]
  cases h with
  | stop =>
    have p : (sigsOf v).Perm [target] :=
      List.perm_of_nodup_nodup_toFinset_eq hrep.1 (by simp) (by simp [hrep.2.1])
    have eq := List.perm_singleton.mp p
    cases v with
    | nil => simp [sigsOf] at eq
    | cons w rest =>
      simp only [sigsOf, List.map_cons, List.cons.injEq, List.map_eq_nil_iff] at eq
      obtain ⟨hw, rfl⟩ := eq
      simp [hw, sigEq_iff]
  | @unary m t U a τ ha hf hr1 hr2 tail =>
    apply Bool.or_eq_true_iff.mpr; left
    apply Bool.or_eq_true_iff.mpr; right
    apply Bool.and_eq_true_iff.mpr
    exact ⟨by simp [Nat.blt_eq], unary_found ha hrep (by omega) hf hr1 hr2 tail (fun w hw => hu w _ _ hw m (by omega) tail)⟩
  | @binaryAnd m t U a b τ ha hb'p hab hf hra hrb tail =>
    apply Bool.or_eq_true_iff.mpr; right
    exact binary_found_and ha hb'p hab hrep (by omega) hf hra hrb tail (fun w hw => hb' w _ _ hw m (by omega) tail)
  | @binaryOr m t U a b τ ha hb'p hab hf hra hrb tail =>
    apply Bool.or_eq_true_iff.mpr; right
    exact binary_found_or ha hb'p hab hrep (by omega) hf hra hrb tail (fun w hw => hb' w _ _ hw m (by omega) tail)
lemma search_complete {m t : Nat} {S : Finset Sig} {τ : Sig → Tag} (h : TRestricted m t S τ)
    (k : Nat) (hk : m ≤ k) (v : List Wire) (hrep : Represents v S τ) : search k t v = true := by
  induction k generalizing m t S τ v with
  | zero =>
    have hm : m = 0 := by omega
    subst m
    cases h
    have p : (sigsOf v).Perm [target] :=
      List.perm_of_nodup_nodup_toFinset_eq hrep.1 (by simp) (by simp [hrep.2.1])
    have eq := List.perm_singleton.mp p
    cases v with
    | nil => simp [sigsOf] at eq
    | cons w rest =>
      simp only [sigsOf, List.map_cons, List.cons.injEq, List.map_eq_nil_iff] at eq
      obtain ⟨hw, rfl⟩ := eq
      simp [search, hw, sigEq_iff]
  | succ k ih =>
    rw [search]
    apply reduced_step h hk hrep <;>
      exact fun w s' τ' hw l hl hh => ih hh hl w hw
def Impossible (k t : Nat) (v : List Wire) : Prop :=
  ∀ m ≤ k, ∀ S τ, Represents v S τ → ¬ TRestricted m t S τ
lemma exclude_search {k t : Nat} {v : List Wire} (hc : search k t v = false) :
    Impossible k t v := by
  intro m hm S τ hrep h
  exact Bool.false_ne_true (hc.symm.trans (search_complete h k hm v hrep))
lemma exclude_step {k t : Nat} {v : List Wire} {u b : List Wire → Bool}
    (hu : ∀ w, u w = false → Impossible k (t - 1) w)
    (hb : ∀ w, b w = false → Impossible k t w)
    (hc : stepTest k t v u b = false) : Impossible (k + 1) t v := by
  intro m hm S τ hrep h
  have hu' : ∀ w s' τ', Represents w s' τ' → ∀ j ≤ k, TRestricted j (t - 1) s' τ' → u w = true := by
    intro w s' τ' hw j hj r
    cases e : u w
    · exact (hu _ e j hj s' τ' hw r).elim
    · rfl
  have hb' : ∀ w s' τ', Represents w s' τ' → ∀ j ≤ k, TRestricted j t s' τ' → b w = true := by
    intro w s' τ' hw j hj r
    cases e : b w
    · exact (hb _ e j hj s' τ' hw r).elim
    · rfl
  exact Bool.false_ne_true (hc.symm.trans (reduced_step h hm hrep hu' hb'))

lemma perm_impossible {k t : Nat} {w z : List Wire} (hp : w.Perm z)
    (hz : Impossible k t z) : Impossible k t w := by
  intro m hm S τ hrep h
  apply hz m hm S τ _ h
  have hpS : (sigsOf w).Perm (sigsOf z) := hp.map Prod.fst
  refine ⟨hpS.nodup_iff.mp hrep.1, ?_, fun x hx => hrep.2.2 x (hp.mem_iff.mpr hx)⟩
  rw [← hrep.2.1]; ext a
  simp only [List.mem_toFinset, hpS.mem_iff]

def wireHash (salt : Nat) (w : Wire) : Nat :=
  let h := ((w.1.1 % 1048573) * (65537 + salt) + (w.1.2 % 1048573) * 131 + w.2.toNat * 997 + 317) % 1048573
  (h * h % 1048573) * h % 1048573
def frontierHash (salt : Nat) (v : List Wire) : Nat :=
  (v.foldl (fun s w => s + wireHash salt w) 0) % 1048573

def eraseWire (a : Wire) : List Wire → Option (List Wire)
  | [] => none
  | b :: l =>
    if tagEq a.2 b.2 && sigEq a.1 b.1 then some l
    else match eraseWire a l with
      | none => none
      | some l' => some (b :: l')
lemma eraseWire_perm {a : Wire} {ys ys' : List Wire} (h : eraseWire a ys = some ys') :
    ys.Perm (a :: ys') := by
  induction ys generalizing ys' with
  | nil => simp [eraseWire] at h
  | cons b l ih =>
    unfold eraseWire at h
    split at h
    · rename_i heq
      simp only [Bool.and_eq_true, tagEq_iff, sigEq_iff] at heq
      have hab : a = b := Prod.ext heq.2 heq.1
      injection h with h'; subst h'; subst hab; exact List.Perm.refl _
    · cases he : eraseWire a l with
      | none => simp [he] at h
      | some l' =>
        simp only [he] at h; injection h with h'; subst h'
        exact (List.Perm.cons b (ih he)).trans (List.Perm.swap a b l')
def isPermFast : List Wire → List Wire → Bool
  | [], [] => true
  | a :: l, ys =>
    match eraseWire a ys with
    | none => false
    | some ys' => isPermFast l ys'
  | _, _ => false
lemma isPermFast_perm {xs ys : List Wire} (h : isPermFast xs ys = true) : xs.Perm ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [isPermFast] at h ⊢
  | cons a l ih =>
    unfold isPermFast at h
    cases he : eraseWire a ys with
    | none => simp [he] at h
    | some ys' =>
      simp only [he] at h
      exact (List.Perm.cons a (ih h)).trans (eraseWire_perm he).symm

def span (p : Nat → Bool) : Nat → Nat → Bool
  | 0, _ => true
  | n + 1, i => p i && span p n (i + 1)
lemma span_join {p : Nat → Bool} {a i b : Nat}
    (ha : span p a i = true) (hb : span p b (i + a) = true) : span p (a + b) i = true := by
  induction a generalizing i with
  | zero => simpa [span] using hb
  | succ a ih =>
    simp only [span, Bool.and_eq_true] at ha
    rw [Nat.succ_add]
    simp only [span, Bool.and_eq_true]
    exact ⟨ha.1, ih ha.2 (by rw [show i + 1 + a = i + (a + 1) by omega]; exact hb)⟩
lemma span_ok {p : Nat → Bool} {n i : Nat} (h : span p n i = true) :
    ∀ j, i ≤ j → j < i + n → p j = true := by
  induction n generalizing i with
  | zero => intro j h1 h2; omega
  | succ n ih =>
    simp only [span, Bool.and_eq_true] at h
    intro j h1 h2
    by_cases he : j = i
    · exact he ▸ h.1
    · exact ih h.2 j (by omega) (by omega)


def Reversible (H J : SigHom) (x : Sig) : Prop := Valid x ∧ J.fn (H.fn x) = x
lemma revInj {H J : SigHom} {x y : Sig} (hx : Reversible H J x) (hy : Reversible H J y)
    (e : H.fn x = H.fn y) : x = y := hx.2.symm.trans ((congrArg J.fn e).trans hy.2)
lemma revProper {H J : SigHom} {a : Sig} (ha : proper a) (ga : Reversible H J a) :
    proper (H.fn a) := by
  refine ⟨H.valid _,?_,?_⟩
  · intro e
    exact ha.2.1 (ga.2.symm.trans ((congrArg J.fn e).trans J.hzero))
  · intro e
    exact ha.2.2 (ga.2.symm.trans ((congrArg J.fn e).trans J.hone))
lemma revNeg {H J : SigHom} {a : Sig} (ha : Reversible H J a) : Reversible H J (neg a) := by
  refine ⟨valid_neg ha.1,?_⟩
  rw [H.hneg ha.1,J.hneg (H.valid _),ha.2]
lemma revBin (d : Bool) {H J : SigHom} {a b : Sig} (ha : Reversible H J a)
    (hb : Reversible H J b) : Reversible H J (bin d a b) := by
  refine ⟨valid_bin ha.1 hb.1,?_⟩
  rw [H.hbin,J.hbin,ha.2,hb.2]
lemma transportTrace {k t S τ} (h : TRestricted k t S τ) (H J : SigHom)
    (reversible : ∀ x ∈ S, Reversible H J x) :
    TRestricted k t (S.image H.fn) (fun x => τ (J.fn x)) := by
  induction h with
  | stop => simpa [H.htarget] using TRestricted.stop
  | @unary k t U a τ ha hf hr1 hr2 tail ih =>
    have ga := reversible a (Finset.mem_insert_self _ _)
    have gu (y : Sig) (hy : y ∈ U) : Reversible H J y := reversible y (Finset.mem_insert_of_mem hy)
    specialize ih (fun x hx => by
      obtain rfl | hu := Finset.mem_insert.mp hx
      · exact revNeg ga
      · exact gu x hu)
    simp only [Finset.image_insert, H.hneg ha.1] at ih ⊢
    have hinvA : J.fn (H.fn a) = a := ga.2
    have hvalU := gu
    have hne : neg (H.fn a) ∉ insert (H.fn a) (U.image H.fn) := by
      rw [← H.hneg ha.1, ← Finset.image_insert]
      intro hx; obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
      have hvy : Reversible H J y := by
        rcases Finset.mem_insert.mp hy with rfl | hyU
        · exact ga
        · exact hvalU y hyU
      exact hf ((revInj hvy (revNeg ga) he) ▸ hy)
    have hnaU : a ∉ U → H.fn a ∉ U.image H.fn := by
      intro hna hx; obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
      exact hna ((revInj (hvalU y hy) ga he) ▸ hy)
    refine TRestricted.unary (revProper ha ga) hne (by simpa [hinvA] using hr1)
      (fun h => hnaU (hr2 (by simpa [hinvA] using h))) ?_
    refine trestricted_congr ih ?_
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxU
    · unfold updUnaryTag
      simp only [ite_true]
      rw [← H.hneg ha.1, (revNeg ga).2]
      simp only [ite_true, hinvA]
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hxU
      have hneY : y ≠ neg a := fun e => hf (e ▸ Finset.mem_insert_of_mem hy)
      have hneGY : H.fn y ≠ neg (H.fn a) := by
        rw [← H.hneg ha.1]; intro e; exact hneY (revInj (hvalU y hy) (revNeg ga) e)
      unfold updUnaryTag
      simp only [hneGY, ite_false, (hvalU y hy).2, hneY]
  | @binaryAnd k t U a b τ ha hb hab hf hra hrb tail ih =>
    have ga := reversible a (Finset.mem_insert_self _ _)
    have gb := reversible b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have gu (y : Sig) (hy : y ∈ U) : Reversible H J y :=
      reversible y (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy))
    specialize ih (fun x hx => by
      obtain rfl | hu := Finset.mem_insert.mp hx
      · exact revBin false ga gb
      · exact gu x hu)
    simp only [Finset.image_insert, H.hbin false a b] at ih ⊢
    have hinvA := ga.2
    have hinvB := gb.2
    have hvalU := gu
    have hne : bin false (H.fn a) (H.fn b) ∉
        insert (H.fn a) (insert (H.fn b) (U.image H.fn)) := by
      rw [← H.hbin false a b, ← Finset.image_insert, ← Finset.image_insert]
      intro hx; obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
      have hvy : Reversible H J y := by
        rcases Finset.mem_insert.mp hy with rfl | hy1
        · exact ga
        rcases Finset.mem_insert.mp hy1 with rfl | hyU
        · exact gb
        · exact hvalU y hyU
      exact hf ((revInj hvy (revBin false ga gb) he) ▸ hy)
    have hnotU (z : Sig) (hvz : Reversible H J z) (hnz : z ∉ U) : H.fn z ∉ U.image H.fn := by
      intro hx; obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
      exact hnz ((revInj (hvalU y hy) hvz he) ▸ hy)
    refine TRestricted.binaryAnd (revProper ha ga) (revProper hb gb)
      (fun e => hab (revInj ga gb e)) hne
      ⟨by simpa [hinvA] using hra.1, fun h => hnotU a ga (hra.2 (by simpa [hinvA] using h))⟩
      ⟨by simpa [hinvB] using hrb.1, fun h => hnotU b gb (hrb.2 (by simpa [hinvB] using h))⟩ ?_
    refine trestricted_congr ih ?_
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxU
    · unfold updAndTag
      simp only [ite_true]
      rw [← H.hbin false a b, (revBin false ga gb).2]
      simp only [ite_true, hinvA, hinvB]
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hxU
      have hneY : y ≠ bin false a b := fun e => hf (e ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy))
      have hneGY : H.fn y ≠ bin false (H.fn a) (H.fn b) := by
        rw [← H.hbin false a b]; intro e; exact hneY (revInj (hvalU y hy) (revBin false ga gb) e)
      unfold updAndTag
      simp only [hneGY, ite_false, (hvalU y hy).2, hneY]
  | @binaryOr k t U a b τ ha hb hab hf hra hrb tail ih =>
    have ga := reversible a (Finset.mem_insert_self _ _)
    have gb := reversible b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have gu (y : Sig) (hy : y ∈ U) : Reversible H J y :=
      reversible y (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy))
    specialize ih (fun x hx => by
      obtain rfl | hu := Finset.mem_insert.mp hx
      · exact revBin true ga gb
      · exact gu x hu)
    simp only [Finset.image_insert, H.hbin true a b] at ih ⊢
    have hinvA := ga.2
    have hinvB := gb.2
    have hvalU := gu
    have hne : bin true (H.fn a) (H.fn b) ∉
        insert (H.fn a) (insert (H.fn b) (U.image H.fn)) := by
      rw [← H.hbin true a b, ← Finset.image_insert, ← Finset.image_insert]
      intro hx; obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
      have hvy : Reversible H J y := by
        rcases Finset.mem_insert.mp hy with rfl | hy1
        · exact ga
        rcases Finset.mem_insert.mp hy1 with rfl | hyU
        · exact gb
        · exact hvalU y hyU
      exact hf ((revInj hvy (revBin true ga gb) he) ▸ hy)
    have hnotU (z : Sig) (hvz : Reversible H J z) (hnz : z ∉ U) : H.fn z ∉ U.image H.fn := by
      intro hx; obtain ⟨y, hy, he⟩ := Finset.mem_image.mp hx
      exact hnz ((revInj (hvalU y hy) hvz he) ▸ hy)
    refine TRestricted.binaryOr (revProper ha ga) (revProper hb gb)
      (fun e => hab (revInj ga gb e)) hne
      ⟨by simpa [hinvA] using hra.1, fun h => hnotU a ga (hra.2 (by simpa [hinvA] using h))⟩
      ⟨by simpa [hinvB] using hrb.1, fun h => hnotU b gb (hrb.2 (by simpa [hinvB] using h))⟩ ?_
    refine trestricted_congr ih ?_
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxU
    · unfold updOrTag
      simp only [ite_true]
      rw [← H.hbin true a b, (revBin true ga gb).2]
      simp only [ite_true]
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hxU
      have hvy := hvalU y hy
      have hneY : y ≠ bin true a b := fun e => hf (e ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hy))
      have hneGY : H.fn y ≠ bin true (H.fn a) (H.fn b) := by
        rw [← H.hbin true a b]; intro e; exact hneY (revInj hvy (revBin true ga gb) e)
      have eqA : (H.fn y = H.fn a) ↔ (y = a) := ⟨revInj hvy ga, congrArg H.fn⟩
      have eqB : (H.fn y = H.fn b) ↔ (y = b) := ⟨revInj hvy gb, congrArg H.fn⟩
      unfold updOrTag
      simp only [hneGY, ite_false, hvy.2, hneY, eqA, eqB, hinvA, hinvB]

lemma equivalentImpossible {k t : Nat} {w z : List Wire} (H J : SigHom)
    (good : ∀ a ∈ sigsOf w, Reversible H J a)
    (hp : (w.map (fun x => (H.fn x.1,x.2))).Perm z) (hn : Impossible k t z) : Impossible k t w := by
  intro m hm S τ rep run
  apply hn m hm (S.image H.fn) (fun x => τ (J.fn x)) _ (transportTrace run H J (fun a ha =>
    good a (List.mem_toFinset.mp (rep.2.1 ▸ ha))))
  have e : sigsOf (w.map (fun x => (H.fn x.1,x.2))) = (sigsOf w).map H.fn := by
    simp [sigsOf,List.map_map,Function.comp_def]
  have p : ((sigsOf w).map H.fn).Perm (sigsOf z) := by rw [← e]; exact hp.map Prod.fst
  have nd : ((sigsOf w).map H.fn).Nodup := by
    apply List.Nodup.map_on _ rep.1
    intro a ha b hb hab
    exact revInj (good a ha) (good b hb) hab
  refine ⟨p.nodup_iff.mp nd,?_,?_⟩
  · ext a
    simp only [← rep.2.1,List.mem_toFinset,← p.mem_iff]
    simp
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp (hp.mem_iff.mpr hx)
    simpa only [(good y.1 (List.mem_map_of_mem hy)).2] using rep.2.2 y hy

lemma movedImpossible {k t : Nat} (w : List Wire) (H J : SigHom)
    (good : ∀ a ∈ sigsOf w, Reversible H J a) (hn : Impossible k t w) :
    Impossible k t (w.map (fun x => (H.fn x.1,x.2))) := by
  apply equivalentImpossible J H _ _ hn
  · intro a ha
    change a ∈ List.map Prod.fst _ at ha
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    obtain ⟨y,hy,rfl⟩ := List.mem_map.mp hx
    have fixed := (good y.1 (List.mem_map_of_mem hy)).2
    exact ⟨H.valid _,congrArg H.fn fixed⟩
  · apply List.Perm.of_eq
    rw [List.map_map]
    calc
      _ = w.map id := by
        apply List.map_congr_left
        intro x hx
        exact Prod.ext (good x.1 (List.mem_map_of_mem hx)).2 rfl
      _ = w := by simp

namespace VariableProjection
def Tight (H : SigHom) (k : Nat) (S : Finset Sig) : Prop :=
  ∀ q, q + 1 < k → ¬ Feasible H q S
def Slack (H : SigHom) (k : Nat) (S : Finset Sig) : Prop :=
  ∀ q, q + 2 < k → ¬ Feasible H q S
def WireTagOk (k : Nat) (S : Finset Sig) (a : Sig) : Tag → Prop
  | .tNone => True
  | .tDeg3 => ∃ H : SigHom, H.fn a = zero ∧ Slack H k S
  | .tSpec0 => ∃ H : SigHom, H.fn a = zero ∧ Tight H k S
  | .tSpec1 => ∃ H : SigHom, H.fn a = one ∧ Tight H k S
def TagOk (k : Nat) (S : Finset Sig) (τ : Sig → Tag) : Prop :=
  ∀ a ∈ S, WireTagOk k S a (τ a)
lemma wireTagOk_unary_step {k : Nat} {U : Finset Sig} {a x : Sig} {tg : Tag} (hva : Valid a)
    (h : WireTagOk (k + 1) (insert a U) x tg) : WireTagOk k (insert (neg a) U) x tg := by
  cases tg with
  | tNone => trivial
  | tDeg3 =>
    obtain ⟨i, hp, hs⟩ := h
    exact ⟨i, hp, fun q hq hf => hs (q + 1) (by omega) (pull_unary hva hf)⟩
  | tSpec0 =>
    obtain ⟨i, hp, ht⟩ := h
    exact ⟨i, hp, fun q hq hf => ht (q + 1) (by omega) (pull_unary hva hf)⟩
  | tSpec1 =>
    obtain ⟨i, hp, ht⟩ := h
    exact ⟨i, hp, fun q hq hf => ht (q + 1) (by omega) (pull_unary hva hf)⟩
lemma wireTagOk_binary_step {k : Nat} {U : Finset Sig} {a b x : Sig} {d : Bool} {tg : Tag}
    (h : WireTagOk (k + 1) (insert a (insert b U)) x tg) :
    WireTagOk k (insert (bin d a b) U) x tg := by
  cases tg with
  | tNone => trivial
  | tDeg3 =>
    obtain ⟨i, hp, hs⟩ := h
    exact ⟨i, hp, fun q hq hf => hs (q + 1) (by omega) (pull_binary hf)⟩
  | tSpec0 =>
    obtain ⟨i, hp, ht⟩ := h
    exact ⟨i, hp, fun q hq hf => ht (q + 1) (by omega) (pull_binary hf)⟩
  | tSpec1 =>
    obtain ⟨i, hp, ht⟩ := h
    exact ⟨i, hp, fun q hq hf => ht (q + 1) (by omega) (pull_binary hf)⟩
lemma restrict_live {k t S τ} (h : Live k t S) (ht : TagOk k S τ) : TRestricted k t S τ := by
  induction h generalizing τ with
  | stop => exact TRestricted.stop
  | @unary k t U a ha hf tail ih =>
    have hta := ht a (Finset.mem_insert_self _ _)
    have hr1 : τ a ≠ .tSpec0 ∧ τ a ≠ .tSpec1 := by
      constructor <;> intro heq <;> rw [heq] at hta
      · obtain ⟨i, hp0, hti⟩ := hta
        have hz : ¬ proper (i.fn a) := fun hp => hp.2.1 hp0
        have ho : ¬ proper (i.fn (neg a)) := fun hp =>
          hp.2.2 (by rw [i.hneg ha.1, hp0, neg_laws.1])
        obtain ⟨q, hq, hfe⟩ := feasible_const tail i (neg a) (Finset.mem_insert_self _ _) ho
        exact hti q (by omega) (free_unary ha.1 hz hfe)
      · obtain ⟨i, hp1, hti⟩ := hta
        have ho : ¬ proper (i.fn a) := fun hp => hp.2.2 hp1
        have hz : ¬ proper (i.fn (neg a)) := fun hp =>
          hp.2.1 (by rw [i.hneg ha.1, hp1, neg_laws.2])
        obtain ⟨q, hq, hfe⟩ := feasible_const tail i (neg a) (Finset.mem_insert_self _ _) hz
        exact hti q (by omega) (free_unary ha.1 ho hfe)
    have hr2 : τ a = .tDeg3 → a ∉ U := by
      intro heq haU
      rw [heq] at hta
      obtain ⟨i, hp0, hsl⟩ := hta
      have hz : ¬ proper (i.fn a) := fun hp => hp.2.1 hp0
      have ho : ¬ proper (i.fn (neg a)) := fun hp =>
        hp.2.2 (by rw [i.hneg ha.1, hp0, neg_laws.1])
      have hne : neg a ≠ a := fun e => by rw [e] at hf; exact hf (Finset.mem_insert_self _ _)
      obtain ⟨q, hq, hfe⟩ := feasible_two_consts tail i (neg a) a
        (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem haU) hne ho hz
      exact hsl q (by omega) (free_unary ha.1 hz hfe)
    have ht' : TagOk k (insert (neg a) U) (updUnaryTag τ a) := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hxU
      · unfold updUnaryTag; simp only [ite_true]
        split
        · rename_i hd3
          rw [hd3] at hta
          obtain ⟨i, hp0, hsl⟩ := hta
          have hz : ¬ proper (i.fn a) := fun hp => hp.2.1 hp0
          refine ⟨i, by rw [i.hneg ha.1, hp0]; exact neg_laws.1, ?_⟩
          intro q hq hfe; exact hsl q (by omega) (free_unary ha.1 hz hfe)
        · trivial
      · have hne : x ≠ neg a := fun e => hf (e ▸ Finset.mem_insert_of_mem hxU)
        unfold updUnaryTag; simp only [hne, ite_false]
        exact wireTagOk_unary_step ha.1 (ht x (Finset.mem_insert_of_mem hxU))
    exact TRestricted.unary ha hf hr1 hr2 (ih ht')
  | @binary k t U a b d ha hb hab hf tail ih =>
    have hta := ht a (Finset.mem_insert_self _ _)
    have htb := ht b (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    cases d with
    | false =>
      have sideAnd : ∀ {x y : Sig} (hx : Valid x) (hy : Valid y) (hxy : x ≠ y)
          (hfx : bin false x y ∉ insert x (insert y U))
          (tail' : Live k t (insert (bin false x y) U))
          (htx : WireTagOk (k + 1) (insert x (insert y U)) x (τ x)),
          τ x ≠ .tSpec0 ∧ (τ x ≠ .tNone → x ∉ U) := by
        intro x y _ _ _ hfx tail' htx
        constructor
        · intro heq; rw [heq] at htx
          obtain ⟨i, hp0, hti⟩ := htx
          have hz : ¬ proper (i.fn x) := fun hp => hp.2.1 hp0
          have hg0 : ¬ proper (i.fn (bin false x y)) := fun hp =>
            hp.2.1 (by rw [i.hbin, hp0, bin_comm]; exact (bin_laws (i.valid y)).2.2.1)
          obtain ⟨q, hq, hfe⟩ := feasible_const tail' i (bin false x y) (Finset.mem_insert_self _ _) hg0
          exact hti q (by omega) (free_binary_left hz hfe)
        · intro hne hxU
          cases htxc : τ x with
          | tNone => exact hne htxc
          | tSpec0 =>
            rw [htxc] at htx
            obtain ⟨i, hp0, hti⟩ := htx
            have hz : ¬ proper (i.fn x) := fun hp => hp.2.1 hp0
            obtain ⟨q, hq, hfe⟩ := feasible_const tail' i x (Finset.mem_insert_of_mem hxU) hz
            exact hti q (by omega) (free_binary_left hz hfe)
          | tSpec1 =>
            rw [htxc] at htx
            obtain ⟨i, hp1, hti⟩ := htx
            have ho : ¬ proper (i.fn x) := fun hp => hp.2.2 hp1
            obtain ⟨q, hq, hfe⟩ := feasible_const tail' i x (Finset.mem_insert_of_mem hxU) ho
            exact hti q (by omega) (free_binary_left ho hfe)
          | tDeg3 =>
            rw [htxc] at htx
            obtain ⟨i, hp0, hsl⟩ := htx
            have hz : ¬ proper (i.fn x) := fun hp => hp.2.1 hp0
            have hg0 : ¬ proper (i.fn (bin false x y)) := fun hp =>
              hp.2.1 (by rw [i.hbin, hp0, bin_comm]; exact (bin_laws (i.valid y)).2.2.1)
            have hne' : bin false x y ≠ x := fun e => by rw [e] at hfx; exact hfx (Finset.mem_insert_self _ _)
            obtain ⟨q, hq, hfe⟩ := feasible_two_consts tail' i (bin false x y) x
              (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hxU) hne' hg0 hz
            exact hsl q (by omega) (free_binary_left hz hfe)
      have hra := sideAnd ha.1 hb.1 hab hf tail hta
      have hrb : τ b ≠ .tSpec0 ∧ (τ b ≠ .tNone → b ∉ U) :=
        sideAnd hb.1 ha.1 hab.symm (by rwa [bin_comm, Finset.insert_comm])
          (by rwa [bin_comm]) (by rwa [Finset.insert_comm])
      have ht' : TagOk k (insert (bin false a b) U) (updAndTag τ a b) := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxU
        · unfold updAndTag; simp only [ite_true]
          split
          · rename_i hd
            rcases hd with hda | hdb
            · rw [hda] at hta
              obtain ⟨i, hp0, hsl⟩ := hta
              have hz : ¬ proper (i.fn a) := fun hp => hp.2.1 hp0
              refine ⟨i, by rw [i.hbin, hp0, bin_comm]; exact (bin_laws (i.valid b)).2.2.1, ?_⟩
              intro q hq hfe; exact hsl q (by omega) (free_binary_left hz hfe)
            · rw [hdb] at htb
              obtain ⟨i, hp0, hsl⟩ := htb
              have hz : ¬ proper (i.fn b) := fun hp => hp.2.1 hp0
              refine ⟨i, by rw [i.hbin, hp0]; exact (bin_laws (i.valid a)).2.2.1, ?_⟩
              intro q hq hfe; exact hsl q (by omega) (free_binary_right hz hfe)
          · trivial
        · have hne : x ≠ bin false a b := fun e => hf (e ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU))
          unfold updAndTag; simp only [hne, ite_false]
          exact wireTagOk_binary_step (ht x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU)))
      exact TRestricted.binaryAnd ha hb hab hf hra hrb (ih ht')
    | true =>
      have sideOr : ∀ {x y : Sig}
          (tail' : Live k t (insert (bin true x y) U))
          (htx : WireTagOk (k + 1) (insert x (insert y U)) x (τ x)),
          τ x ≠ .tSpec1 ∧ (τ x = .tSpec0 → x ∉ U) := by
        intro x y tail' htx
        constructor
        · intro heq; rw [heq] at htx
          obtain ⟨i, hp1, hti⟩ := htx
          have ho : ¬ proper (i.fn x) := fun hp => hp.2.2 hp1
          have hg1 : ¬ proper (i.fn (bin true x y)) := fun hp =>
            hp.2.2 (by rw [i.hbin, hp1, bin_comm]; exact (bin_laws (i.valid y)).2.2.2.1)
          obtain ⟨q, hq, hfe⟩ := feasible_const tail' i (bin true x y) (Finset.mem_insert_self _ _) hg1
          exact hti q (by omega) (free_binary_left ho hfe)
        · intro heq hxU; rw [heq] at htx
          obtain ⟨i, hp0, hti⟩ := htx
          have hz : ¬ proper (i.fn x) := fun hp => hp.2.1 hp0
          obtain ⟨q, hq, hfe⟩ := feasible_const tail' i x (Finset.mem_insert_of_mem hxU) hz
          exact hti q (by omega) (free_binary_left hz hfe)
      have hra := sideOr tail hta
      have hrb : τ b ≠ .tSpec1 ∧ (τ b = .tSpec0 → b ∉ U) :=
        sideOr (by rwa [bin_comm]) (by rwa [Finset.insert_comm])
      have ht' : TagOk k (insert (bin true a b) U) (updOrTag τ a b) := by
        intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hxU
        · unfold updOrTag; simp only [ite_true]; trivial
        · have hne : x ≠ bin true a b := fun e => hf (e ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU))
          unfold updOrTag; simp only [hne, ite_false]
          by_cases hxa : x = a ∧ τ a = .tDeg3
          · simp only [hxa]
            obtain ⟨rfl, hd3⟩ := hxa
            rw [hd3] at hta
            obtain ⟨i, hp0, hsl⟩ := hta
            have hz : ¬ proper (i.fn x) := fun hp => hp.2.1 hp0
            refine ⟨i, hp0, fun q hq hfe => hsl q (by omega) (free_binary_left hz hfe)⟩
          · simp only [hxa, ite_false]
            by_cases hxb : x = b ∧ τ b = .tDeg3
            · simp only [hxb]
              obtain ⟨rfl, hd3⟩ := hxb
              rw [hd3] at htb
              obtain ⟨i, hp0, hsl⟩ := htb
              have hz : ¬ proper (i.fn x) := fun hp => hp.2.1 hp0
              refine ⟨i, hp0, fun q hq hfe => hsl q (by omega) (free_binary_right hz hfe)⟩
            · simp only [hxb, ite_false]
              exact wireTagOk_binary_step (ht x (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hxU)))
      exact TRestricted.binaryOr ha hb hab hf hra hrb (ih ht')

end VariableProjection

def thetaOriginalBits : List Sig := [
  (0x3ffffffffffffffffffffffffffffffffffffffffffffff4d849641ddb12bd3612590776c4aa3c0228ae44945e8f008a2b912517,0x3fffffffffffffffffffffffffffffffffffffffffffff24386c0009da09c90e1b0002768270350420a044145c0d410828110517),
  (0xa3c0228ae44945e8f008a2b912517f4d849641ddb12bd3612590776c4a,0x3fffffffffffffffffffffffffffffffffffffffffffff0350420a044145c0d41082811051724386c0009da09c90e1b000276827),
  (0x911898c4c8749724462631321d25c911898c4c8749724462631321d25c,0x808390c5d024922020e4317409248808390c5d024922020e4317409248),
  (0x3fffffffffffffffffffffffffffffffffffffffffffff6f20c0b39707a20109d54109a92380850a05d229a2000a9c790c46d3e3,0x4002ba9605a20001c441a981418000dbd45209a0000282330446c2e0),
  (0x850a05d229a2000a9c790c46d3e36f20c0b39707a20109d54109a9238,0xdbd45209a0000282330446c2e0004002ba9605a20001c441a981418),
  (0x427550426a48e1bc8302ce5c1e8802a71e4311b4f8c214281748a6880,0x71106a60506001000aea58168800a08cc111b0b800036f514826800),
  (0x2a71e4311b4f8c214281748a68800427550426a48e1bc8302ce5c1e88,0xa08cc111b0b800036f51482680000071106a60506001000aea581688)]

def theta3Bits : List Sig := [
  (0x3ffffffffffffffffffffffffffffffffffffffffffffff4d849641ddb12bd3612590776c4aa3c0228ae44945e8f008a2b912517,0x3fffffffffffffffffffffffffffffffffffffffffffff24386c0009da09c90e1b0002768270350420a044145c0d410828110517),
  (0xa3c0228ae44945e8f008a2b912517f4d849641ddb12bd3612590776c4a,0x3fffffffffffffffffffffffffffffffffffffffffffff0350420a044145c0d41082811051724386c0009da09c90e1b000276827),
  (0x3fffffffffffffffffffffffffffffffffffffffffffff6ee7673b378b68dbb9d9cecde2da36ee7673b378b68dbb9d9cecde2da3,0x3fffffffffffffffffffffffffffffffffffffffffffff7f7c6f3a2fdb6ddfdf1bce8bf6db77f7c6f3a2fdb6ddfdf1bce8bf6db7),
  (0x3fffffffffffffffffffffffffffffffffffffffffffff6f20c0b39707a20109d54109a92380850a05d229a2000a9c790c46d3e3,0x4002ba9605a20001c441a981418000dbd45209a0000282330446c2e0),
  (0x850a05d229a2000a9c790c46d3e36f20c0b39707a20109d54109a9238,0xdbd45209a0000282330446c2e0004002ba9605a20001c441a981418),
  (0x427550426a48e1bc8302ce5c1e8802a71e4311b4f8c214281748a6880,0x71106a60506001000aea58168800a08cc111b0b800036f514826800),
  (0x2a71e4311b4f8c214281748a68800427550426a48e1bc8302ce5c1e88,0xa08cc111b0b800036f51482680000071106a60506001000aea581688)]

def theta6Bits : List Sig := [
  (0x3ffffffffffffffffffffffffffffffffffffffffffffff4d849641ddb12bd3612590776c4aa3c0228ae44945e8f008a2b912517,0x3fffffffffffffffffffffffffffffffffffffffffffff24386c0009da09c90e1b0002768270350420a044145c0d410828110517),
  (0xa3c0228ae44945e8f008a2b912517f4d849641ddb12bd3612590776c4a,0x3fffffffffffffffffffffffffffffffffffffffffffff0350420a044145c0d41082811051724386c0009da09c90e1b000276827),
  (0x911898c4c8749724462631321d25c911898c4c8749724462631321d25c,0x808390c5d024922020e4317409248808390c5d024922020e4317409248),
  (0x3fffffffffffffffffffffffffffffffffffffffffffff6f20c0b39707a20109d54109a92380850a05d229a2000a9c790c46d3e3,0x4002ba9605a20001c441a981418000dbd45209a0000282330446c2e0),
  (0x3ffffffffffffffffffffffffffffffffffffffffffffff7af5fa2dd65dfff56386f3b92c1c90df3f4c68f85dfef62abef656dc7,0x3ffffffffffffffffffffffffffffffffffffffffffffffff242badf65ffffd7dccfbb93d1fffbffd4569fa5dfffe3bbe567ebe7),
  (0x427550426a48e1bc8302ce5c1e8802a71e4311b4f8c214281748a6880,0x71106a60506001000aea58168800a08cc111b0b800036f514826800),
  (0x2a71e4311b4f8c214281748a68800427550426a48e1bc8302ce5c1e88,0xa08cc111b0b800036f51482680000071106a60506001000aea581688)]

def theta7Bits : List Sig := [
  (0x3ffffffffffffffffffffffffffffffffffffffffffffff4d849641ddb12bd3612590776c4aa3c0228ae44945e8f008a2b912517,0x3fffffffffffffffffffffffffffffffffffffffffffff24386c0009da09c90e1b0002768270350420a044145c0d410828110517),
  (0xa3c0228ae44945e8f008a2b912517f4d849641ddb12bd3612590776c4a,0x3fffffffffffffffffffffffffffffffffffffffffffff0350420a044145c0d41082811051724386c0009da09c90e1b000276827),
  (0x911898c4c8749724462631321d25c911898c4c8749724462631321d25c,0x808390c5d024922020e4317409248808390c5d024922020e4317409248),
  (0x3fffffffffffffffffffffffffffffffffffffffffffff6f20c0b39707a20109d54109a92380850a05d229a2000a9c790c46d3e3,0x4002ba9605a20001c441a981418000dbd45209a0000282330446c2e0),
  (0x850a05d229a2000a9c790c46d3e36f20c0b39707a20109d54109a9238,0xdbd45209a0000282330446c2e0004002ba9605a20001c441a981418),
  (0x3ffffffffffffffffffffffffffffffffffffffffffffffbd8aafbd95b71e437cfd31a3e177fd58e1bcee4b073debd7e8b75977f,0x3ffffffffffffffffffffffffffffffffffffffffffffffff8eef959faf9ffefff515a7e977ff5f733eee4f47fffc90aeb7d97ff),
  (0x2a71e4311b4f8c214281748a68800427550426a48e1bc8302ce5c1e88,0xa08cc111b0b800036f51482680000071106a60506001000aea581688)]

def eightBits : List Sig := [
  (0x3ffffffffffffffffffffffffffffffffffffffff988c662c60004200118004e25321040016c0030d9e4a00039fffd8007000fff,0x988c622c6d1042d111b44462532105c212dc21048e4ae20089c49b883710712),
  (0x3ffffffffffffffffffffffffffffffffffffffff2130860080010c00060007c01c3e180027000332607ffff2640020007ffffff,0x2130840090850d0886422180040e1a2125221210201110d226222444488a88c),
  (0xf88f000070001800070463c0200039fffcc3878c001c78003fff9fff000,0x288f043070431810c6040140208600486843828c4604588c09191234230),
  (0xc03f0130000180001ffff8387c07c0003e0000fc07f0001f80003fffe000000,0xc015013001c5801c828730387c07c0693e0690bc0570389b807230e661c81c8),
  (0x1c001c00001ffffe000003f8007ffffc00000fff800001fffffc0000000000,0x1c000659406c001a00c8002680d8000d0fb70000c9f741b00340068068),
  (0x3ffffffffffffffffffffffffffffffffffffffff01fffe000001ffffffffffc00007ffffffffff000000001ffffffffffffffff,0x3ffffffffffffffffffffffffffffffffffffffff35fffe0ade87ffe8fffa3fc0040fffb1fffb1f102011d0ffffa3ff47fe8fe8f),
  (0xfffffe00000000000000003fffffffffffffff0000000000000000000000000,0xffffd60019800198006600337ebd97703fb703000001b000036006c00d80d80),
  (0xffffffffffffffffffffffc0000000000000000000000000000000000000000,0x35eafe0ade006be01d7807c000000380003800000001c000038007000e00e00)]

def ordinaryEightBits : List Sig := [
  (0x3ffffffffffffffffffffffffffffffffffffffff988c662c60004200118004e25321040016c0030d9e4a00039fffd8007000fff,0x988c622c6d1042d111b44462532105c212dc21048e4ae20089c49b883710712),
  (0x3ffffffffffffffffffffffffffffffffffffffff2130860080010c00060007c01c3e180027000332607ffff2640020007ffffff,0x2130840090850d0886422180040e1a2125221210201110d226222444488a88c),
  (0xf88f000070001800070463c0200039fffcc3878c001c78003fff9fff000,0x288f043070431810c6040140208600486843828c4604588c09191234230),
  (0xc03f0130000180001ffff8387c07c0003e0000fc07f0001f80003fffe000000,0xc015013001c5801c828730387c07c0693e0690bc0570389b807230e661c81c8),
  (0x1c001c00001ffffe000003f8007ffffc00000fff800001fffffc0000000000,0x1c000659406c001a00c8002680d8000d0fb70000c9f741b00340068068),
  (0xfe0001fffffe00000000003ffff80000000000ffffffffe0000000000000000,0xca0001f5217800170005c03ffbf0004e0004e0efdfee2f00005c00b80170170),
  (0xfffffe00000000000000003fffffffffffffff0000000000000000000000000,0xffffd60019800198006600337ebd97703fb703000001b000036006c00d80d80),
  (0xffffffffffffffffffffffc0000000000000000000000000000000000000000,0x35eafe0ade006be01d7807c000000380003800000001c000038007000e00e00)]

def sampleMap (key : Nat) (j : Fin 414) : Fin 414 :=
  Fin.ofNat 414 (index9 key (if j.val < 232 then j.val else 0))
def slice0Yes : Nat := 0x5b831481b209d18cb5643710e530d9e8f47a281d19a8a1f1e972665a988184166a658c595aa9dea390dbad1e394f2dd14626e2349ca446ae4b23e3d3b0f2a7642e56e667386cf4747abb1b8c8478f836412090514745c940a64166831d862331e972407aa6dd8a76324836eb43a48bab728189909644b9d2ccd4d94c82b53ca9db8cd5bb35b8a720b89245373a9136b5539e8f47a28388188a761e8ccb929bc19a4106331248f2986c72f553b8cb2f57a2dd14f05227db6dc4f9991eec3d0f9c81b739996eb96429cf4e21c8f948e72cbb14e412090514e2331416a41063347cf05c9e8ccfa1ca1c7c1b493194ee34db19f2b7283c1ce6079320c00c43ad482537206d480c
def slice0No : Nat := 0xe8001c00000395eaf1e28c70a527240ee97032949c9702815469001818040251a5c16060387520030702cca3802a9478052701c9c0b01abc6c3c1c3a00ea552a943a0007000000e57abca2e82729470360d00c0ca51c00c0a05740d92e06361b1d003058180e1d1b25c1c0b329380aa52881470071c02d2eaf481449ca303a954aa50e8015e00002bc1c0e3b939d0a5518d8780303a9546030582c9c364b81c88442700c0a07030746c9757814b0e805a94ee0b5181946054b8392077740e00ca552a943a005780000af07038343851a95d09028a5c0ea57425c160b1c2400607160b070970281c0c1d4800d5e052c28c16a50d02dd00674014060e1b069464e032954aa5
def slice0 : SigHom := pairHom (sampleMap slice0Yes) (sampleMap slice0No)
def slice3Yes : Nat := 0x1b2e58c2a66bc948a21c965ce5715198cc666cbc882721b998187a5116d72cd20a7548dc510011ec8153d1eac84f0d8e45b2cba5c4c674831b83733191e6001c8306c7a438a8ccf247990b2397a8dc54cd66b34e4f206364aecd20ae4c85b3d19818ca47a48c8005226c54f473a6dc6366c96c72f744a1dee414915d9aa279800b2411b104b20066939365743b1924a200198cc666c939727232198f40c2bb9482cd5ca9936f52b8a9908f00175b88f758d8e4e563251b6594a1e9ea64330dc9e2a439e86c0c1c800cc4e640dd8c876e19000cd66b34e44e3d36544cd5c9046ee506198f4916439c6e2a4da90005d49291f2366cb950ede3a0e5bcb973a899a57278a98cb9
def slice3No : Nat := 0x8005800000b004020c28c70362c240c891020d8b091028154690048115eaf51a4416040500520091602dd038028d830052c028b00b048094a181c19414361b0d8020016000002c010089a652c0d870a55102408361c0240a0532a952204361b0ca0905810140152a44580b741600a3626814700a1c02d220248134b0a3050d86c3600800040000008582c32160ca3651a943009050d946090582cb0a54882888442c0240a0a020054a91010149c65058d8c80b518114605488b12064328e008361b0d80200010000002160b14438518d8ca9026a44143632a44160b1c240120a0703870910282808014802404052728c16365102cca0432814122c52a894658020d86c36
def slice3 : SigHom := pairHom (sampleMap slice3Yes) (sampleMap slice3No)
def slice6Yes : Nat := 0x448307266000a58c87640dd6a723329d4ea7320a454ec73a9d721b43ba41800151e18ca2439e876a43310032a45c225d8e91bbc03039782e544e753a28f27a642e5121b1f1994e291da286ec80cb9ccc0000001d8295c990e4001503114e90da9d72eb1dacd147a6309ccc405a89d4c89323a590755b8f8ea2a599c800873c9e86e2a448a86e7a003144e721f0e566873d29d4ea73231418ec4529c36b9392345400063d04e1939199483b3d329443b66225d88d1cbb86c377706c328a53b9de6661f06d12b9641e94ec55239c723e51228f40000001d8c50d9910e00060a9ce8d5ca9c368c522d5ce6613b18f4ca59b187a89322347ce565b21ca0c5aa1c007279998720c
def slice6No : Nat := 0x360001c0000038582c740d94a380c064ee75050e03075048246c190582804021b1d4060a039b0320b0700c34a5048e1d0090c01c3003058b146e8528f00e381c0e0d80007000000e160b0c83c0c0e14aa33282c14385282c12091e28cea0a0e874780b018280e6c519d41c030d0601238320254a075280cea2c0c9903036038e07038360005800000b01c0e3b86078381b28dd00b038e06c0b0180c30a33a81c02010c02c1207051b1467516025443c018e0ee031b0286c093a83832771e29414381c0e0d80016000002c07038caa51b0e07819321d40e381e1d4060352864160757abd4a750481c146c0c82c5809510d806383280c780a1e024160e519946c18050e07038
def slice6 : SigHom := pairHom (sampleMap slice6Yes) (sampleMap slice6No)
def slice7Yes : Nat := 0x6d80144411506166d95ab184e592086c361b2b86172532806d4e0c6c980002a5c975663b6cb35901920a986e192036ca660631546ca22aa9c76500db709ecd5aa9db60c521043618643718cb51b940822a150a8a6185395cb22a5c801b8600606d4e52640f9b8cd598e482a6138e47adb2b9816a5b14a90b6b91f16454d927b358cb96dae58ccd1532c7259522887cd96686c361b2bb2c00536e06c18a72cb79722a0038472372c90432c866b3076c85c36ca6de511898ac6310306edc0d941c84152031b6a75ab3436cb0c94144a41db719a2a150a8a6cb0615db22a002e4a0de5386c18e30c89ca0411cacd9acc1f2cd94db2bb79485e5bad4bc0013b645459721054400
def slice7No : Nat := 0x220000400000095eaf28a8834a31b0e09c050328c6c050180d443829018020151014120602110705201024301a01a8ca2031b0106c09292bc32510d29408a351a8c880001000000257abcb0a51b28c3419269480ca30d1480603528640a06070394a520481808440c81404090c0d806a32c00c34040d0240aaf1c1606ca20228d46a3220015e00002bc0402270d94aa351064a2520228d4452048246c1902810582c1b14806040311032055780c78a504a8c9c0951019440302808704e528680ca351a8c88005780000af010089a1a5128d4a382c01408a35281412090d0e0a4040e8743405018100c441c1495e031e28812a3268254a065280ca4020c93544360328d46a3
def slice7 : SigHom := pairHom (sampleMap slice7Yes) (sampleMap slice7No)

def eightWires : List Wire := [
  (eightBits.getD 0 zero,.tSpec0),(eightBits.getD 1 zero,.tNone),
  (eightBits.getD 2 zero,.tNone),(eightBits.getD 3 zero,.tSpec0),
  (eightBits.getD 4 zero,.tNone),(eightBits.getD 5 zero,.tSpec1),
  (eightBits.getD 6 zero,.tSpec0),(eightBits.getD 7 zero,.tNone)]
def eightTag (a : Sig) : Tag :=
  if a = eightBits.getD 5 zero then .tSpec1
  else if a = eightBits.getD 0 zero ∨ a = eightBits.getD 3 zero ∨ a = eightBits.getD 6 zero
    then .tSpec0 else .tNone



def ordinaryEightWires : List Wire := [
  (ordinaryEightBits.getD 0 zero,.tSpec0),(ordinaryEightBits.getD 1 zero,.tNone),
  (ordinaryEightBits.getD 2 zero,.tNone),(ordinaryEightBits.getD 3 zero,.tSpec0),
  (ordinaryEightBits.getD 4 zero,.tNone),(ordinaryEightBits.getD 5 zero,.tSpec0),
  (ordinaryEightBits.getD 6 zero,.tSpec0),(ordinaryEightBits.getD 7 zero,.tNone)]
def ordinaryEightTag (a : Sig) : Tag :=
  if a = ordinaryEightBits.getD 5 zero then .tSpec0
  else if a = ordinaryEightBits.getD 0 zero ∨ a = ordinaryEightBits.getD 3 zero ∨ a = ordinaryEightBits.getD 6 zero
    then .tSpec0 else .tNone



def fullWires : List Wire := [
  (raw0,.tDeg3),(raw1,.tDeg3),(raw2,.tDeg3),(raw3,.tDeg3),(neg raw4,.tSpec1),
  (raw5,.tDeg3),(raw6,.tSpec0),(raw7,.tSpec0),(raw8,.tDeg3)]
def fullTag (z : Sig) : Tag :=
  if z = neg raw4 then .tSpec1 else if z = raw6 ∨ z = raw7 then .tSpec0 else .tDeg3


def valueAt (j : Fin 9) (a : Sig) : Sig := if a = raw.getD j.val zero then neg a else a
def sourcesAt (j : Fin 9) : List Sig := (raw.erase (raw.getD j.val zero)) ++ [neg (raw.getD j.val zero)]
def signedThetaAt (j : Fin 9) : List Sig := (thetaOrder.map (valueAt j)).map fun a => projectLeaf (project0 a)
def signedEight : List Sig := (raw1007Order.map (valueAt 6)).map project4
def smallerBound (n : Nat) (v : List Sig) : Prop :=
  ∀ k ≤ n, ∀ t S, Live k t S → (∀ a ∈ S, a ∈ v) → False


def signedRaw : List Sig := [raw0,raw1,raw2,raw3,neg raw4,raw5,raw6,raw7,raw8]

def bare (v : List Sig) : List Wire := v.map fun a => (a,.tNone)

def landsIn (H : SigHom) (xs ys : List Sig) : Bool :=
  xs.all fun x => decide (H.fn x = zero ∨ H.fn x = one ∨ H.fn x ∈ ys)
lemma fromMinor (H : SigHom) (xs ys : List Sig) (budget : Nat)
    (table : landsIn H xs ys = true) (lower : smallerBound budget ys) :
    ¬ Feasible H budget xs.toFinset := by
  rintro ⟨m,hm,t,T,live,sub⟩
  apply lower m hm t T live
  intro a ha
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp (sub ha)
  have opts := List.all_eq_true.mp table b (List.mem_toFinset.mp hb)
  obtain e | e | good := of_decide_eq_true opts
  · exact False.elim ((live_proper live _ ha).2.1 e)
  · exact False.elim ((live_proper live _ ha).2.2 e)
  · exact good




lemma tableLower (v : List Sig) (w : List Wire) (τ : Sig → Tag) (budget extra : Nat)
    (room : budget + 1 ≤ v.length + extra) (nd : v.Nodup)
    (fits : v.all (fun a => decide (a.1 ≤ top ∧ a.2 ≤ top)) = true)
    (needed : v.all (fun a => unionSep true (v.erase a) != top) = true)
    (rep : Represents w v.toFinset τ)
    (constrain : ∀ k ≤ budget, ∀ t, Live k t v.toFinset → TRestricted k t v.toFinset τ)
    (checked : ∀ t ≤ extra, Impossible budget t w) : smallerBound budget v := by
  intro k size t S live sub
  have valid (a : Sig) (ha : a ∈ v) : Valid a := by
    have p := of_decide_eq_true (List.all_eq_true.mp fits a ha)
    exact ⟨valid1_of_le_top p.1,valid1_of_le_top p.2⟩
  have eq : v.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hr => ?_,sub a⟩
    by_contra hn
    have fail := List.all_eq_true.mp needed a hr
    have cov : unionSep true (v.erase a) = top := by
      apply Nat.eq_of_testBit_eq
      intro i
      rw [testBit_top]
      by_cases hi : i < 414
      · simp only [hi,decide_true]
        obtain ⟨b,hb,h⟩ := live_sep live i hi
        have ba : b ≠ a := fun he => hn (he ▸ hb)
        have hm := (List.mem_erase_of_ne ba).mpr (sub _ hb)
        exact (mem_unionSep true _ _).2 ⟨b,hm,sep_weaken _ (live_proper live b hb).1 i hi h⟩
      · simp only [hi,decide_false]
        exact valid_unionSep (fun x hx => valid x (List.mem_of_mem_erase hx)) i (by omega)
    simp [cov] at fail
  subst S
  have sz := live_size live
  rw [List.toFinset_card_of_nodup nd] at sz

  exact checked t (by omega) k size _ _ rep (constrain k size t live)
lemma bareRep (v : List Sig) (nd : v.Nodup) : Represents (bare v) v.toFinset (fun _ => .tNone) := by
  have eq : sigsOf (bare v) = v := by simp [sigsOf,bare,Function.comp_def]
  refine ⟨by rwa [eq],by rw [eq],?_⟩
  intro w hw
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp hw
  rfl
lemma bareConstrain (v : List Sig) (k t : Nat) (hl : Live k t v.toFinset) :
    TRestricted k t v.toFinset (fun _ => .tNone) := by
  exact restrict_live hl (fun _ _ => trivial)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma slice0Bound : landsIn slice0 eightBits theta6Bits = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma slice0Value : slice0.fn (eightBits.getD 0 zero) = zero := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma slice3Bound : landsIn slice3 eightBits theta6Bits = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma slice3Value : slice3.fn (eightBits.getD 3 zero) = zero := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma slice6Bound : landsIn slice6 eightBits thetaOriginalBits = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma slice6Value : slice6.fn (eightBits.getD 5 zero) = one := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma slice7Bound : landsIn slice7 eightBits theta3Bits = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma slice7Value : slice7.fn (eightBits.getD 6 zero) = zero := by decide +kernel


lemma eightTagOk (hOriginal : smallerBound 10 thetaOriginalBits) (h6 : smallerBound 10 theta6Bits)
    (h3 : smallerBound 10 theta3Bits) {k : Nat} (small : k ≤ 12) :
    VariableProjection.TagOk k eightBits.toFinset eightTag := by
  intro a _
  unfold eightTag
  split
  · rename_i e
    subst a
    exact ⟨slice6,slice6Value,fun q hq hf =>
       fromMinor _ _ _ _ slice6Bound hOriginal (feasible_mono hf (by omega))⟩
  · split
    · rename_i e
      rcases e with rfl | rfl | rfl
      · exact ⟨slice0,slice0Value,fun q hq hf =>
          fromMinor _ _ _ _ slice0Bound h6 (feasible_mono hf (by omega))⟩
      · exact ⟨slice3,slice3Value,fun q hq hf =>
          fromMinor _ _ _ _ slice3Bound h6 (feasible_mono hf (by omega))⟩
      · exact ⟨slice7,slice7Value,fun q hq hf =>
          fromMinor _ _ _ _ slice7Bound h3 (feasible_mono hf (by omega))⟩
    · trivial
lemma eightRep : Represents eightWires eightBits.toFinset eightTag := by
  refine ⟨by decide +kernel,rfl,?_⟩
  intro w hw
  simp only [eightWires,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ordinarySlice0Bound : landsIn slice0 ordinaryEightBits thetaOriginalBits = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ordinarySlice0Value : slice0.fn (ordinaryEightBits.getD 0 zero) = zero := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ordinarySlice3Bound : landsIn slice3 ordinaryEightBits thetaOriginalBits = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ordinarySlice3Value : slice3.fn (ordinaryEightBits.getD 3 zero) = zero := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ordinarySlice6Bound : landsIn slice6 ordinaryEightBits thetaOriginalBits = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ordinarySlice6Value : slice6.fn (ordinaryEightBits.getD 5 zero) = zero := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ordinarySlice7Bound : landsIn slice7 ordinaryEightBits thetaOriginalBits = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ordinarySlice7Value : slice7.fn (ordinaryEightBits.getD 6 zero) = zero := by decide +kernel


lemma ordinaryEightTagOk (hOriginal : smallerBound 10 thetaOriginalBits)  {k : Nat} (small : k ≤ 12) :
    VariableProjection.TagOk k ordinaryEightBits.toFinset ordinaryEightTag := by
  intro a _
  unfold ordinaryEightTag
  split
  · rename_i e
    subst a
    exact ⟨slice6,ordinarySlice6Value,fun q hq hf =>
       fromMinor _ _ _ _ ordinarySlice6Bound hOriginal (feasible_mono hf (by omega))⟩
  · split
    · rename_i e
      rcases e with rfl | rfl | rfl
      · exact ⟨slice0,ordinarySlice0Value,fun q hq hf =>
          fromMinor _ _ _ _ ordinarySlice0Bound hOriginal (feasible_mono hf (by omega))⟩
      · exact ⟨slice3,ordinarySlice3Value,fun q hq hf =>
          fromMinor _ _ _ _ ordinarySlice3Bound hOriginal (feasible_mono hf (by omega))⟩
      · exact ⟨slice7,ordinarySlice7Value,fun q hq hf =>
          fromMinor _ _ _ _ ordinarySlice7Bound hOriginal (feasible_mono hf (by omega))⟩
    · trivial
lemma ordinaryEightRep : Represents ordinaryEightWires ordinaryEightBits.toFinset ordinaryEightTag := by
  refine ⟨by decide +kernel,rfl,?_⟩
  intro w hw
  simp only [ordinaryEightWires,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel


namespace ProofTable
def literalPosChunk (j : Nat) : Nat := (if j < 2 then (if j < 1 then 0x280000000fff000fff000000000000000000000ffffffc000820000ffffffffffffffe8420844000104010822084214000008401100003ffc000000003ffc0000000000000000021084108421044213ffffff004001007ffffffffffffff0100400040102000020a20fff000fff000000000fff0000000000000004210821084208842410842220842245ffffff002008043fffffffff8000404013f9fffffffffffffffffffffc000003ffffffffc00fefe0003bfff7c0def7e00ef7bf7801bffc01bbeff70001defffe006f777fd10c000000000fff000000000000ffffff000000210821084208441123ff00113fff800427e40227fc22008217ff200225fff1200218000000000003ffc000000000003fffffc000421043f883ff880041084422084244fc027c3e022ffc0f84010be21e40847fd0043000000000000000fff000000000000fffffff83e0805f0043f08082108fc3f087882104221104411145f87e017c179f0809e40c4000000000000000003fffffc000000003ffc210fe00847f007e01f83e01107e03e042084423f0fc3c08220842122287e3e0f else 0xffffffffffffffffffffffffffffffffffffffffc07fff8000007ffffffffff00001ffffffffffc000000007fffffffffffffffc000000000000000000000000000000000000000001c001c00001ffffe000003f8007ffffc00000fff800001fffffc00000000000000000000000000000000000000000000000000300fc04c0000600007fffe0e1f01f0000f80003f01fc0007e0000ffff800000000000000000000000000000000000000000000000000f88f000070001800070463c0200039fffcc3878c001c78003fff9fff000ffffffffffffffffffffffffffffffffffffffffc84c218020004300018001f0070f860009c000cc981ffffc990008001fffffffffffffffffffffffffffffffffffffffffffffff988c662c60004200118004e25321040016c0030d9e4a00039fffd8007000fff018000000000000000000000ffffff000000000ffc0407fff100020fc84207fc421021ff9000ff9104023fff8840007fe422200b403fffffc003ffc000000000000000000000003fffffffffffffffe084210008210004210422110882228411042108004210000) else (if j < 3 then 0xffffffffffffffffffffffffffffffffffffffffffffffdebd7e8b75977ffd58e1bcee4b072437cfd31a3e177fbd8aafbd95b71ffffffffffffffffffffffffffffffffffffffffffffff6f20c0b39707a20109d54109a92380850a05d229a2000a9c790c46d3e300000000000000000000000000000000000000000000024462631321d25c911898c4c8749724462631321d25c911898c4c874970000000000000000000000000000000000000000000000a3c0228ae44945e8f008a2b912517f4d849641ddb12bd3612590776c4affffffffffffffffffffffffffffffffffffffffffffffd3612590776c4af4d849641ddb12a8f008a2b912517a3c0228ae44945c0000000000000000000000000000000000000000fe0001fffffe00000000003ffff80000000000ffffffffe000000000000000000000000000000000000000000000000000000003ffffffffffffffffffffff000000000000000000000000000000000000000000000000000000000000000000000000000000000fffffe00000000000000003fffffffffffffff0000000000000000000000000 else 0xa9c790c46d3e30850a05d229a200109d54109a92386f20c0b39707a200000000000000000000000000000000000000000000000427550426a48e1bc8302ce5c1e8802a71e4311b4f8c214281748a6880))
def literalPos (i : Nat) : Nat := (literalPosChunk (i / 8) >>> (414 * (i % 8))) &&& 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def literalNegChunk (j : Nat) : Nat := (if j < 2 then (if j < 1 then 0xce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ce0ffffff8000000000ffffffffffffffe00000000000000000000000000000000000003703703703703703703703703703703703700000000000000003fffffe000000007ffffffffffffff000000000000000000000001b01b01b01b01b01b01b01b01b01b01b01b0000000000000000000000000000001ffffff000000003fffffffff8000000003ffd5b55b55b55b55b55b55b55b55b55b55b55b400fffe0003fffffc0ffffe00ffffff801fffc01ffffff0001fffffe007ffffff000069069069069069069069069069069069069000000000000000003ff00003fff800007e00007fc00000007ff000001fff0000000c50c50c50c50c50c50c50c50c50c50c50c50000001f803ff8000000000000000007c007c3e000ffc0f800003e01e00003fc0000823823823823823823823823823823823823f83e0001f0001f000000007c3f007800000000000000001f87e007c079f0000e00015115115115115115115115115115115115100007e00003f003e00f83e00003e01e000000001f0fc3c00000000000003e3e07 else 0xffffffffffffffffffffffffffffffffffffffffcd7fff82b7a1fffa3ffe8ff00103ffec7ffec7c40804743fffe8ffd1ffa3fa3c0000000000000000000000000000000000000000000001c000659406c001a00c8002680d8000d0fb70000c9f741b0034006806800000000000000000000000000000000000000003005404c0071600720a1cc0e1f01f01a4f81a42f015c0e26e01c8c399872072000000000000000000000000000000000000000000000288f043070431810c6040140208600486843828c4604588c091912342300000000000000000000000000000000000000000084c21002421434221908860010386884948848408044434898889111222a2300000000000000000000000000000000000000000988c622c6d1042d111b44462532105c212dc21048e4ae20089c49b883710712000a92a92a92a92a92a92a92a92a92a92a92a92ffc0007fff000000fc00007fc000001ff8000ff8000003fff8000007fe0000000003c03c03c03c03c03c03c03c03c03c03c03c03fffffffffffffffc000000000000000000000000000000000000000000000000) else (if j < 3 then 0xffffffffffffffffffffffffffffffffffffffffffffffffc90aeb7d97ffff5f733eee4f47ffefff515a7e977fff8eef959faf9c000000000000000000000000000000000000000000000004002ba9605a20001c441a981418000dbd45209a0000282330446c2e00000000000000000000000000000000000000000000002020e4317409248808390c5d024922020e4317409248808390c5d024923fffffffffffffffffffffffffffffffffffffffffffff0350420a044145c0d41082811051724386c0009da09c90e1b000276827fffffffffffffffffffffffffffffffffffffffffffffc90e1b00027682724386c0009da09c0d4108281105170350420a044145c0000000000000000000000000000000000000000ca0001f5217800170005c03ffbf0004e0004e0efdfee2f00005c00b8017017000000000000000000000000000000000000000000d7abf82b7801af8075e01f0000000e0000e00000000700000e001c0038038000000000000000000000000000000000000000000ffffd60019800198006600337ebd97703fb703000001b000036006c00d80d80 else 0x282330446c2e0000dbd45209a000001c441a981418004002ba9605a2000000000000000000000000000000000000000000000000071106a60506001000aea58168800a08cc111b0b800036f514826800))
def literalNeg (i : Nat) : Nat := (literalNegChunk (i / 8) >>> (414 * (i % 8))) &&& 0x3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff
def gateRecipeChunk (j : Nat) : Nat := (if j < 5 then (if j < 2 then (if j < 1 then 0x114000b50e0048000e106c1381b02306c02c1b0030001b41a05e06805c1a00f068038000690001f4000850002041705605405c1500b054028150030001541704e04c05c1300f04c02c0004d0002241701705c03c1700b05c00c0005d02005c0800f01403c0800b01402c0300b02001c0500700c01c0200702000c0500300c00c0200300400c000210000540000d000024000050000040002000007000018000050000100000300000800001000000 else 0x741b80007506c1081003e0000f41b022064108160420004b400145000344000d50002c4001c50a8048000a905410811042000464001ad100048001010681681a056068188160020006441f05a0002741805600060426012000264000610641681604a04c1280009505c1681604e00016453046054138150460004141301604801c0004904001c0004106c1a81b06606401c001250e41a8000e506819819003000194000f506c118130460440481100b) else (if j < 3 then 0x11407c4501711403c4500711400c5e02317803c5e00b17801c7e0170a408c2900715c01c7e00f0dc03c370030dc08c370170dc02c3f02321c03c8700b21c01c8700308c06c3f00f0fc01c2900f0a400c3f0170fc02c2900b14005c500072701781e01b07805c1e00f07802c1e00709008c2400f09000c6302318c05c6300315c08c5700b15c00c650170c406c310070c400c150520580f8140420001441d04e0701a8100060004f4000e90701b800071 else (if j < 4 then 0x3a4e48003a53b4e58ed3933b4e48ed38b3b4e28003b5000e7400391000e240038539ce4ce739239ce2ce738a390e2ce438a39ce1ce7386390e1ce4386388e1ce2386000110000400000f0000380000d0000300000b0000280000902f01b0c006c7401f0fc00c7701f2fc1984e00313801c4e00b0c802c6d01f1b405c8002320005c8000f1a803c1e0231f808c7b0171ec02c7b0071ec00c7500b14000c320170c803c3200712808c4801f11402c45023 else 0x3a8e3cea38b000ea4eb38a000eb4ee39f3b8e1c003b93bce78ef386000ef5323923c0e4cf0383000f0511392444e29233b2480e4925392494e292938a440e792739e3ece3d1c38a3c8e6cf238f3c8e2cf238a3c8e1cf2383000f24f33b63cce28f3386000f3516392428e48f13933c4e48f1386000f15123863e4e48f93833b0e6cec3933b0e48003b1404e490138b000fd4e839f3a0e78e839b3a0e4ce83923a0e3ce8383000e84ed3a63a4e78e9393))) else (if j < 7 then (if j < 6 then 0x3d4e4cf53923d4e1cf53865cce28005cd001744f639f3d8e78f638b3d8e28f63873d8e196b38a0016b4f73933dce48f738b3dce28f73873dce190639b418e3d063830010652239b488e3d223830012252348643ce6d0f38f43ce2d0f3830010f50939b424e4d0938f424e0c004254fce795439e550e190b3bb44ce7d133874c8e193f38a534e794d38642cf2d2438a48ce1920386414e790538a410e4908392420e290739e504e794138642ce8d2138a else 0x6759cd9d67267d9bd9f66e6799bd9e66e6759bd9d66e6719bd9c66e67d9ad9f66a6799ad9e66a6759ad9d66a6719ad9c66a66d9ad9b66a67d99d9f66667999d9e66667599d9d66667199d9c66666d99d9b66666999d9a66600019000060000170000580001500005000013000048001965033960019456339600192538396454e3c0063d59ce580063547ce580062d560e5800625574e593539b5f8e793b3834a4f48f439e3d0e2cf438a3d4e7cf539e) else (if j < 8 then 0x739c8dc86737219bdc8667739a3da367f7d99a9f766a739acdac67f6b19cdac667001ac5f067a7b59e9d173b7a99e9ea66e7459fdd167b7459bdd166b739b39e173b739bb9e16737859bde166b78599dbb6ce6cd9f9ce673751ce9ce67f7399f9ce67b7399e9ce66f7399b9ce66b7399a9ce667739999d36736ed9d9bb6736ed9980067d0019e4006750019c40066d0019a40066567d9ed9f67a67d9dd9f6766799dd9e67667d9cd9f6726799cd9e672 else (if j < 9 then 0x8999ee2b672739a4da467f6919eda466b001a46296738d59ca34672839cee0e67f77d9fddf67b77d9bddf6678419bdce6968a59fe2967b8a59ae29667739af9af67e8959ea2566a6c99fdb2673769ada2166f83dce9bd6b6739a8df173b7c59cdf166b6a19fda86736a19ac006a16899fda26736899ac006898499bdfa67a6dda39b767e6dd9adb7666739a19a167e6859ca0966f7ed9c800711001c55c1666001b8400721739a9de766f7f19f9ce6f7 else 0x7359ddcf67f73d9f9cf67373d9c9cf66f73d9b9cf66b73d9a9cf66773d99a506777319fdcc67e7319edcc67a7319cdcc6727319adcc66a73199dcc666001b44006c56b99edce6d36d199e2867375d9fdd767b75d99e3767f8dd9adde75a7799aa4367b80d9c8006e57559fdce68b))))
def gateRecipe (i : Nat) : Nat := (gateRecipeChunk (i / 64) >>> (22 * (i % 64))) &&& 0x3fffff
def inverseGroupChunk (_j : Nat) : Nat := 0x2b49c2327b9ac5a927418a320820
def inverseGroup (i : Nat) : Nat := (inverseGroupChunk (i / 32) >>> (5 * (i % 32))) &&& 31
def sourceCodeChunk (j : Nat) : Nat := (if j < 2 then (if j < 1 then 0x34b28f0404471430000000000000000000000003c734a44014304b0000000000000000000000003473ca14044b04300000000000000000000000028534f0c91d12c1000000000000000000000000000000000000000 else 0x3413ca2c00c51d10000000000000000000000003c134a0c02d11c500000000000000000000000034528f1c00c12d10000000000000000000000003d128d1c02c10c50000000000000000000000003c328d04014744b000) else (if j < 3 then 0x205e17d955d8db0000000000000000000000000217608a355765b0000000000000000000000000216608976e37550000000000000000000000000000000000000002833cd14904b44700000000000000000000000028b34f449043147000000 else (if j < 4 then 0x155db59982376100000000000000000000000001b8d571d81766100000000000000000000000000065571785d8e000000000000000000000000001575b5a38595e0000000000000000000000000 else 0xb70cb3ae7a40000000000000000000000000000c73bb0ae7a40000000000000000000000000000c2dd31ae99c0)))
def sourceCode (i : Nat) : Nat := (sourceCodeChunk (i / 128) >>> (6 * (i % 128))) &&& 63
def groupKeyIdsChunk (_j : Nat) : Nat := 0xf1de1bd19c17b15a1391180f70d60b50a489408387306285204183102081000000
def groupKeyIds (i : Nat) : Nat := (groupKeyIdsChunk (i / 128) >>> (12 * (i % 128))) &&& 0xfff
def moveIndex (key i : Nat) : Nat := (if Nat.blt key 15 then (if Nat.blt key 7 then (if Nat.blt key 3 then (if Nat.blt key 1 then (if Nat.beq key 0 then (if Nat.blt i 413 then index9 0x199cc653399bc965b2b9acee5e25108bc5a2b1488c66271887c3ab558afd7abb5cacd86b760abd5a9d4ca9d4aa350a6d569f54a5d2a3d1c91c8a43208ec963f248dc6afd7cc1e0b0380bee16ff84bddeae570bbddaeb74b8de6e778b7dba0d0485c2a130882c360f0c81c0a6d349dcea73389acf66f3c99cca552897cba5b2c94cc6573093c9acd64b5daad368b2db6cf6cb1d8b1588c7e3b1b8cc4e471790c3e1a8540a3d1a8b44a0d2687489fcf90a8342219046c351acda693a9cce87639168ac582b96cb2542914caae774391cae67192890492591c482211885b0d96a359aad76934d9ed0688c05c2f188b41a090582818080301d7cbd5fb0580bc5c2dd72bb5d2cd64b45b2d55cad57ac560aa54ab156803f1fd027d3319cd0653c9ecf07a3e1dcc26031190c65d2e178be70379c4dc4e27944a04c26bfa02ff803f54aa85329d489b4f2713e9d4d3d1eef57b3cd1c9047a35f2fc7d3edf0a15128d40964aa5d329848a492893773c9daf077bc5d2ec753ad148945a310e886fb89c0e16f108884521918821e1007c3a381d0ec723c1b85c32180d05996ce663359429150ac58280201406dd6db71b43f1f1007a1c0d8cc6a341b0c8241109854280e0784192c563b1990c46130c4c27128000202 i else 403) else 0) else (if Nat.blt key 2 then (if Nat.beq key 1 then (if Nat.blt i 413 then index9 0x195cce6b3796c9e63399dcbe4a411f8ec6a43259247a471b8e48a592b94c9a5b31984aa5f27944bab95bacd5abb61b056abf57ac57ad167b2d8ad36db659ad763b25aae973b8dbaeb79bc5caef6fb85da71379acca733d9e4da77339a4ea291388c3a2b198c44a2f0f8845aa14fa6d2aa355aa53aa74ba654b017fbedeb0385c25fb077bbe60b198bc4e1b1b91c862b1f87c463a8943a0cfa8b49a450a8f3fa051a110782c0a130d8641a17038242972b85dae96eb459ad96ab24ba5932984aa71369e4fa75349248a51267b3d1e4f8773c188c26431980bc5d2f97076391c0e878371a8d066361904c24150a04430170c8682c0f070417ebe60b0178bd7fbfa03007ebe9f2fc7dbe14ca55429d48a250a8d40af572c560ad552b156a977bc1dcf278bb5eaf47bbd9e6ea74bb1d68b45231128e4823d1a87442110a864120cd66c369a4d4e57439dcce372124944b23920462410888fe80409f4fc6734194cce06fb89c2de6db75b8da219148444231047c3f200f43e1e10074381b3a1d4ec723995cb4582d964ac532a154a4d56cb59b0d76a341a6d268b3c5e30188b45c0a0682c1809038200c70389b8de4f289409c4d263198ec96431598cb6733594c26230c5629150b05026138940202000100a03 i else 404) else 0) else (if Nat.beq key 2 then (if Nat.blt i 413 then index9 0x19bcb6772b99c9663399aca64e853fa0cfa8b49a3d129143a051ae56fb8dbaeb79bbdd2f173b85da6d339acca733d9dce279379a4eb1587c4e1b1b91c7e33218bc463a552794c9a5b3197cb2612b944bab557acd5abb61afd72c15bac57a0d0382c0a130d85c2219078242a9d4ba6d2aa355a9d42a94fa654afd7bbedeb0385c1e03097fbe60acd63b2d8ad36db5da2d967b25aa3d1b8ec6a432591c82491f8e48a250f88c3a2b198bc523113884590a824321106803ea04fe7e2511c96492411482442310c843f1e9007c7a3d9dcf8793c1d4e4763a1cce06e389bc723b1b8e878381a0d46436198c05a31178b85628150b052261289d80bc60afd7cbd803f602ff7f3edf0fc7d3e54ea4542994aa350289426c349b4d66a329a0ce66733a1c6e772b91c2de71381bedc6d375b6241088c441d1007c3c1b0e2e972bb5c2dd60af58ab95af1783c9deee76a612e994b255188b452256ab45b2cd64ab562a952f679bddeaf475bb1d4e94ea71349e4fa6d26924a2451e8d48239108731988c86130164b05a2d95cac50279449cd76b365b0d56a3218ec96331428130a848220c05834140901004005e2f974b8542a94ca44d26345a6d26833d9aca6733196c36230830160c8682e0f0803810070300c0a04 i else 407) else 0))) else (if Nat.blt key 5 then (if Nat.blt key 4 then (if Nat.beq key 3 then (if Nat.blt i 413 then index9 0x195ce6533196cee6f3393c965ed165b3d8ad366b25b6d763b65aa592995c9a5b2a944c65f27984bb017dbfdeb037ebe617077bc260a411d8fc6a431e8e496471b9248aa14da7d2aa34ea6556a74baa54a71359bcca73369a4f677339e4eb1989c5e1b1b8ac46471f87c863ae971b9dbaeb72b85e6ef6fbc5dab959add5abb5aac586bf57b057a291189c3a2b12884662f0f8c45a110583c0a13068243617038642a8941a1cfa8b42a05268f3fa451972bb5c2dd74b45b2cd64b531190c260319e8f87b3c9e0ee5e2f974b89e4e27d369a4ea5d32964aa61249448a4c74391e0ec70370c86034170b04c2a120885068361a8cc640f080397ec15f2f578c0422190a83411acda6c351a4fe81401f8fa6734198caaf58ab95ab0562a952ab2b960b65a2b164e8763a9cce4532a950a44f28938a071381bcdc4d263fe02fe7ec01f4fc7cbe1f6e573ba1c8e373381c4df6f385b6dd6d3714ca852a914ea250a814649259289047118904421219108c45211043e200f0747c401f8f4381b7abdde8f37b3bde4f0773b5e2ea763a5d6d56c359b2d46bb41a4d367b4598ce65b299ac664b1d8ac8613118690472351e8b45225188744028160d048305e31180b85a0704018542c158a450050200c02000109c4c25 i else 410) else 0) else (if Nat.beq key 4 then (if Nat.blt i 413 then index9 0x198cb64f2b9ccbe6f3394cd6761b0383c0a130685c2209058642aab4ba7d2aa34ea9d42994daa54a7b339bcca73369dce269359e4ea330f89c3a2b128bc5221118c45a632795c9a5b2a97cb25129984bb0b7bbfdeb037ec1e02f97dc260a933fa1cfa8b42a3d128141a451af36fb9dbaeb72bbdd2e171bc5dac357add5abb5aafd72b159b057a4b1b8fc6a431e91c82391d9248adb63b3d8ad366b5da2c965b65ab2387c5e1b1b8ac7e331189c863a02fd7f3fe00a8522954ca771379bee07091082452110c8c200e8783e9c4f269369f4ebdde6f47abd9208d4723c723a1b8ec703c0c0642c170d33994cb663345428158a45805018117abc5f2fd82c041a090a84431a8d26c359b4fc7d401fd02663299cd0fc7c3e5f4fb5028544a37239dc6e872b9890472512496221089046dd6d36db83d1f8f8801b0e2dd72b85dae95aaf572c560562c168ae5b2c980c4613218c9c4f2894164b459ad96aa9552b15673391d4e87629150a6553c1e8ee7b3c9f0b85e2e97cde6e381c4984d4aa5d2c994c3b5e0f2773bde28945a2918d46b361b2d56b824160d0503022130905428c563b258cc800004049248a5126ec74ba9d6874433da4d3683445c2d180bc62060401c68321a8cc6c0f0704188c2618944c27 i else 402) else 0)) else (if Nat.blt key 6 then (if Nat.beq key 5 then (if Nat.blt i 413 then index9 0x19ccae772d98ca6673797c964edb6bb65aad366b1da2cb64b3d8b0b83c260b037ebde02fb7cbfdea632f984ba5b2a93cb2532895c9b238fc863b1b8ac3e331388c5e1a7b3b9e4ea733699ce26b349bccaab53aa54aa34ea5d429b4ca7d2a4b239248a431e8dc823b1c8fc6ac35fb057abb5aabd72b358add5af377bc5daeb72b7dd2e370b9dba9347a451a8b429fd128340a1cfa1b0b8642a130681c220b0483c0a33178c45a2b1287c52231089c3a02ff803f5fcfc7d3edf0f971381c2de6fb9dcae87338dc8dd6db71b4f0793bde2ed773ddeaf679bd1d8ea75ba5acd86ab65aed463b258cc862b3998cd6532da4d069b459ec46130d82bf602f17abe432110a8241a04fe803e9f8da6b361a4d46833994cca85329d48a55128d40a12311086452090896492511c90401f0fc7a200f8743c2312084441c0daed72ba5bae16cb45aac9667c3d1ecee783c990c46330184be5e2e17562af582b55cac55aa554763a1d4e473389c0dc6f2d960ae5a2c958a24f28138aa532a1489a4c4ca5d30954b27d389e4ea6936944924d223c1c8e876371c0d86835190cc2a130a044241a0c0642c170803c1c8b46225149047a351c88438b0542b140a4622f180b45c2713094160a068301201010000a030201c1006 i else 410) else 0) else (if Nat.beq key 6 then (if Nat.blt i 413 then index9 0x196cc65f3995c9e67379dcd65211048642a130682c36070b83c0a71349e4ea73369acf6673b9bccaa14caa54aa34ea6d569753a7d2a8940a451a8b42a0d267f47a1cfb017cc260b037ebee16f783bfdea5928984ba5b2a94cc64f2f95c9a29108c45a2b1288c661f1789c3ab958b057abb5aacd86af5fadd5ae970bc5daeb72b8de6df77b9dbb1988c863b1b8ac4e470f8fc5e1ad164b65aad366b2db6c76bb3d8a411c9248a431e8ec9637238fc6972b75d2ed70af56ac162ae31180c66430960ac5a2c96cae4f27140a2f2783b5e2ef7725d2a984ca59168946229b0d66a365aed564b1d8ac86304c22140a84816090683014010000978bd603057ebe4120d0a86421f4fc80409fcd26a361b4d665331a0ceb4592d56cb354aad58aa3b9e8f07b3e1e4e4733a9d8e86e379c0e25e2e17cba522a154a64c26bf603007fbf948a853a994a41221148c4321379c4e17037c3a200f879f0fc7dbe9f2a051a8942472412896491e8fc803e71b9dc8e873395b4dd6e36c42221208c361c79bddecf57a2693c9c4ea7d368d4823d1c371d0e4763c1c0a0542b160a594ce66b3196160c86034170181408ec75ba9d29249a512288438c868351b0cc5a2e180c45e251309da4cf69b45a0c461b081e10070181007 i else 402) else 0)))) else (if Nat.blt key 11 then (if Nat.blt key 9 then (if Nat.blt key 8 then (if Nat.beq key 7 then (if Nat.blt i 413 then index9 0x199cae4f2d9bcd6733192cbe763d238e48a43258dc823f248ec6ab55fac57abb61abd72b760acd5a552f944ba5b3193cb2573094c9a25178845a2b1987c52271888c3a6d3b9a4ea733d99ce26f3c9accae577b85daeb79b7dd2e778b8dbacd6bb25aad36db1da2cf6cb2d8afd83be60b0385bde02ff84bedea9d53a654aa355a5d429f54a6d2a0d0b8242a130d81c220f0c82c0a8547a051a8b499fd128748a0cfb158fc463b1b91c3e331790c4e190a8441a090c6c359a8d26d25124904725ba1cae77238dcc241188842582d15cac592d9d4e873391d8a85329155acd96ab61a8d7058341409060c05e2e168c5a6d06933da208038197cbf5eaf180c17f3fe02fd802954ca85229df2fa7e3e1f6a15128146803f9f8fa8133998ca6821114864420919bee071379c21e0f8803a3f1f0f480db6eb69b81c0dae172b75d2ed66b4592d56c9b4e279349d4fa592e954c265229249a515caf56ac162aa54aad58f47abdde6f6472411a8f773c1def276bc5148b44a31d2ea763ad0e8830988c063321e4f47b3c1dcf85d2f170be381c8ec74371e05c30190b0682413088502a331a0d464360703c204f27140a270379b8e24c268a4562a140b196cc673299a040280d8ec664b159001000084c2513b0988c3 i else 404) else 0) else (if Nat.beq key 8 then (if Nat.blt i 413 then index9 0x196cde4b3395cee733193ca66a8948a051a8b49a1d0a7f47a0cfa713c9a4ea733d9bcda673b9accae978b85daeb79b9dcadf77b8dba110c8242a130d83c1a070b82c0ab960ac57abb61add6aaf5facd5a5930944ba5b3195caa4f2f94c9b1990c463b1b91c5e2b0f8fc4e1b0184be60b0385bfdfaf783bedeaa154a654aa355a7d3a9753a6d2a29188845a2b1989c4a1f1788c3a41248e48a43258fc7a37238ec6ad16cb25aad36db3d9ac76bb2d8972ba5bae176af582b55cb14ba612a964cbc1e2f276bb9de8b46225145a2c164ac572d988c660309909e5027145b2d66bb61a8d50682c18090504c2811090558ec864b158c010100178c05eaf97ec17ec0202fe7fa914ea852a99f0fb7e3e5f4a051a8544b45aac966b655aa554ac4d2713a9e4da7de6f67bbd1ea8d47a411c9249a4528eb763a5d48843a090a8342218fa803f1fd02412291084432311c94482492c7a3f1f100d26c351acda653319cd0de70b89bee00e8803c1f71ba1cce77239442241108db4dc6eb6c361c391d4e6743b1dcf67a3c1e4f86e381bce2371d8e474381e0a0562a148b05a30170bc62321a8d06636128984e542914caa5e2e174be4c2685830190b86994cd6732d980302811a6d16933da0080301c1e0e0830d88c2 i else 407) else 0)) else (if Nat.blt key 10 then (if Nat.beq key 9 then (if Nat.blt i 413 then index9 0x19bce65f3199cd6572d92c9e531589c3e1b1b8cc4647218bc7e3ae571b7dbaeb74b85e6f173bbddafd7dbddeb0380be617097fc1e0a85419fcfa8b44a05269143a3d1a9d4da5d2aa350a6556a94fa9d4ab559abd5abb5cac586c15bafd7acd65b1d8ad368b25b6d967b5daa552993c9a5b2c944c6612b97cba6d3599cca73389a4f679379dcea0d0581c0a130882436190785c2a251187c3a2b148846631138bc5a3d1d8dc6a43208e496491f91c890a864120d0880409f4fc7f3a9d8e4733a1ecf87a3b9e0f270389b8de44229188242219289647241247e401e8f8743b1e0e46e38150ac5828148c0622d170bc6a361a0c866261389580c15e2f57cbf5d2ed72b75c2c162af56ab96ab65a2c966ab562a5546c369a4d46b34194cc672c968b6582b15cc66431180c2502893c9c542a948a65f2f170ba4d2640202fd7f3fdf6fc7c3e5f4f1793c1daee77bd9eef37a3d5d6ec74ba94ea8522954ca35028544984ca5d2a964622d128a4ea793e9c4d26d1e9046a39269449245108770b89bcdf70399cee871b91cadc6eb69b6d76c365acd46ab2192c762b199ace6532d98d16934d9ed061b1184200e8783e2410888461b0e0301a0b04828281509844240200800321a0c0582e05018101006038401e0e i else 413) else 0) else (if Nat.beq key 10 then (if Nat.blt i 413 then index9 0x198cce4b379cca6572d97cee6a331387c3a2b148c44a21118bc5aab4fa5d2aa350aa53a994da9d4ac35babd5abb5cb056ab159afd7a1b0781c0a13088641a090585c2af373b7dbaeb74bc5cae171bbddb0b7fbddeb0380c25faf97dc1e0a4b1f8dc6a43209247a391d91c8a632b93c9a5b2c984aa512997cba7b3799cca73389e4da69359dcea93439fcfa8b44a450a8141a3d1b238bc3e1b1b8cc862b1189c7e3adb67b1d8ad368b659ac965b5daa02fe7ec01fea852a914ea67bbd1e6f67aa79369c4d2753e90472351e4522108824621b89bede70b80401e0e87c763a1c0e46e3c158a852281633996ca66b3032170c05834050200d7abe5e30182bf5bae172ba5dab55caf582c564b35a2d56ca9552ad58fc7cbe1f6fa50a8146a276bc9dcf078bbd2a964ba6132894522d18ec74badd4914924d28874420d0a8243210d46c349b4d6562d160b25b2b9ccea723b1d0a4542a94cfc803ea04fe66329a0ce6030988c6642713ca0513c1ecf27a3b9f0de70371c4b85d2f17c984d241288e4b24b91d0e771b99ca221208446d46cb61acd76a8241a0b060285c30168c45ecf69b49a2d0030200e3f1e9007cdd6d371b61b0e31592c7643182212098502a00008086a331a0c86c261289d88c3610381e10 i else 403) else 0))) else (if Nat.blt key 13 then (if Nat.blt key 12 then (if Nat.beq key 11 then (if Nat.blt i 252 then index9 0x4d2653c944a249245d27938c4622a954a65371b79bcdc6e16cb679759d0f07774ba5cee7449c8e46633198cc6633198cc6633198cc4014a9948a41c8e4300c06030180c06030180c0603018b85b8f87c271386c361b0d86c361b0d86c361b0db2990c81b8dd30964b3e5228f47bedf4a14fa7deef77abd53a9b4d980c05228141b6592c934824120904824120904824120905c8e170178bce26cb659acd66b359acd66b359acd66b34ae57783c11a8d3a9d5e8e572a1d0e64323b9dcec76231148a79bc90c7a3d1e8f47a3d1e8f47a3d1e8f4cc5aad47a190cb198ca2510d800000000000000000000000000196b359a9d4ea753a9d4ea753a9d4ea7538ec76c55cae572b95cae572b95cae572b9150a8542a150a8542a150a8542a i else 42) else 0) else (if Nat.beq key 12 then (if Nat.blt i 252 then index9 0x425c0a04489392005021380a06021489c5102810124e52814080705994ea77048294ae81c060c805020241c080301c160a3600c00030d0254aa31c0d83005020241c080301c160a018080009528e078180c8140809070200c0705828061d000254a381c06010970382d2290328212e084b819220a483a122902c01806522886946581b1340a04048200c440382c1403010000c5228818a45826a880a04048200c440382c140357800b04d0382c0e03039d4160b051946c65321d41477741d4ee3c053a0c8050202410060382c146c018b000030d28c061a0ca8c6ca3510d80a04048200c07058280602008007819510140809040180e0b0500c3aaf000f032a20281012080301c160a01abc58000281012080301c160a018b00200 i else 0) else 0)) else (if Nat.blt key 14 then (if Nat.beq key 13 then (if Nat.blt i 252 then index9 0x50a753c9f4fa6d36e372388b65b2f178ae572e980c0592c988c4f37a3c9188646a350e8744a29147a3d1e8f47a3d1e8f47a3d1e8f4ca62b318cc66432196b95cae572b95cae572b95cae5723d1b0dc6e3b1d8a8542a150a8542a150a8542a1510072391f0f9f6f77bbe5f4f57aa61229a4a2512c9647a3d329249379bce16cb65b6dc6e3819acd66b359acd66b359acd66b349e5226954aa4e28140824120904824120904824120904a65372b95d2e9773b9d6f07839dceec761d4ea64321e0e4723c9d0ee6633198cc6633198cc6633198cca65128970b359a9148b55aadd4ea753a9d4ea753a9d4ea753a9c30190c80000000000000000000000000009c4e2906030180c06030180c06030180c0d86c361b0d86c361b0d86c361b i else 27) else 0) else (if Nat.beq key 14 then (if Nat.blt i 252 then index9 0x42440a064b9612005031600a0403148b04d0281806581b0140c0a05ba0ea640181c6c651c0f0ee050300c58080202816073602400095100c6ca31c29478050300c580802028160704abc00031b0e0303c0c8140c0316020080a0581c12010000c6c381c0f010910502d2e90740212208488112e07481952e9027010125226a89464e529440a060182008440502c0e0957800085226810a44e288680a060182008440502c0e09010009c510502c1409051d4160b03ba14ae83b9d40e64329d4c81803994ee050300c10040502c0e6c0483800095128c12a20ca8d4aa30d2940a0601820080a0581c12af0e80030190d0140c0304010140b03824020200060321a028180608020281607048081c00028180608020281607048383a00 i else 0) else 0))))) else (if Nat.blt key 23 then (if Nat.blt key 19 then (if Nat.blt key 17 then (if Nat.blt key 16 then (if Nat.beq key 15 then (if Nat.blt i 252 then index9 0x4c245f2964b23d1eeb3c9d1cae53a9d4c8647a2351a8743bc1e04f2e938a44d30180b2596d940a0412090482412090482412090482a60c100723952290520c06030180c06030180c06030183d1b28944190c8000000000000000000000000003318cc65aad534944a2793292492853afb7bbdd3e9f4da6df4f57aba5d278391c912e7739dccc6633198cc6633198cc6633199e68c433b9dcf245228f47a3d1e8f47a3d1e8f47a3d1e9d8ec2d96dbcde2a955c66231371b85329978bc572bb85b2d972389c0cd66b359acd66b359acd66b359aca1b8dd702713b21903e1f2dc361b0d86c361b0d86c361b0d86d8a3b1d8a8542a150a8542a150a8542a152cd66cb5cae572b95cae572b95cae572b953a9d4ea753a9d4ea753a9d4ea7 i else 167) else 0) else (if Nat.beq key 16 then (if Nat.blt i 252 then index9 0x424416074b995200b03994160a039d4ca640581c06651b02c0e0402938a44d018186c5851868a20b0380c0408050100a062202400090c00c6c3851a94340b0380c0408050100a060483800031b28d441a0c82c0e030102014040281812010000c6ca3518681091020152e90270212208488292e06481612e907402812753206070e8529dc160701820146c020140c0907000147532028eae83b8f0160701820146c020140c0916001d077020140809021480a05031394a4e289480c4d2c1489aa203160a20b0380c100a020140c4404abc00090c0e012180c8e14a381e294160701820140402818120e0e80144191e02c0e0304028080503024022c00288323c0581c0608050100a06048b15e000581c0608050100a0604abc3a00 i else 0) else 0)) else (if Nat.blt key 18 then (if Nat.beq key 17 then (if Nat.blt i 252 then index9 0x50a307a5e2f0ec76cc7232d1a8d4fa7d148a20188c43e1f180c0f3653153a862d96c6e371b15cae2a150a8542a150a8542a150a854f47938d90c863319c4b95cae572b95cae572b95cae5729e44a1d0e9b4d9e8f47a3d1e8f47a3d1e8f47a3d17472392c965f6ee772e1c2b359a68f0983a9d4aa551389ca4190cbc1e0fa763b16eb55ab814ea753a9d4ea753a9d4ea753a9cf2993ba592c292994c361b0d86c361b0d86c361b0d86ca05074ba5cae57bbdd4cde6f28944d96ca51287239244c864278609a000000000000000000000000000eb73b9df2f57aa9148dc6e36d9acd66b359acd66b359acd66b34e89249198cc6633198cc6633198cc663323d1e4e06030180c06030180c06030180c209048241209048241209048241 i else 65) else 0) else (if Nat.beq key 18 then (if Nat.blt i 252 then index9 0x41d40606290f03203030f006070325c7877018180a3c1c00c0c0a04a8922640281070181b1609a030301458080382812040082c000b7401470a51b28cb00303014580803828120405abc00051c0d8ca584800c0c05160200e0a04810166c0001470361b160107505024a41951020ea083a81ca4040c860a4190d01c16973bba14a1a519440606028200e1d05024080b578000e973b81d2e1a289380606028200e1d05024080b07000345105024140b0524412090228946a226a4408640c244c865020609a0303014100705024080105808000b7429416e84829546a52728c0606028200e0a0481016af22000ca902700c0c050401c14090202cd80e00195204e018180a08038281204058380400018180a08038281204058088800 i else 0) else 0))) else (if Nat.blt key 21 then (if Nat.blt key 20 then (if Nat.beq key 19 then (if Nat.blt i 252 then index9 0x4c1487a753a86432403c8a4c0604b258a050663c1e0b55aa351a4f53061224d72b9544a21b190c80000000000000000000000000005d273ad48a41c8e4e80c06030180c06030180c0603018f96d964b28f47904824120904824120904824120bd18cc643a1d34552aae0f02713bedc2a12f179dcee59acd183b1d988c4992994d6e3e1f1dc361b0d86c361b0d86c361b0d86dc8fa7027d3ecb763b14ea753a9d4ea753a9d4ea753a9d148a6f378b65b4a25194e9748dc6e72393ddeed96ca74ae5779b150c2a150a8542a150a8542a150a854e36e3713c924932190e773a24cc6633198cc6633198cc6633199c4f57ab359acd66b359acd66b359acd66a6d36f25cae572b95cae572b95cae572b93d1e8f47a3d1e8f47a3d1e8f47a i else 122) else 0) else (if Nat.beq key 20 then (if Nat.blt i 252 then index9 0x414806073a868320303868060603a5c34510181c161a5180c0e0404861224d0582946a21b194c8030382c040803010120a0081400052702d46a51b0e0ca030382c040803010120a02838000b518d8b0654800c0e0b010200c04048280a440002d46361b194105202024ea190c020a40829018ea0a0ca88ea191e0180a97289394a3c1c1dc0607058200c1d020241405070000c97288192e3c3bba00607058200c1d02024140557800787702024080502244120905060701832244144d512449a5805288c8030382c1006020241401028b00005272940a4e4829470a5740e00607058200c04048280a0e36000b0907400c0e0b0401808090501488af0016120e80181c160803010120a02abc58000181c160803010120a028b0d800 i else 0) else 0)) else (if Nat.blt key 22 then (if Nat.beq key 21 then (if Nat.blt i 252 then index9 0x7db8570ee772cd66ca79b15bcde7bbddb2d953395caa2513a5d2e46632df4e0783c16ab55bbb1d8a753a9d4ea753a9d4ea753a9d4ee3713d18cc664321e4b95cae572b95cae572b95cae572f96db71b8f57ab359acd66b359acd66b359acd66bad48a473b9d425e2f0f5183b1da60a49a2a954ea750c864f0271396cb69d2b95c6c371ba18542a150a8542a150a8542a150a89e9126a51281832190000000000000000000000000000e47230180c4624fa7c808d468f87c8a452592c5028264a6533c8a4ee1b0d86c361b0d86c361b0d86c365d2c9653c9b4d8e4728743a24f47a3d1e8f47a3d1e8f47a3d1e89c8f47904824120904824120904824120a49247406030180c06030180c06030180c33198cc6633198cc6633198cc66 i else 102) else 0) else (if Nat.beq key 22 then (if Nat.blt i 252 then index9 0x4148120a3aa88320905288120405245444d0482816a2518241406018f12e510581d461a52ba0ee090502d5e080201806070e81400052c02d4636528e1d0090502d5e08020180607028b0000b51a949ce848024140b5782008060181c0a440002d46a552ba010520300cea191e020a40829010ea070c868ea190c0100a91269606c181c190120a0582008010300c0e0516000089126811221832194120a0582008010300c0e050100030640300c0c050325c0603038f0703c3ba5c0e510d25ca24e03868ee090502c10040300c0e1d0283800052c0d80a58480d87036328e0120a0582008060181c0a2c360009c9032824140b040100c03038148802001392065048281608020180607028081c0004828160802018060702838d800 i else 0) else 0)))) else (if Nat.blt key 27 then (if Nat.blt key 25 then (if Nat.blt key 24 then (if Nat.beq key 23 then (if Nat.blt i 252 then index9 0x4d1e170552a89c4ea627861d2e94a250e4726516cb6371bb79bc79200a53277311887c3e5b94ca61b0d86c361b0d86c361b0d86c36eb3a1747239522909c0c06030180c06030180c06030189e44b9dce9249198cc6633198cc6633198cc663338d90c86e37130753a8f4a4190ca8518fb773b8bc5e1d8edc2b359b95ca91321906ca251134000000000000000000000000001e69d433ddeec52b95c542a150a8542a150a8542a150a9b2d946a35e0f04b2599860302d56a502827d3e8a453e9d8ec7232dc0a753a9d4ea753a9d4ea753a9d4ef443a1df28f47b198c592cb6c824120904824120904824120905e49b4d9e8f47a3d1e8f47a3d1e8f47a3d3d5eae25cae572b95cae572b95cae572b966b359acd66b359acd66b359acd i else 205) else 0) else (if Nat.beq key 24 then (if Nat.blt i 252 then index9 0x41d4120429060320902060120a022443064048100a181c0240807018692e7702818703c52938a209020141c080501c06060e82c000b32814703652a8c9c09020141c080501c06060580800051c295d04e48024080507020140701818166c0001470a55293810750380ca4190d020ea083a828a4060c8f0a419510281691321946ca25193412040282014010380c0c0b0100014913202922a22696012040282014010380c0c0b16001444d0380c0e0b03a5c060303069461a28a5c0c771e25ceee8030f0a20902014100a0380c0c1d05abc000b328d81665480d946362c28c120402820140701818160222001d0902c0240805040280e030302cd82c003a12058048100a080501c0606058b15e00048100a080501c060605abc8800 i else 0) else 0)) else (if Nat.blt key 26 then (if Nat.beq key 25 then (if Nat.blt i 232 then index9 0x80741a020f270982e220288219010140a0514a703e0f020144400172083a1e0fa409813170542417012200e17428401e82051f4fe0d3e888260402818ee15220882000008080a9c09018144403810041e0f0781e9c110a4321e0f8740c820001444ca090bc0c152606c04882086d7e1014a0888b75c8056e1f178643c2e3b854141f0807c14150f0a03619008345e2e0a8140a05148a03a0f0301400220c8383e1e0e87036070c8082e120a8502612088401e0e06824160a048000e06028100602008002022220540a280b8101a01098182a1e0f0781e28000a45c1e0e87c080e1101400560b90408020d9302a1417930961014838024322910861d208b83c19018081a1d i else 29) else 0) else (if Nat.beq key 26 then (if Nat.blt i 232 then index9 0xc0d410351a8202a151582c08000e81c0c09018003a090502816070e00d2492058241c030d0600e1c040390e0405000560a0e8683a0e0e0542e2b020143400000003035040d46a080a854ca050e800081720070060002070140a0285c1203663300a1c0700c34180b824100e43874140032828081a020381215039943a0b0d00000000c0d42a351a8541008030740a000585c561c0d000161c070383a17048683c1e0e870141a018602e090a8282605070000c0e0580c160a048200e060281006000000030350a8d46a15040208004058000a07328243400028241c0e0201c381a2c1600809050680618038702a0a0982c1c00200380a030282838080b900161d018000000 i else 0) else 0))) else (if Nat.blt key 29 then (if Nat.blt key 28 then (if Nat.beq key 27 then (if Nat.blt i 232 then index9 0x80888815028a02e040680426060a8783c1e078a00029170783a1f020384405001582e4102008364c0a8505e4c25840520e0090c8a4421874822e0f064060206874201f050543c280d864020d178b82a050281452280e83c0c0500088320e0f8783a1c0d81c32020b8482a14098482210078381a09058281200038180a0401808020008000020202a702406051100e04010783c1e07a7044290c8783e1d03208000511328242f03054981b01220821b5f8405282222dd72015b87c5e190f0b8ee150507c201d068083c9c260b8880a20864040502814529c0f83c0805110005c820e8783e902604c5c150905c04880385d0a1007a08147d3f834fa22098100a063b8548822 i else 34) else 0) else (if Nat.beq key 28 then (if Nat.blt i 232 then index9 0xc0d42a351a85410082001016000281cca090d0000a090703808070e068b05802024141a018600e1c0a828260b07000800e0280c0a0a0e0202e400587406000000030350a8d46a15040200c1d028001617158703400058701c0e0e85c121a0f0783a1c0506806180b8242a0a098141c00030381603058281208038180a040180000000c0d410351a8202a15328143a000205c801c01800081c050280a170480d98cc028701c030d0602e09040390e1d05000ca0a02068080e048540e650e82c3400000003035040d46a080a854560b020003a070302406000e824140a0581c38034924816090700c341803870100e438101400158283a1a0e83838150b8ac08050d0000000 i else 0) else 0)) else (if Nat.blt key 30 then (if Nat.beq key 29 then (if Nat.blt i 232 then index9 0x807c14150f0a03619008345e2e0a8140a05148a03a0f0301400220c8383e1e0e87036070c8082e120a8502612088401e0e06824160a048000e06028100602008002022220540a280b8101a01098182a1e0f0781e28000a45c1e0e87c080e1101400560b90408020d9302a1417930961014838024322910861d208b83c19018081a1d080741a020f270982e220288219010140a0514a703e0f020144400172083a1e0fa409813170542417012200e17428401e82051f4fe0d3e888260402818ee15220882000008080a9c09018144403810041e0f0781e9c110a4321e0f8740c820001444ca090bc0c152606c04882086d7e1014a0888b75c8056e1f178643c2e3b854141f i else 31) else 0) else (if Nat.beq key 30 then (if Nat.blt i 232 then index9 0xc0d42a351a8541008030740a000585c561c0d000161c070383a17048683c1e0e870141a018602e090a8282605070000c0e0580c160a048200e060281006000000030350a8d46a15040208004058000a07328243400028241c0e0201c381a2c1600809050680618038702a0a0982c1c00200380a030282838080b900161d0180000000c0d410351a8202a151582c08000e81c0c09018003a090502816070e00d2492058241c030d0600e1c040390e0405000560a0e8683a0e0e0542e2b020143400000003035040d46a080a854ca050e800081720070060002070140a0285c1203663300a1c0700c34180b824100e43874140032828081a020381215039943a0b0d0000000 i else 0) else 0))))))

def readLiteral (i : Nat) : Sig := (literalPos i,literalNeg i)
def forward (g : Nat) : SigHom :=
  let keys := groupKeyIds g
  pairHom (fun j => Fin.ofNat 414 (moveIndex (keys &&& 127) j.val))
    (fun j => Fin.ofNat 414 (moveIndex (keys >>> 7) j.val))
def backward (g : Nat) : SigHom := forward (inverseGroup g)
def ruleCode (g i : Nat) : Nat := sourceCode (g*26+i)
def movedLiteral (g i : Nat) : Sig :=
  let n := ruleCode g i - 1
  let a := readLiteral (n / 2)
  if Nat.beq (n % 2) 0 then a else neg a
def supportedLiteral (g i : Nat) : Bool :=
  Nat.blt g 22 && Nat.blt i 26 && !(Nat.beq (ruleCode g i) 0)
def sourceChecked (g i : Nat) : Bool :=
  if Nat.beq (ruleCode g i) 0 then true else
    sigEq ((forward g).fn (readLiteral i)) (movedLiteral g i) &&
    sigEq ((backward g).fn (movedLiteral g i)) (readLiteral i)
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma seed_0 : span (sourceChecked 0) 26 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma seed_1 : span (sourceChecked 1) 26 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma seed_2 : span (sourceChecked 2) 26 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma seed_3 : span (sourceChecked 3) 26 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma seed_4 : span (sourceChecked 4) 26 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma seed_5 : span (sourceChecked 5) 26 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma seed_6 : span (sourceChecked 6) 26 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma seed_7 : span (sourceChecked 7) 26 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma seed_8 : span (sourceChecked 8) 26 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma seed_9 : span (sourceChecked 9) 26 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma seed_10 : span (sourceChecked 10) 26 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma seed_11 : span (sourceChecked 11) 26 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma seed_12 : span (sourceChecked 12) 26 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma seed_13 : span (sourceChecked 13) 26 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma seed_14 : span (sourceChecked 14) 26 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma seed_15 : span (sourceChecked 15) 26 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma seed_16 : span (sourceChecked 16) 26 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma seed_17 : span (sourceChecked 17) 26 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma seed_18 : span (sourceChecked 18) 26 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma seed_19 : span (sourceChecked 19) 26 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma seed_20 : span (sourceChecked 20) 26 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma seed_21 : span (sourceChecked 21) 26 0 = true := by decide +kernel
lemma seeds (g : Nat) (hg : g < 22) : span (sourceChecked g) 26 0 = true := by
  interval_cases g
  · exact seed_0
  · exact seed_1
  · exact seed_2
  · exact seed_3
  · exact seed_4
  · exact seed_5
  · exact seed_6
  · exact seed_7
  · exact seed_8
  · exact seed_9
  · exact seed_10
  · exact seed_11
  · exact seed_12
  · exact seed_13
  · exact seed_14
  · exact seed_15
  · exact seed_16
  · exact seed_17
  · exact seed_18
  · exact seed_19
  · exact seed_20
  · exact seed_21

lemma sourceCorrect {g i : Nat} (hs : supportedLiteral g i = true) :
    (forward g).fn (readLiteral i) = movedLiteral g i ∧
      (backward g).fn (movedLiteral g i) = readLiteral i := by
  simp only [supportedLiteral,Bool.and_eq_true,Nat.blt_eq,Bool.not_eq_true'] at hs
  have c := span_ok (seeds g hs.1.1) i (Nat.zero_le _) (by simpa only [Nat.zero_add] using hs.1.2)
  simp only [sourceChecked,hs.2,Bool.false_eq_true,ite_false,Bool.and_eq_true] at c
  exact ⟨sigEq_iff.mp c.1,sigEq_iff.mp c.2⟩
lemma maskedValid (a : Nat) : Valid1 (a &&& top) := by
  intro j hj
  rw [Nat.testBit_and,testBit_top]
  simp [show ¬ j < 414 by omega]
lemma readValid (i : Nat) : Valid (readLiteral i) := ⟨maskedValid _,maskedValid _⟩
lemma movedValid (g i : Nat) : Valid (movedLiteral g i) := by
  dsimp only [movedLiteral]
  split
  · exact readValid _
  · exact valid_neg (readValid _)

def op (i : Nat) : Nat := gateRecipe i &&& 3
def argA (i : Nat) : Nat := (gateRecipe i >>> 2) &&& 1023
def argB (i : Nat) : Nat := gateRecipe i >>> 12
def seedId (i : Nat) : Nat := gateRecipe i >>> 2
def evalSignal (lit : Nat → Sig) : Nat → Nat → Sig
  | 0, i => lit (seedId i)
  | fuel+1, i =>
    match op i with
    | 0 => lit (seedId i)
    | 1 => neg (evalSignal lit fuel (argA i))
    | 2 => bin false (evalSignal lit fuel (argA i)) (evalSignal lit fuel (argB i))
    | _+3 => bin true (evalSignal lit fuel (argA i)) (evalSignal lit fuel (argB i))
def supported (g : Nat) : Nat → Nat → Bool
  | 0, i => supportedLiteral g (seedId i)
  | fuel+1, i =>
    match op i with
    | 0 => supportedLiteral g (seedId i)
    | 1 => supported g fuel (argA i)
    | _+2 => supported g fuel (argA i) && supported g fuel (argB i)
lemma evalValid (lit : Nat → Sig) (hv : ∀ j, Valid (lit j)) (fuel i : Nat) :
    Valid (evalSignal lit fuel i) := by
  induction fuel generalizing i with
  | zero => exact hv _
  | succ fuel ih =>
    rcases e : op i with _ | _ | _ | n <;> simp only [evalSignal,e]
    · exact hv _
    · exact valid_neg (ih _)
    · exact valid_bin (ih _) (ih _)
    · exact valid_bin (ih _) (ih _)
lemma evalMove (g fuel i : Nat) (hs : supported g fuel i = true) :
    (forward g).fn (evalSignal readLiteral fuel i) = evalSignal (movedLiteral g) fuel i ∧
    (backward g).fn (evalSignal (movedLiteral g) fuel i) = evalSignal readLiteral fuel i := by
  induction fuel generalizing i with
  | zero => exact sourceCorrect hs
  | succ fuel ih =>
    rcases e : op i with _ | _ | _ | n <;> simp only [evalSignal,supported,e,Bool.and_eq_true] at hs ⊢
    · exact sourceCorrect hs
    · obtain ⟨a,b⟩ := ih _ hs
      rw [(forward g).hneg (evalValid _ readValid _ _),(backward g).hneg (evalValid _ (movedValid g) _ _),a,b]
      simp
    · obtain ⟨a,b⟩ := ih _ hs.1
      obtain ⟨c,d⟩ := ih _ hs.2
      rw [(forward g).hbin,(backward g).hbin,a,b,c,d]
      simp
    · obtain ⟨a,b⟩ := ih _ hs.1
      obtain ⟨c,d⟩ := ih _ hs.2
      rw [(forward g).hbin,(backward g).hbin,a,b,c,d]
      simp

def readShape : Nat → Nat → List Nat
  | 0, _ => []
  | n+1, bits => (bits &&& 4095) :: readShape n (bits >>> 12)
def wire (lit : Nat → Sig) (u : Nat) : Wire :=
  (evalSignal lit 5 (u >>> 2),tagOfNat (u &&& 3))
def coversCode (g : Nat) (u : Nat) : Bool := supported g 5 (u >>> 2)

lemma moveShape (l : List Nat) (g : Nat) (hs : l.all (coversCode g) = true) :
    l.map (wire (movedLiteral g)) = (l.map (wire readLiteral)).map (fun x => ((forward g).fn x.1,x.2)) ∧
    ∀ a ∈ sigsOf (l.map (wire readLiteral)), Reversible (forward g) (backward g) a := by
  constructor
  · rw [List.map_map]
    apply List.map_congr_left
    intro u hu
    exact Prod.ext (evalMove g _ _ (List.all_eq_true.mp hs u hu)).1.symm rfl
  · intro a ha
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp ha
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hx
    obtain ⟨a,b⟩ := evalMove g _ _ (List.all_eq_true.mp hs u hu)
    exact ⟨evalValid _ readValid _ _,(congrArg (backward g).fn a).trans b⟩
def shapeChunk (k j : Nat) : Nat := (if Nat.blt k 97 then (if Nat.blt k 82 then (if Nat.blt k 73 then (if Nat.blt k 65 then (if Nat.blt k 64 then (if Nat.beq k 56 then 0x8707c473867c67066c66470007907386a067c67066c66470008ac8a467c67867066c66470007387206f46ec67066866470008a488867c67867066866470007847386a067066c66866470008787c467c67066c66866470007a078467867066c668664777c77872067867066c6686648 else 0) else (if Nat.beq k 64 then (if j < 3 then (if j < 1 then 0x8e473869067c67867066c668664977c73869067c67867066c668664975c73869067c67867066c668664900073869067c67867066c668664873872069067c67867066c66866497386d069067c67867066c66866497386a069067c67867066c668664900090068867c67867066c668664885473868867c67867066c668664985073868867c67867066c668664900073868867c67867066c668664873872068867c67867066c66866497386d068867c67867066c66866497386b068867c67867066c668664973869068867c67867066c668664900073868467c67867066c6686648 else (if j < 2 then 0x7fc72067c67867066c668664881073872067c67867066c66866497f473872067c67867066c668664979073872067c67867066c668664977c73872067c67867066c668664900073872067c67867066c668664877873870467c67867066c66866497387206dc67c67867066c66866490009386d067c67867066c66866480008a46bc67c67867066c66866480007dc6b067c67867066c668664877c7386ac67c67867066c66866490007386ac67c67867066c66866487386cc6ac67c67867066c668664900087c6a067c67867066c66866480008f469067c67867066c6686648 else 0x80473867c67867066c66866480007f873867c67867066c66866480007f473867c67867066c66866480007d073867c67867066c66866480007cc73867c67867066c66866480007bc73867c67867066c66866480007b873867c67867066c66866480007b073867c67867066c66866480007ac73867c67867066c66866480007a473867c67867066c668664800079073867c67867066c668664800078873867c67867066c668664800078473867c67867066c668664800074873867c67867066c668664800074473867c67867066c668664800000073867c67867066c6686647)) else (if j < 4 then 0x7dc67c67867066c668664700077c77867c67867066c668664800077c76867c67867066c668664800077c75c67c67867066c668664800077875867c67867066c668664800076875867c67867066c668664800075c75867c67867066c668664800089073867c67867066c668664800087c73867c67867066c668664800086c73867c67867066c668664800086873867c67867066c668664800086473867c67867066c668664800086073867c67867066c668664800081873867c67867066c668664800081073867c67867066c668664800080873867c67867066c6686648 else (if j < 5 then 0x7f473867c67867066866470000007b873867c67867066866470000007ac73867c67867066866470007f473872067c67867066866480007687386dc67c67867066866480007386f46dc67c678670668664800084473869067c67867066866480007386f468867c67867066866480007386b068867c678670668664800000093867c67867066c668664700000091867c67867066c668664700000090067c67867066c66866470000008f467c67867066c66866470000008a467c67867066c668664700000087c67c67867066c66866470000007fc67c67867066c6686647 else 0x86473867c67867066c664700000085473867c67867066c664700000079073867c67867066c664700079073872067c67867066c66480007607386bc67c67867066c66480008e873869067c67867066c664800085473868867c67867066c664800000080873867c6786706686647))) else 0)) else (if Nat.blt k 72 then (if Nat.beq k 65 then 0x8a473067c67867066866477b867c67867467066866477c467c67467066c668664778467867467066c6686647 else 0) else (if Nat.beq k 72 then (if j < 2 then (if j < 1 then 0x64c3a039c39a39038e38838438290006403a039c39a39038e38838438290006383a039c39a39038e38838438290006303a039c39a39038e38838438296625c83a039c39a39038e388384382a6625883a039c39a39038e388384382a65c50c3a039c39a39038e388384382a65c5083a039c39a39038e388384382a6624983a039c39a39038e388384382a6624643a039c39a39038e388384382a66243c3a039c39a39038e388384382a6304243a039c39a39038e388384382a6624183a039c39a39038e388384382a6404183a039c39a39038e388384382a65c40c3a039c39a39038e388384382a6383c83a039c39a39038e388384382a else 0x6624284243a039a39038e388384382a66254c4183a039a39038e388384382a6624283c83a039a39038e388384382a00066258839c39a39038e388384382900064c55439c39a39038e388384382900065c50c39c39a39038e388384382900065c50839c39a39038e388384382900066246439c39a39038e388384382900066244c39c39a39038e388384382900066243439c39a39038e388384382966243c41839c39a39038e388384382a66242441839c39a39038e388384382a00064c3b439c39a39038e38838438290006383b439c39a39038e388384382900042c3b439c39a39038e38838438290006623a039c39a39038e3883843829) else (if j < 3 then 0x7386ac67c67867066c66866480000007386a867c67867066c668664800000073869467c67867066c668664800000073869067c67867066c668664800000073868c67c67867066c668664800000073868867c67867066c668664800000073868467c67867066c668664800000073868067c67867066c668664800000073867c67867467066c668664800000063849039c39a390388384382800000065c41439c39a390388384382800000065c42039c39038e388384382800066246442839a39038e38838438290006624283c839a39038e388384382900066254c3a039a39038e38838438296624644283a039a39038e388384382a else 0x73867c67867066c668664700000073873067c67867066c668664800000073872867c67867066c668664800000073872467c67867066c668664800000073872067c67867066c668664800000073870c67c67867066c668664800000073870867c67867066c668664800000073870467c67867066c668664800000073870067c67867066c66866480000007386dc67c67867066c66866480000007386d867c67867066c6686648)) else 0))) else (if Nat.blt k 75 then (if Nat.blt k 74 then (if Nat.beq k 73 then (if j < 3 then (if j < 1 then 0x6b867c67867467066c66866486b467c67867467066c66866486b067c67867467066c66866486ac67c67867467066c66866486a867c67867467066c66866486a467c67867467066c66866486a067c67867467066c668664869c67c67867467066c668664869867c67867467066c668664869467c67867467066c668664869067c67867467066c668664868c67c67867467066c668664868867c67867467066c668664868467c67867467066c668664868067c67867467066c668664800067c67867467066c6686647 else (if j < 2 then 0x6f867c67867467066c66866486f467c67867467066c66866486f067c67867467066c66866486ec67c67867467066c66866486e867c67867467066c66866486e467c67867467066c66866486e067c67867467066c66866486dc67c67867467066c66866486d867c67867467066c66866486d467c67867467066c66866486d067c67867467066c66866486cc67c67867467066c66866486c867c67867467066c66866486c467c67867467066c66866486c067c67867467066c66866486bc67c67867467066c6686648 else 0x73867c67867467066c668664873467c67867467066c668664873067c67867467066c668664872c67c67867467066c668664872867c67867467066c668664872467c67867467066c668664872067c67867467066c668664871c67c67867467066c668664871867c67867467066c668664871467c67867467066c668664871067c67867467066c668664870c67c67867467066c668664870867c67867467066c668664870467c67867467066c668664870067c67867467066c66866486fc67c67867467066c6686648)) else (if j < 4 then 0x73870467c67867066c668664873870067c67867066c66866487386dc67c67867066c66866487386d867c67867066c66866487386ac67c67867066c66866487386a867c67867066c668664873869467c67867066c668664873869067c67867066c668664873868c67c67867066c668664873868867c67867066c668664873868467c67867066c668664873868067c67867066c668664800073c67c67467066c668664700074067867467066c668664774067c67867467066c668664873c67c67867467066c6686648 else (if j < 5 then 0x7387306ac67c67867066866487387306a867c678670668664873873069467c678670668664873873069067c678670668664873873068467c678670668664873873068067c678670668664873873067c678674670668664800073067c678674670668664700074073c73867066c668664700073867c67867066c668664773873067c67867066c668664873872867c67867066c668664873872467c67867066c668664873872067c67867066c668664873870c67c67867066c668664873870867c67867066c6686648 else 0x73873072c67c678670664700073c73872c67c67066c664700073872c67c67867066c664700072c67c67867467066c664794c73873067c678670668664894873873067c678670668664890873873067c678670668664881473873067c678670668664800073873067c678670668664773873072867c678670668664873873072467c678670668664873873072067c678670668664873873070c67c678670668664873873070867c678670668664873873070467c678670668664873873070067c6786706686648))) else 0) else (if Nat.beq k 74 then 0x73873072067c678670668664873873069067c678670668664873872067c67867066c668664873870867c67867066c66866487386ac67c67867066c66866487386a867c67867066c668664873869067c67867066c668664873868867c67867066c668664873868467c67867066c668664872067c67867467066c66866486d067c67867467066c66866486b067c67867467066c66866486a067c67867467066c668664869067c67867467066c668664868867c67867467066c6686648 else 0)) else (if Nat.blt k 80 then (if Nat.beq k 75 then 0x73873072c67c678670664773c73872c67c67066c664773872c67c67867066c664772c67c67867467066c664773873067c678670668664773067c678674670668664774073c73867066c668664773867c67867066c668664773c67c67467066c668664774067867467066c668664767c67867467066c6686647 else 0) else (if Nat.blt k 81 then (if Nat.beq k 80 then (if j < 2 then (if j < 1 then 0x6623d83a039c39a39038e388384382a0006623d03a039c39a39038e388384382a0006623cc3a039c39a39038e388384382a0006623c83a039c39a39038e388384382a0006623ac3a039c39a39038e388384382a0006623a83a039c39a39038e388384382a0006623a43a039c39a39038e388384382a37e0b409402201e01a01600e00a006002b00037e13405c01e01a01600e00a006001a00037e37006402201a01600d00a005001a00000037e36402101a01600d00a005001900037e3642fc02101a01600d00a005001a00037e36411402101a01600d00a005001a00037e2fc06402101a01600d00a005001a37e3642fc06402101a01600d00a005001b00037e1e802201e01a01600e009005001a else 0x6624783a839c39a39038e388384382a0006624183a839c39a39038e388384382a0006623d43a839c39a39038e388384382a0006623d03a839c39a39038e388384382a0006623c43a839c39a39038e388384382a0006623c03a839c39a39038e388384382a0006623b43a839c39a39038e388384382a0006623b03a839c39a39038e388384382a0006623ac3a839c39a39038e388384382a0006623f83a439c39a39038e388384382a0006623d03a439c39a39038e388384382a0006623ac3a439c39a39038e388384382a00000065c3a039c39a39038e388384382900066241c3a039c39a39038e388384382a0006624183a039c39a39038e388384382a00066240c3a039c39a39038e388384382a) else (if j < 3 then 0x6623e839c39a39038e38838438290000006623e439c39a39038e38838438290000006623e039c39a39038e38838438290000006623d039c39a39038e388384382900066260c3d039c39a39038e388384382a0006625e43d039c39a39038e388384382a0006623d83d039c39a39038e388384382a0006623d43d039c39a39038e388384382a00000064c3b839c39a39038e38838438290006624ec3ac39c39a39038e388384382a0006624a43ac39c39a39038e388384382a0006623d43ac39c39a39038e388384382a0006623d03ac39c39a39038e388384382a0006623c43ac39c39a39038e388384382a0006623b43ac39c39a39038e388384382a0006624f43a839c39a39038e388384382a else (if j < 4 then 0x6623c43b439a39038e38838438290000006624283a039a39038e388384382900000000066239c39a39038e388384382800000000064c39c39a39038e388384382800000000063839c39a39038e38838438280000006625c039c39a39038e38838438290000006625bc39c39a39038e38838438290000006625b039c39a39038e38838438290000006625ac39c39a39038e388384382900000066243839c39a39038e388384382900000066241c39c39a39038e388384382900000066241839c39a39038e388384382900000066240c39c39a39038e388384382900000066240839c39a39038e38838438290000006623fc39c39a39038e38838438290000006623f839c39a39038e3883843829 else 0x73873067c678670668664700000000000073867c67867066c668664700000000000067c67867467066c668664700000000066242839a39038e3883843828))) else 0) else (if Nat.beq k 81 then (if j < 2 then (if j < 1 then 0x6623a83a039c39a39038e388384382a00000044439c39739038e388384382800000042039c39739038e38838438280004203a039c39739038e38838438290003dc3c839a39739038e38838438290004283a039a39739038e38838438290003dc3a039a39739038e388384382900040c39c39a39739038e38838438294243a039c39a39739038e388384382a4183a039c39a39739038e388384382a40c3a039c39a39739038e388384382a3c83a039c39a39739038e388384382a3c03a039c39a39739038e388384382a3b43a039c39a39739038e388384382a3b03a039c39a39739038e388384382a3a83a039c39a39739038e388384382a else 0x6623fc39c39a39038e38838438290006623f839c39a39038e38838438290000003f439c39a39038e38838438280006623e439c39a39038e38838438290006623e039c39a39038e38838438290006623d039c39a39038e388384382900064c3b839c39a39038e38838438290003f43b439c39a39038e38838438296624183a839c39a39038e388384382a00065c3a039c39a39038e388384382966241c3a039c39a39038e388384382a6624183a039c39a39038e388384382a66240c3a039c39a39038e388384382a6623cc3a039c39a39038e388384382a6623c83a039c39a39038e388384382a6623ac3a039c39a39038e388384382a) else (if j < 3 then 0x6623dc3b039a39038e38838438290006623dc3a839a39038e38838438290006624283a039a39038e38838438290006623dc3a039a39038e388384382900000066239c39a39038e388384382800000064c39c39a39038e388384382800000063839c39a39038e38838438280006625c039c39a39038e38838438290006625bc39c39a39038e38838438290006625b039c39a39038e38838438290006625ac39c39a39038e388384382900066243839c39a39038e388384382900066241c39c39a39038e388384382900066241839c39a39038e388384382900066240c39c39a39038e388384382900066240839c39a39038e3883843829 else (if j < 4 then 0x4fc39c39a397390388384382800000049039c39a397390388384382800000041439c39a39739038838438280004903c839c39a39739038838438290004143a039c39a39739038838438290000006623cc3c839a38e38838438280000003cc3c839a39738e388384382800000041c39c39a39738e388384382800041c3a039c39a39738e38838438290003d83a039c39a39738e388384382900000066242839a39038e38838438280006625ac3dc39a39038e38838438290006623dc3c839a39038e38838438290006623cc3c839a39038e38838438290006623dc3b439a39038e38838438290006623c43b439a39038e3883843829 else 0x73873067c678670668664700000000073867c67867066c668664700000000067c67867467066c66866470000003b43b039a39739038e38838280000006623c43c039a39038e38438280000003c43c039a39739038e3843828))) else 0))))) else (if Nat.blt k 89 then (if Nat.blt k 84 then (if Nat.blt k 83 then (if Nat.beq k 82 then (if j < 1 then 0x6623cc3c839a38e38838438280003cc3c839a39738e38838438283d83c839c39a39738e388384382941c3a039c39a39738e38838438293d83a039c39a39738e38838438296623dc3c839a39038e38838438296624283a039a39038e38838438296623dc3a039a39038e388384382966241839c39a39038e388384382966240c39c39a39038e38838438296623e439c39a39038e388384382965c3a039c39a39038e38838438294203a039c39739038e38838438293dc3c839a39739038e38838438294283a039a39739038e38838438293dc3a039a39739038e3883843829 else 0x73873067c678670668664700000073867c67867066c668664700000067c67867467066c66866474903c839c39a39739038838438294143a039c39a3973903883843829) else 0) else (if Nat.beq k 83 then 0x73873067c678670668664773867c67867066c668664767c67867467066c6686647 else 0)) else (if Nat.blt k 88 then (if Nat.beq k 84 then 0x73873067c678670668664773867c67867066c668664767c67867467066c6686647 else 0) else (if Nat.beq k 88 then (if j < 2 then (if j < 1 then 0x37e11406402101e01a01600d00a005001b00000037e1fc06c02201e01a00e009005001a00037e1fc07406c02201e01a00e009005001b00037e1f807406c02201e01a00e009005001b00037e0dc07406c02201e01a00e009005001b00000037e2b806c02101e01a00e009005001a00037e2080e802201e01a01600e009005001b00037e34407002201e01a01600e009005001b00037e20807002201e01a01600e009005001b00037e2bc06c02201e01a01600e009005001b00037e20806c02201e01a01600e009005001b00000037e06c02101e01a01600e009005001a00037e0dc06c02101e01a01600e009005001b00000037e33407401e01a01600d009005001a00000037e07402201e01a01600d009005001a00037e1f807402201e01a01600d009005001b else 0x37e13406c06802201e01a01600e00a005001c37e0c806c06802201e01a01600e00a005001c37e11407006402201e01a01600e00a005001c00000037e2f806402101e01a00d00a005001a00037e2f811406402101e01a00d00a005001b00000000037e2fc02101a01600d00a005001900000037e2fc06402101a01600d00a005001a00037e2fc11406402101a01600d00a005001b00037e1d00d402201e01a01600d00a005001b00037e1140d402201e01a01600d00a005001b00037e1d007402201e01a01600d00a005001b00037e31806802201e01a01600d00a005001b00037e1d006802201e01a01600d00a005001b00037e30006402201e01a01600d00a005001b00037e1d006402201e01a01600d00a005001b00000037e06402101e01a01600d00a005001a) else (if j < 3 then 0x37e0b40a402101e01a01600e009006001b00037e0f805402101e01a01600e009006001b00000037e06c06806402201e01a00e005001a00000037e07006c06402201e01a00a005001a00000037e07006c06801e01a01600a005001a00037e0d407406c02201e01a00e00a005001b00037e0d406c06802201e01a00e00a005001b00037e0d406c06402201e01a00e00a005001b00000000037e13002101e01a00e00a005001900000037e13006c02101e01a00e00a005001a00000037e13006402101e01a00e00a005001a00037e13006c06402101e01a00e00a005001b00037e11406c06402101e01a00e00a005001b00037e0dc06c06402101e01a00e00a005001b00000037e13402201e01a01600e00a005001a00037e13406802201e01a01600e00a005001b else (if j < 4 then 0x37e06c06405c02201e01a00e00a006001b00000037e0b406402101e01a00e00a006001a00037e0e406405802101e01a00e00a006001b00037e0b406405802101e01a00e00a006001b00037e06c06805c01e01a01600e00a006001b00037e07006805801e01a01600e00a006001b00037e0b406802201e01a01600e00a006001b00037e0d406805c01e01a01600d00a006001b00037e08806805c01e01a01600d00a006001b00037e11405c02201e01a01600d00a006001b37e07806405c02201e01a01600d00a006001c00037e0b407406c02201e01a00e009006001b00037e08807406c02201e01a00e009006001b00037e0b408402201e01a01600e009006001b00037e07806c02201e01a01600e009006001b00037e0f80b402101e01a01600e009006001b else 0x6623d039c39a39038e38838438290000000006623ac39c39a39038e38838438290000000006623a839c39a39038e38838438290000000006623a439c39a39038e38838438290000000006623a039c39a39038e388384382937e06405c04402201e01a01600e00a006002c37e06c05c04002201e01a01600e00a006002c37e06c06803c02201e01a01600e00a006002c00000014c10402101e01a01500e009005002a00014c10404402101e01a01500e009005002b00000037e06806405802201e01a00d006001a00000037e06806405c01e01a01600d006001a))) else 0))) else (if Nat.blt k 91 then (if Nat.blt k 90 then (if Nat.beq k 89 then (if j < 1 then 0x18004402201e01a01500e009005002a1040fc02101e01a01500e009005002a07406c04c01e01a01300e009005002a0ec02201e01a01601300e009005002a37e06806405802201e01a00d006001a37e06806405c01e01a01600d006001a37e06c06806402201e01a00e005001a37e07006c06402201e01a00a005001a37e07006c06801e01a01600a005001a37e11406c02101e01a00e00a005001a37e0dc06402101e01a00e00a005001a37e13402201e01a01600e00a005001a13402201e01a01601300e00a005001a37e2fc11402101a01600d00a005001a37e2fc06402101a01600d00a005001a2fc06402101a01601300d00a005001a else (if j < 2 then 0x6623a439c39a39038e38838438290006623a039c39a39038e38838438290000003dc39a39739038e38838438280003d439c39a39739038e38838438290003d039c39a39739038e38838438290003bc39c39a39739038e38838438290003b839c39a39739038e38838438290003b439c39a39739038e38838438290003b039c39a39739038e38838438290003ac39c39a39739038e38838438290003a839c39a39739038e38838438290003a439c39a39739038e38838438290003a039c39a39739038e388384382906c04c04402201e01a016013009005a06c06404402101e01a01300a005002a10406c04402101e01a016009005002a else 0x3d839c39a39738e38838438280000006623dc39a39038e38838438280006623d039c39a39038e38838438290006623ac39c39a39038e38838438290006623a839c39a39038e3883843829)) else 0) else (if Nat.beq k 90 then (if j < 1 then 0x7406c04c01e01a01300e009005002a0ec02201e01a01601300e009005002a37e06806405802201e01a00d006001a37e06806405c01e01a01600d006001a06806405802201e01a01300d006001a06806405c01e01a01601300d006001a37e1a402201e01a01600d00a006001a37e06c06806402201e01a00e005001a06c06806402201e01a01300e005001a07006806401e01a01601300e005001a37e07006c06402201e01a00a005001a37e07006c06801e01a01600a005001a07006c06402201e01a01300a005001a07006c06801e01a01601300a005001a37e13402201e01a01600e00a005001a13402201e01a01601300e00a005001a else (if j < 2 then 0x3dc39a39739038e38838438280003d439c39a39739038e38838438290003d039c39a39739038e38838438290003bc39c39a39739038e38838438290003b839c39a39739038e38838438290003b439c39a39739038e38838438290003b039c39a39739038e38838438290003ac39c39a39739038e38838438290003a839c39a39739038e38838438290003a439c39a39739038e38838438290003a039c39a39739038e388384382906c04404002101e01a01601300a005a06c04c04402201e01a016013009005a06c06404002101e01a01300e005002a06c06404402101e01a01300a005002a07406c04402201e01a013009005002a else 0x3d839c39a39738e38838438280000006623dc39a39038e38838438280006623d039c39a39038e38838438290006623ac39c39a39038e38838438290006623a839c39a39038e38838438290006623a439c39a39038e38838438290006623a039c39a39038e3883843829)) else 0)) else (if Nat.blt k 92 then (if Nat.beq k 91 then 0x6623dc39a39038e38838438286623ac39c39a39038e38838438296623a839c39a39038e38838438296623a439c39a39038e38838438296623a039c39a39038e38838438293bc39c39a39739038e38838438293b839c39a39739038e38838438293b439c39a39739038e38838438293b039c39a39739038e38838438293ac39c39a39739038e38838438293a839c39a39739038e38838438293a439c39a39739038e38838438293a039c39a39739038e3883843829 else 0) else (if Nat.blt k 96 then (if Nat.beq k 92 then 0x3d839c39a39738e38838438286623dc39a39038e38838438283dc39a39739038e3883843828 else 0) else (if Nat.beq k 96 then (if j < 1 then 0x37e07006402201e01a01600e00a005001b37e07406002201e01a01600e00a005001b00037e0d402201e01a01600d00a005001a37e0d407402201e01a01600d00a005001b37e0d406802201e01a01600d00a005001b37e0d406402201e01a01600d00a005001b00037e11402101e01a01600d00a005001a37e11406402101e01a01600d00a005001b00037e07406c02201e01a00e009005001a00037e0e802201e01a01600e009005001a37e0e807002201e01a01600e009005001b37e0e806c02201e01a01600e009005001b00037e0dc02101e01a01600e009005001a37e0dc06c02101e01a01600e009005001b00037e1f802201e01a01600d009005001a37e1f807402201e01a01600d009005001b else 0x66239c39a39038e388384382800000000039c39a39739038e388384382837e06405c02201e01a01600d00a006001b37e06805802201e01a01600d00a006001b37e07405002201e01a01600d00a006001b37e06c05c02201e01a01600e009006001b37e07405402201e01a01600e009006001b00037e0b402101e01a01600e009006001a37e0b405402101e01a01600e009006001b00037e06c06402101e01a00e00a005001a37e06c06802201e01a01600e00a005001b) else 0)))))) else (if Nat.blt k 108 then (if Nat.blt k 101 then (if Nat.blt k 99 then (if Nat.blt k 98 then (if Nat.beq k 97 then (if j < 3 then (if j < 1 then 0x37e06c03b01e01a01600e009005001a00037e0e802201e01a01600e009005001a37e0e807002201e01a01600e009005001b37e0e806c02201e01a01600e009005001b00037e0dc02101e01a01600e009005001a37e0dc06c02101e01a01600e009005001b00007406c02201e01a01300e009005001a00006c03b01e01a01601300e009005001a0000dc02101e01a01601300e009005001a0dc06c02101e01a01601300e009005001b00020002201e01a01501300e009005001a20007002201e01a01501300e009005001b00037e1f802201e01a01600d009005001a37e1f807402201e01a01600d009005001b0001f802201e01a01601300d009005001a1f807402201e01a01601300d009005001b else (if j < 2 then 0x37e06803702201e01a00d00a005001a00037e06403b01e01a01600d00a005001a00037e0d402201e01a01600d00a005001a37e0d407402201e01a01600d00a005001b37e0d406802201e01a01600d00a005001b37e0d406402201e01a01600d00a005001b00037e11402101e01a01600d00a005001a37e11406402101e01a01600d00a005001b00006803702201e01a01300d00a005001a00006403b01e01a01601300d00a005001a00011402101e01a01601300d00a005001a11406402101e01a01601300d00a005001b0000c802201e01a01501300d00a005001a0c806802201e01a01501300d00a005001b00007006c02201e01a016013009005001a00037e07406c02201e01a00e009005001a else 0xb402101e01a01601300e009006001a00006c02f02101e01a01601300e005001a00006806402201e01a01601300d005001a00007402f02201e01a01601300d005001a00006403302101e01a01601300a005001a00006803302201e01a01501300a005001a00037e06c06402101e01a00e00a005001a00037e06003702101e01a00e00a005001a37e06c06802201e01a01600e00a005001b37e07006402201e01a01600e00a005001b37e07406002201e01a01600e00a005001b00006c06402101e01a01300e00a005001a00006003702101e01a01300e00a005001a06c06802201e01a01601300e00a005001b07006402201e01a01601300e00a005001b00007006801e01a01501300e00a005001a)) else (if j < 4 then 0x9804402201e01a01501300e009005002b0000fc02101e01a01501300e009005002a0fc04402101e01a01501300e009005002b37e06405c02201e01a01600d00a006001b37e06805802201e01a01600d00a006001b37e07405002201e01a01600d00a006001b06405c02201e01a01601300d00a006001b06805802201e01a01601300d00a006001b00005803302101e01a016013009006001a00037e05403702101e01a00e009006001a37e06c05c02201e01a01600e009006001b37e07405402201e01a01600e009006001b00037e0b402101e01a01600e009006001a37e0b405402101e01a01600e009006001b00005403702101e01a01300e009006001a06c05c02201e01a01601300e009006001b else (if j < 5 then 0x39c39a39739038e388384382806404402101e01a01601300e00a005002b06c04002101e01a01601300e00a005002b06804402201e01a01501300e00a005002b07004002201e01a01501300e00a005002b00006c04402101e01a016013009005002a00004803302101e01a016013009005002a00004c03302201e01a015013009005002a00000010402101e01a01500e009005002900010404402101e01a01500e009005002a06c04c02201e01a01601300e009005002b07404402201e01a01601300e009005002b00004403b01e01a01501300e009005002a00009802201e01a01501300e009005002a09807002201e01a01501300e009005002b09804c02201e01a01501300e009005002b else 0x66239c39a39038e3883843828))) else 0) else (if Nat.beq k 98 then (if j < 2 then (if j < 1 then 0x37e07406c02201e01a00e009005001a00037e06c03b01e01a01600e009005001a00037e0e802201e01a01600e009005001a00037e0dc02101e01a01600e009005001a37e0dc06c02101e01a01600e009005001b00007406c02201e01a01300e009005001a00007003702201e01a01300e009005001a00006c03b01e01a01601300e009005001a0000dc02101e01a01601300e009005001a0dc06c02101e01a01601300e009005001b00020002201e01a01501300e009005001a20007002201e01a01501300e009005001b00037e1f802201e01a01600d009005001a37e1f807402201e01a01600d009005001b0001f802201e01a01601300d009005001a1f807402201e01a01601300d009005001b else 0xe402101e01a01601300e00a005001a00007006801e01a01501300e00a005001a00006003b01e01a01501300e00a005001a00037e06803702201e01a00d00a005001a00037e06403b01e01a01600d00a005001a00037e0d402201e01a01600d00a005001a00037e11402101e01a01600d00a005001a37e11406402101e01a01600d00a005001b00006803702201e01a01300d00a005001a00006403b01e01a01601300d00a005001a0000d402201e01a01601300d00a005001a00011402101e01a01601300d00a005001a11406402101e01a01601300d00a005001b0000c802201e01a01501300d00a005001a0c806802201e01a01501300d00a005001b00007006c02201e01a016013009005001a) else (if j < 3 then 0x37e0b402101e01a01600e009006001a00005403702101e01a01300e009006001a0000b402101e01a01601300e009006001a00006c02f02101e01a01601300e005001a00006806402201e01a01601300d005001a00007402f02201e01a01601300d005001a00006403302101e01a01601300a005001a00006803302201e01a01501300a005001a00037e06c06402101e01a00e00a005001a00037e06003702101e01a00e00a005001a37e06c06802201e01a01600e00a005001b37e07006402201e01a01600e00a005001b00006c06402101e01a01300e00a005001a00006003702101e01a01300e00a005001a06c06802201e01a01601300e00a005001b07006402201e01a01601300e00a005001b else (if j < 4 then 0x10402101e01a01500e009005002900010404402101e01a01500e009005002a06c04c02201e01a01601300e009005002b07404402201e01a01601300e009005002b00004403b01e01a01501300e009005002a00009802201e01a01501300e009005002a09804402201e01a01501300e009005002b0000fc02101e01a01501300e009005002a0fc04402101e01a01501300e009005002b37e06405c02201e01a01600d00a006001b37e06805802201e01a01600d00a006001b06405c02201e01a01601300d00a006001b06805802201e01a01601300d00a006001b00005803302101e01a016013009006001a00037e05403702101e01a00e009006001a37e06c05c02201e01a01600e009006001b else 0x66239c39a39038e388384382800000000039c39a39739038e388384382806404402101e01a01601300e00a005002b06c04002101e01a01601300e00a005002b06804402201e01a01501300e00a005002b00006c04402101e01a016013009005002a00004803302101e01a016013009005002a00004c03302201e01a015013009005002a))) else 0)) else (if Nat.blt k 100 then (if Nat.beq k 99 then 0x66239c39a39038e388384382800000039c39a39739038e388384382806c04402101e01a016013009005002a10404402101e01a01500e009005002a04403b01e01a01501300e009005002a09802201e01a01501300e009005002a06806402201e01a01601300d005001a37e06c06402101e01a00e00a005001a06c06402101e01a01300e00a005001a07006801e01a01501300e00a005001a37e11402101e01a01600d00a005001a11402101e01a01601300d00a005001a07006c02201e01a016013009005001a37e07406c02201e01a00e009005001a07406c02201e01a01300e009005001a else 0) else (if Nat.beq k 100 then 0x66239c39a39038e388384382800039c39a39739038e388384382810402101e01a01500e0090050029 else 0))) else (if Nat.blt k 105 then (if Nat.blt k 104 then (if Nat.beq k 101 then 0x66239c39a39038e388384382839c39a39739038e3883843828 else 0) else (if Nat.beq k 104 then 0x37e06402101e01a01600d00a005001a37e06c02101e01a01600e009005001a37e07402201e01a01600d009005001a else 0)) else (if Nat.blt k 106 then (if Nat.beq k 105 then 0x4402101e01a01501300e009005002a37e06402101e01a01600d00a005001a06402101e01a01601300d00a005001a06802201e01a01501300d00a005001a00003302101e01a015013009005001937e06c02101e01a01600e009005001a06c02101e01a01601300e009005001a07002201e01a01501300e009005001a37e07402201e01a01600d009005001a00037e03b01e01a01500d009005001907402201e01a01601300d009005001a00003b01e01a01501300d0090050019 else 0) else (if Nat.blt k 107 then (if Nat.beq k 106 then 0x4402101e01a01501300e009005002a37e06402101e01a01600d00a005001a06402101e01a01601300d00a005001a06802201e01a01501300d00a005001a00003302101e01a015013009005001937e06c02101e01a01600e009005001a06c02101e01a01601300e009005001a07002201e01a01501300e009005001a37e07402201e01a01600d009005001a00037e03b01e01a01500d009005001907402201e01a01601300d009005001a00003b01e01a01501300d0090050019 else 0) else (if Nat.beq k 107 then 0x4402101e01a01501300e009005002a37e06402101e01a01600d00a005001a06402101e01a01601300d00a005001a06802201e01a01501300d00a005001a00003302101e01a015013009005001937e06c02101e01a01600e009005001a06c02101e01a01601300e009005001a07002201e01a01501300e009005001a37e07402201e01a01600d009005001a00037e03b01e01a01500d009005001907402201e01a01601300d009005001a00003b01e01a01501300d0090050019 else 0))))) else (if Nat.blt k 114 then (if Nat.blt k 112 then (if Nat.blt k 109 then (if Nat.beq k 108 then 0x4402101e01a01501300e009005002a37e06402101e01a01600d00a005001a06402101e01a01601300d00a005001a06802201e01a01501300d00a005001a00003302101e01a015013009005001937e06c02101e01a01600e009005001a06c02101e01a01601300e009005001a07002201e01a01501300e009005001a37e07402201e01a01600d009005001a00037e03b01e01a01500d009005001907402201e01a01601300d009005001a00003b01e01a01501300d0090050019 else 0) else (if Nat.beq k 109 then 0x3302101e01a015013009005001937e03b01e01a01500d009005001903b01e01a01501300d0090050019 else 0)) else (if Nat.blt k 113 then (if Nat.beq k 112 then 0x37e02101e01a01500d0090050019 else 0) else (if Nat.beq k 113 then 0x37e02101e01a01500d009005001902101e01a01501300d0090050019 else 0))) else (if Nat.blt k 116 then (if Nat.blt k 115 then (if Nat.beq k 114 then 0x37e02101e01a01500d009005001902101e01a01501300d0090050019 else 0) else (if Nat.beq k 115 then 0x37e02101e01a01500d009005001902101e01a01501300d0090050019 else 0)) else (if Nat.blt k 117 then (if Nat.beq k 116 then 0x37e02101e01a01500d009005001902101e01a01501300d0090050019 else 0) else (if Nat.blt k 118 then (if Nat.beq k 117 then 0x37e02101e01a01500d009005001902101e01a01501300d0090050019 else 0) else (if Nat.beq k 118 then 0x37e02101e01a01500d009005001902101e01a01501300d0090050019 else 0)))))))
def countCodeChunk (_j : Nat) : Nat := 0x81020408101000018c183060300001031f2289b00000031a9d2cc000000306563440000000163f03b000000000002580000000000000900000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def countCode (i : Nat) : Nat := (countCodeChunk (i / 128) >>> (7 * (i % 128))) &&& 0x7f
def widthCodeChunk (_j : Nat) : Nat := 0x707070707070700000707c7c7c7c7c000064707c88888800000064707c7c940000005858707c88000000005864647c000000000000587000000000000000640000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000
def widthCode (i : Nat) : Nat := (widthCodeChunk (i / 128) >>> (8 * (i % 128))) &&& 0xff
def saltCodeChunk (_j : Nat) : Nat := 0x300000000000000000000
def saltCode (i : Nat) : Nat := (saltCodeChunk (i / 128) >>> (1 * (i % 128))) &&& 1
def lanesCodeChunk (_j : Nat) : Nat := 0x4081020408102043152a54a880204082252689c02040841c9134e02040820441cc102040811442941020408102041440204081020408702040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081
def lanesCode (i : Nat) : Nat := (lanesCodeChunk (i / 128) >>> (7 * (i % 128))) &&& 0x7f
def multiplierChunk (_j : Nat) : Nat := 0x19f3e7cf9f3e702073e7cf9f3e702073e7cf9f3e702040b5cf9f3b502040e7cf9f3b50204081ced73e7020408102073e7020408102040e702040810204081020408102040810204081020408102040810204081020408102040810204081020408102040810204081
def multiplier (i : Nat) : Nat := (multiplierChunk (i / 128) >>> (7 * (i % 128))) &&& 0x7f
def laneBitsChunk (_j : Nat) : Nat := 0x22222211157777511237997111468891113368911116699111111391111111511111111111111111111111111111111111111111111111111111111
def laneBits (i : Nat) : Nat := (laneBitsChunk (i / 128) >>> (4 * (i % 128))) &&& 15
def indexBitsChunk (_j : Nat) : Nat := 0x55555511168888611569bba11169aab111669bb111189cb1111117b1111111811111111111111111111111111111111111111111111111111111111
def indexBits (i : Nat) : Nat := (indexBitsChunk (i / 128) >>> (4 * (i % 128))) &&& 15
def shiftsCode (key : Nat) : Nat := (if Nat.blt key 90 then (if Nat.blt key 81 then (if Nat.blt key 74 then (if Nat.blt key 72 then (if Nat.beq key 64 then 0x180000000000400010000000000000c0000000000400000000000000000200000000600000000002000000001000000000000000000000000000010000000000000000000000203008000000 else 0) else (if Nat.blt key 73 then (if Nat.beq key 72 then 0x8000200000000000000000004000040000000000000000040000008000600000000003000040001000000000000040000008040000000000000000040200008040000 else 0) else (if Nat.beq key 73 then 0x30000002020000000020000000040000006000000c0000000000000038000201008000001008000401008000200000000200008000400000040202000000000008000000008000000000000000008000200000000000 else 0))) else (if Nat.blt key 75 then (if Nat.beq key 74 then 0x30000010010000c0044 else 0) else (if Nat.blt key 80 then (if Nat.beq key 75 then 0x1000041000 else 0) else (if Nat.beq key 80 then 0x408000000000000000400000080000000080004000080000000000002000080000010000000000000002010000400000000000000000000010000000000000c0a01010000000 else 0)))) else (if Nat.blt key 84 then (if Nat.blt key 82 then (if Nat.beq key 81 then 0x30100020000010001030101010000070100010100000102000000000000010000000000050000050000010103010000000000000100000000 else 0) else (if Nat.blt key 83 then (if Nat.beq key 82 then 0x430c0001001001040000041 else 0) else (if Nat.beq key 83 then 1 else 0))) else (if Nat.blt key 88 then (if Nat.beq key 84 then 1 else 0) else (if Nat.blt key 89 then (if Nat.beq key 88 then 0x80000020000002010000000030080000000080000010000804000000000000000400010001802000000400000000400000100400010080000000000008010000c0002008000000000000001000000200 else 0) else (if Nat.beq key 89 then 0x10000030001000000020000000001000000000100000101000000000000010000 else 0))))) else (if Nat.blt key 104 then (if Nat.blt key 97 then (if Nat.blt key 91 then (if Nat.beq key 90 then 0x1000100000002000000000001000000000000000000000300000001000000000000 else 0) else (if Nat.blt key 96 then (if Nat.beq key 91 then 0x40001006106000000000 else 0) else (if Nat.beq key 96 then 0x1800204000080008004080000000101 else 0))) else (if Nat.blt key 98 then (if Nat.beq key 97 then 0x200000000000000000200000000000008040000000000000000000000010000000000000001000000200000040000000000000000000002000000000000000401000000000000000003000080000000040000 else 0) else (if Nat.blt key 99 then (if Nat.beq key 98 then 0x2000000001000000002000000000000000001000040001020000000000000000000000001010000000008000200000080000000000000000000200000000000000040000000000200000000002 else 0) else (if Nat.beq key 99 then 0x1000400000000800004000 else 0)))) else (if Nat.blt key 107 then (if Nat.blt key 105 then (if Nat.beq key 104 then 0x80000400 else 0) else (if Nat.blt key 106 then (if Nat.beq key 105 then 0x80000000080000000000040000400000 else 0) else (if Nat.beq key 106 then 0x80000000080000000000040000400000 else 0))) else (if Nat.blt key 108 then (if Nat.beq key 107 then 0x80000000080000000000040000400000 else 0) else (if Nat.blt key 109 then (if Nat.beq key 108 then 0x80000000080000000000040000400000 else 0) else (if Nat.beq key 109 then 0x2008001 else 0))))))
def entriesCode (key : Nat) : Nat := (if Nat.blt key 97 then (if Nat.blt key 82 then (if Nat.blt key 73 then (if Nat.blt key 65 then (if Nat.blt key 64 then (if Nat.beq key 56 then 0x56011500c60082000000580000422a0000009800009b008559b0000000000000 else 0) else (if Nat.beq key 64 then 0x1ce00000086e00000000000426670000000000000039ccb80000000170c00000000ec8007370000000000000000000000001230003dd23d5ff0d00000000000000b840014a800000000000001e600000000000000000000000000000000000000000001c340000000000000000000000000000006df7a14a000f7c0011f00000000000000002b500000000000000000002a9000000000000000013940000000005c000000000000061b0016a8000000000000000000000000000000cbf5927f0000000009b000000001e308600000763001975b88000011d8000000000000011c00000000000000fd400000a220000000000000000000000000000004d200000000000000fd00000160400644d6b44196d3ce9a001ceb4300000000001000000a4000000000000000000000000000000000000000002b498d000844419b64a000000580000000000005560000000000000000000000000005d94fb5a000000000000000007095529e800000000000000000016082a2c2000000003981b400253001079e3800000000000000000029f0dd000840000009f40021a4b800000000000000000002270017b0000000000000000089a8f400000000000000000000000000000000000000763d97c70000001b016800000ec0001e4001499acdefc62895b700023a00000000000000000b10000000000000000000000000000001b9000000000003141bc000000014a0000000000000000000191c00085d9600000000000000001070000000000000000000000296001c38003460006380000031000000000000000000001640000000000000000000003a7d5300000000689001bdf2300000000000000000000000000000000000000015800000000000005950000000000081200000000001288005270000039c8003701618b93500000000000000000000000000000000000000175000000000000005da00000000000aff39cfb else 0)) else (if Nat.blt key 72 then (if Nat.beq key 65 then 0xb4001005c058 else 0) else (if Nat.beq key 72 then 0xd6d3f800000001fa80091ef2400000000000000000000000030365e00000000000000000000004bc802ed0000000000005a000000007bc000000000004b800000000000002f9000000000000000000000000000000000000000000000000000000000000034000000002308000000000011f00107c00000000002688008ee00000235000000000000006363c800000000000000000000000000000000000000f7c0009b000000cf8000000009a8000000000000e89400000421000000130002b80000000000000000000000000fd8003e200000000000000000000cc001ee11800000000000766000000000000000000000139c000000000021b800000000000006e0564000000f83a4da0000000000040900000012000000001c380f6dc000000000000000000000094c000000000000000000000000000000001d8c1e9700013080025a000000000000003e800000000004bb000458000000000000000000000014000000fcc00000000000000008100027e92c0000000000000000000000000a30000000000000000000000000000000000dc8000f60000000000052e258dd00000000000024000002fa0000000000000129400000346001fa00041800146800000000004e5570000000924d2000000000000021a800000a540003e000000000007ba000000000000000000000000000000000879b8a4b0000000000000000000000000e7400000001338000000005b400000000000000002ee04c00000001134c30000000000000000000021ca200000000353816000000100000000000000031c98bf2516002460000002c4000000010d96b80028c0000000000000000000260dbde3c348140000000039e00400000898034000000000000000002e0017d800000000f280000000000000000000003190010800000000118c000000004ac0000000000000161000000002c100000000000000000000000001bc08800 else 0))) else (if Nat.blt key 75 then (if Nat.blt key 74 then (if Nat.beq key 73 then 0x40b00082a23d1cf4fd0004d15970000007390006440006b40000000000000000000007790000000000000000000000000003450000000008130004e600009b00069d0000000001b90000000000000000003b300000000000000065d0000003030000000000000000002c10007620000000000005697e90000000850005277ba0000000005d96e100057f2690000001fb0000007366cb0005810000000000000000000000000000007ff0000004e76b20000000000000000007207bb0000000c70007bd00005955200052900000032f3df0000006ca65b0000007bc2110000000000004210000000000000000000000000000004e40007d11a302d4bb4370000000006e00000005ef0000000006f700053f00000000000000042000000000062e00000011f00000000000000000000051148f64700041e2ab39d0000006b56890007230000000000000000000000000000000000154630004b95c052600000000135b00000000000000000000083f00069e5c30000000000000000000000000000000000000004fb7a70000000000006050160000000005100007d30000000000001770003876f500044d0000001e50000000000006df0003c970b18d7650000000000005537a500037170d0000000000000000000000000000005ad00000001482b4fc00069f0000000000000000170005ed7a600000000000000000004300053d0000000000000000000000000004e50000000007e70000000002d700000047900000000000069c0000000000001090000000000004a50000005d60000000000000000dd0000007a400000000000065c00000055527f0007910000006730b15aa25365a1356c95133f514b0000000000000002950000000004fa00000000000059400000000000064553e6de74c0000006310000000001610004cf51253c41f0002ed74f0000000000000005540000000000000000000000000000006b300000000000064600000000077b0006c80005280f300056b06f319000000000227000000000000000000000000000000000000000000000000000000000000000 else 0) else (if Nat.beq key 74 then 0x21400f00031000c7794d55e003780000db003c4000000000009b9910c5ada6341a38f300001620000000000000314000000d2268008f965ba000b800000099b721200000000000 else 0)) else (if Nat.blt key 80 then (if Nat.beq key 75 then 0xdd0014dc00000000000000001682439b000000000000000000840000178500000000000000152d00c5000001000000000083b10000f1006f000000000000006c else 0) else (if Nat.blt key 81 then (if Nat.beq key 80 then 0x37b123b800000000a3eb8c0000047afb80000000000000000000000001b000000000404000eb00000000000000000000000800000000000045b000000e3000000ca8000000011684280000052c0000038a000000000000022200000000000000000000000000000000000000000000000000000000000000000000073a000fdb1984200000000000000000006d8000000004220000000000000021800000000000003ca0000053f5436b40000068a000002696e287400000a42a2d9d89d5db5e074800000000000000000000000000068c000000000018780000031c0000000000000000000000000ea00000000000000c98000000000000040b0020000000090c0000000000000000000000001c380000101c00000b0261000000000000004df00000000419001556cb80044e00000000000000000000000000000000000000000000000000000000b4000000000000053a52a000000001e6000000000000021b9b9000001198b1000000000ec90b3d4000004c00024780000000000000000000003d70014940000031a4d4000ee0000000050b0b273c849b22b00000000000000000000000000958005180000000065e0000000000000160800000000000000000000000000138c0000000000000000000000000000000013f800000000005c30000000000000000000000000000000000000000041846c00000000000000000000000008100000000000000000000004c93911e58180047294c00000000c94000000003fc000000005dec7278a46001558000000013a800000002b10002080015bd79368000000003940000000052000000017000001cb00000055c000000000000000000022dd9ccd0000024e00000000000000000000000000000025a0003340000011f0000000000000118c002d7000000000000000000000000026c000000005840000000000000000000000005ac000374a100000000000000 else 0) else (if Nat.beq key 81 then 0x6eb034c40013c0003ca0000000040e0011c00059c6663891f0012282c80000000063c6f0010bee1b570000000027f0000000000000005c001f20016b44d8000000000015780c000003f500000284ca55ae10eb1800a7e000002f98b6a5442c9cbb0eb80000000000000000000001d99f43ecaae22c5983523c001010005c01d8005707ece78006a60000027b0000019400068200000000000000001090000000000083a0000015c000000a5b100a20017d37f80200058da4000000004f50000000016e001346b5800000da400000a2692cd1aeda6e00000000000001f60000011e40002d2dae5400000000000000000000000013500000000000000f7cb9000000000005d90000016780000000000b9331a8440017788c0000000079363c0000000000000000001066f795a000094ee42e0007180033d0001bc00000000000003d689200000000976560b0800732001cb800000000dc800 else 0))))) else (if Nat.blt key 89 then (if Nat.blt key 84 then (if Nat.blt key 83 then (if Nat.beq key 82 then 0x2161200000000001001a80000d131f46e9003ae86683300000007996772005380000000000000006a000000058802c38d0005e5a00000ed035721e153600001f800be0000000a8 else 0) else (if Nat.beq key 83 then 0x1b565c0 else 0)) else (if Nat.blt key 88 then (if Nat.beq key 84 then 0x1b565c0 else 0) else (if Nat.beq key 88 then 0x4fe0000000000052c000009a2000000002c20000000000000000000000000000000000014c8000000000000000005c00000a82000000850010dcbb9351f20000004300135739800000000000000000000035b00063c000000000023180051113437800000a540000000000000000000000000000000000038994a00000000cd8000003f53dc0000053100000000000000000000000000000018dbb200000000000000000b70000000066a4a729a0602d9cf91f0dce93ca9a40067f00140ecc00018f41c0000000000000000766c380000000114400493cdf56eb58000000031e800000f7e36cbf0000014b8000000000000000000000000000000000000004240023dbde000000000006618caabb86000000005e68ac4db710014540000000123c00000000000000000000000000034665800000000000000000000021d80000000000000000000001cf1ba00000000000000000000000000000000000000000a03084000000007c0000005874200053200000000000000000000000010e00000006e0032e800000000004794aa00135e810000000000000000000000000002c0d1700000000000000002c580037b1ea78800000f24003030000005acfdaac0000000065e00160800d0000000000a90000000000000024000000165c00000000003188000000028cd6c92000071800000c1400000cb20000000000000000000000000001e700000000000be2e1c00000000002628010000000000000000000000000e756bd5594e6ec0000000000000000c4f6b400000000000000003f600000000000000003b7000000005719dc0000000000000000059000d1400575cac00000000000bb6978000000010880000000113bcb00102c0000000000000000001664799130000000000000000000000000002c1800000002ef000000000000008ac00000000000000006549daf3d86513000000005760009067f00000047f02800 else 0))) else (if Nat.blt key 91 then (if Nat.blt key 90 then (if Nat.beq key 89 then 0x2e60000000000001c700303ba56bc9c00b4c2d0000000000000000000000000003106c4000000000000aac0006ee460800002f90000000000001fbb388e000000000000000002c139c0000000000000000000000000001640000000000002c4000028d586d79a4000000010c00000000000027c00000001bc00000004240000000002b747c000000000000c3c0000000984000000058800000000000000000a84750000000000000000000000000001a3000002dc00b40000000000000634000000094c00000b3844000000037c0031e7f000000023d0000089c00c46fa5dc000000000000003190000000000000006e40021c00000007cc00001359dc0052c0005ddd3d400002fb0000000000000f4001cf00400000855b0000000000000000000009b00090000000029500000001e53740000000000003cc0000000bb400 else 0) else (if Nat.beq key 90 then 0xc480000000001f33cf2fc5400d4eff0000000000000000000000000000000033c00000001dd00000b5c00003106080000325000000000031c0089efa000000000000000002ed44c0000000000000000000000000000001739c00000000006f00000ae695c0c0000000004000000010c00174000000000000000000013500000002e352c00001b90033b000000028d000000000000000000000000000000002cd0000000000000000000000000001cf000001d400bf000000000000068c00001619fc00000718f4000010b000002c6ab000000026900085c9a53cf5775ac0026c00000000034500000001e50000000000000000000087c0000000a8c0000000002094840000327000000000000120001fb000006340000000000003d00000000000590000000000002c10000000211424000002d0000047c0000000c64dd else 0)) else (if Nat.blt key 92 then (if Nat.beq key 91 then 0xb802040000000a22577c260a0000005d83b00001e600000b40000000000116000001f00378018e000026c000069ac400ea8ac5c00852c800860000000000000001ba00002f40000 else 0) else (if Nat.blt key 96 then (if Nat.beq key 92 then 0x409173c0025000ec002302d else 0) else (if Nat.beq key 96 then 0x17900000000000009b164e6001e570d656e63d000003d4000000037c004254b000005dc00000000000000000001d02258200000000000022773cf768dc1294dd0b4e805c0031c0000000001615f4000000000000000004d400000004a0732140074c0000000000000012900121000004f40153c0000000000006e800000007f4a10000063a110000084d54600750011f0012a48c002c44344c000000000000 else 0)))))) else (if Nat.blt key 108 then (if Nat.blt key 101 then (if Nat.blt key 99 then (if Nat.blt key 98 then (if Nat.beq key 97 then 0x102800000001820000018ef39cfd0000023cee1000002b6000000001e9a3f00000000000000000000005400000000000000000139001ad8002c20016e0002578455acfda3d7c0374b5e320010874480000000000000cfc0000000000000000000000001768000000024980000000000000000a2400000000000000000000000063194ca56ed0000012ee8a9673f8000000000000000037300000000000000495418004220007980000000000000712000000000000000000000058400000000001af8000000000029bb2e1660a8004d2d1400000000002688000000000030d2975db288000000000031900000000000000000000006489200000000000000000000a7a058000000000ba97c372a0e7dc400000144000cba00000000000000003ca000fd5fb0000000000002d692000000000000000000000000000000000000005290000000034e00000000000000000002b500000000647001ad5f53b455e00000648000000004c56f242400000000001cec83000000002550000000000000000000000000000000000000000000000124000000b9a000001f00000024780000000240800000000d1800000003028006b762c000000015546880010a00197800000000000002460000000026a0000000000000215a81cd000000000001738000000000023d000000000000000000000000089cbba1c1e52efa7d3f8000000000000000000139800000001e48000016df339b900000000000136001230007be00000000001a4c00000000dec000c7000002d7000bdee1c0000000170c000000000016bb9200000000000001b2c000008c60005880000010c0022731b6b69f86f71a0000000000000000000000dd0002ad55c000003be000000003b30000000000088200000000000000003370000000000000000160800000000005d90020000000000197800390a5600000000000a28000009cf5d400000000b8800000 else 0) else (if Nat.beq key 98 then 0x102800000001770000000000058b0000013fe1b00000274000000000003a700000000000000000000004bc00000000000000918000000014b5f00014200000000139cfd8007683ccaad82000002e1800000000000000000000000000000000000000000002d7000002128000000000000000091c00000000000000000000000058187094e9500089aaae48951000000fe0000000000000068e0000000000000120a11000000848000000000035d00073c000000000000000000052c000000000019980000000000259000001f48591a2c6400000000002318000000009aaf79e4002d0800000000003030000000000000000000000000c380000000000000000000971ef8000000012a817ad70e8dcd1400000123000b5a000000000000000039e000f25e50000000000002d63a000000000000000000000000000000000000004a500000191000000000000000007400027300000000597000efaf7b884da000ed5980000022b800000d3400000000001b8800000000000000000000000000000000000000000000000000000000000108800000a3a000001f000000210800000000000000000000018d00000000000aaacbc00000001344428001ce00000000000000000000000000000023e000000000000000023fb700000000000147800000000000001d900000000000000001fb2d8000a00001e5001764b0a3d0000000000000000000000000001ce80000141cd1db700000000000136000000007660000000000173400000000d3e7f0dd0000000035ba7e0000000000144c00000000001b32c100000000000001814000008162c40000000010c004fd44f2ecbb8000de001b080000000000000000d200026b4d8000003920000000038700031c000007feab00000056c0000000000000000000000a54000000000000052900000400000000002d74a76c800000000000920000009e31e400000000b3000000 else 0)) else (if Nat.blt key 100 then (if Nat.beq key 99 then 0x68a7401130000000000005c00b10000001350000000000000000010000190000026c0000003740000000014c00738010a708fb4800000000000b20024042002cb1c000079a8400000000000000590c00de000000000848000000000000000000000114000000000003a0000000000de0000000001d0000000000000000a4850005a00000000000000000000002f00000 else 0) else (if Nat.beq key 100 then 0x5702d else 0))) else (if Nat.blt key 105 then (if Nat.blt key 104 then (if Nat.beq key 101 then 0x417 else 0) else (if Nat.beq key 104 then 0x406c0b800001b17c0000000003119000b57080018700005 else 0)) else (if Nat.blt key 106 then (if Nat.beq key 105 then 0xc789a50000009b008d00000000000000794500000000bb002d0000000031475a0000de00004801e10000000b63c800000087f300648500000000002e000000b10000006f000000000002000000000000460000003200440000868a590000430000000c00180000707a000000170000000000000035dd2f00000000000000 else 0) else (if Nat.blt key 107 then (if Nat.beq key 106 then 0xc789a50000009b008d00000000000000794500000000bb002d0000000031475a0000de00004801e10000000b63c800000087f300648500000000002e000000b10000006f000000000002000000000000460000003200440000868a590000430000000c00180000707a000000170000000000000035dd2f00000000000000 else 0) else (if Nat.beq key 107 then 0xc789a50000009b008d00000000000000794500000000bb002d0000000031475a0000de00004801e10000000b63c800000087f300648500000000002e000000b10000006f000000000002000000000000460000003200440000868a590000430000000c00180000707a000000170000000000000035dd2f00000000000000 else 0))))) else (if Nat.blt key 114 then (if Nat.blt key 112 then (if Nat.blt key 109 then (if Nat.beq key 108 then 0xc789a50000009b008d00000000000000794500000000bb002d0000000031475a0000de00004801e10000000b63c800000087f300648500000000002e000000b10000006f000000000002000000000000460000003200440000868a590000430000000c00180000707a000000170000000000000035dd2f00000000000000 else 0) else (if Nat.beq key 109 then 0x6c003730002d0400020002c000000001c7c00195c0018000 else 0)) else (if Nat.blt key 113 then (if Nat.beq key 112 then 1 else 0) else (if Nat.beq key 113 then 0x5c01 else 0))) else (if Nat.blt key 116 then (if Nat.blt key 115 then (if Nat.beq key 114 then 0x5c01 else 0) else (if Nat.beq key 115 then 0x5c01 else 0)) else (if Nat.blt key 117 then (if Nat.beq key 116 then 0x5c01 else 0) else (if Nat.blt key 118 then (if Nat.beq key 117 then 0x5c01 else 0) else (if Nat.beq key 118 then 0x5c01 else 0)))))))

def checkpointCount (k t : Nat) : Nat := countCode (8*k+t)
def shape (k t i : Nat) : List Nat :=
  let key := 8*k+t
  let bits := shapeChunk key (i / 16) >>> (widthCode key * (i % 16))
  readShape (bits &&& 15) (bits >>> 4)
def checkpoint (k t i : Nat) : List Wire := (shape k t i).map (wire readLiteral)
def hint (k t : Nat) (w : List Wire) : Nat :=
  let key := 8*k+t
  let h := frontierHash (saltCode key) w
  let bits := laneBits key
  let mask := (1 <<< bits)-1
  let bucket := h % lanesCode key
  let offset := (shiftsCode key >>> (bits*bucket)) &&& mask
  let slot := (h*multiplier key % 1048573+offset) &&& mask
  (entriesCode key >>> (indexBits key*slot)) &&& ((1 <<< indexBits key)-1)

def matched (k t : Nat) (w : List Wire) : Bool :=
  match hint k t w with
  | 0 => false
  | code+1 =>
    let i := code / 22
    let g := code % 22
    Nat.blt i (checkpointCount k t) &&
      if Nat.beq g 0 then isPermFast w (checkpoint k t i) else
        let l := shape k t i
        l.all (coversCode g) && isPermFast w (l.map (wire (movedLiteral g)))
lemma matchedImpossible {k t w} (known : ∀ i < checkpointCount k t, Impossible k t (checkpoint k t i))
    (ok : matched k t w = true) : Impossible k t w := by
  unfold matched at ok
  cases eq : hint k t w with
  | zero => simp [eq] at ok
  | succ code =>
    simp only [eq,Bool.and_eq_true,Nat.blt_eq] at ok
    obtain ⟨hi,test⟩ := ok
    split at test
    · exact perm_impossible (isPermFast_perm test) (known _ hi)
    · simp only [Bool.and_eq_true] at test
      obtain ⟨usable,p⟩ := test
      obtain ⟨rot,good⟩ := moveShape _ _ usable
      rw [rot] at p
      exact perm_impossible (isPermFast_perm p)
        (movedImpossible _ _ _ good (known _ hi))
def resume (k t : Nat) (w : List Wire) : Bool :=
  if matched k t w then false else search k t w
lemma resumeImpossible {k t w} (known : ∀ i < checkpointCount k t, Impossible k t (checkpoint k t i))
    (ok : resume k t w = false) : Impossible k t w := by
  unfold resume at ok
  split at ok
  · next ht => exact matchedImpossible known ht
  · exact exclude_search ok

def rowCheck (k t i : Nat) : Bool :=
  match k with
  | 0 => !search 0 t (checkpoint 0 t i)
  | k + 1 => !stepTest k t (checkpoint (k+1) t i) (resume k (t-1)) (resume k t)

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_7_0_0 : span (rowCheck 7 0) 5 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_7_0_5 : span (rowCheck 7 0) 4 5 = true := by decide +kernel
lemma join_7_0_0_9 : span (rowCheck 7 0) 9 0 = true := @span_join (rowCheck 7 0) 5 0 4 b_7_0_0 b_7_0_5
lemma pass_7_0 : span (rowCheck 7 0) (checkpointCount 7 0) 0 = true := join_7_0_0_9
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_8_0_0 : span (rowCheck 8 0) 5 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_8_0_5 : span (rowCheck 8 0) 5 5 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_8_0_10 : span (rowCheck 8 0) 5 10 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_8_0_15 : span (rowCheck 8 0) 5 15 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_8_0_20 : span (rowCheck 8 0) 5 20 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_8_0_25 : span (rowCheck 8 0) 5 25 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_8_0_30 : span (rowCheck 8 0) 5 30 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_8_0_35 : span (rowCheck 8 0) 5 35 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_8_0_40 : span (rowCheck 8 0) 5 40 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_8_0_45 : span (rowCheck 8 0) 5 45 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_8_0_50 : span (rowCheck 8 0) 5 50 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_8_0_55 : span (rowCheck 8 0) 5 55 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_8_0_60 : span (rowCheck 8 0) 5 60 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_8_0_65 : span (rowCheck 8 0) 5 65 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_8_0_70 : span (rowCheck 8 0) 5 70 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_8_0_75 : span (rowCheck 8 0) 5 75 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_8_0_80 : span (rowCheck 8 0) 5 80 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_8_0_85 : span (rowCheck 8 0) 3 85 = true := by decide +kernel
lemma join_8_0_0_10 : span (rowCheck 8 0) 10 0 = true := @span_join (rowCheck 8 0) 5 0 5 b_8_0_0 b_8_0_5
lemma join_8_0_10_10 : span (rowCheck 8 0) 10 10 = true := @span_join (rowCheck 8 0) 5 10 5 b_8_0_10 b_8_0_15
lemma join_8_0_20_10 : span (rowCheck 8 0) 10 20 = true := @span_join (rowCheck 8 0) 5 20 5 b_8_0_20 b_8_0_25
lemma join_8_0_30_10 : span (rowCheck 8 0) 10 30 = true := @span_join (rowCheck 8 0) 5 30 5 b_8_0_30 b_8_0_35
lemma join_8_0_40_10 : span (rowCheck 8 0) 10 40 = true := @span_join (rowCheck 8 0) 5 40 5 b_8_0_40 b_8_0_45
lemma join_8_0_50_10 : span (rowCheck 8 0) 10 50 = true := @span_join (rowCheck 8 0) 5 50 5 b_8_0_50 b_8_0_55
lemma join_8_0_60_10 : span (rowCheck 8 0) 10 60 = true := @span_join (rowCheck 8 0) 5 60 5 b_8_0_60 b_8_0_65
lemma join_8_0_70_10 : span (rowCheck 8 0) 10 70 = true := @span_join (rowCheck 8 0) 5 70 5 b_8_0_70 b_8_0_75
lemma join_8_0_80_8 : span (rowCheck 8 0) 8 80 = true := @span_join (rowCheck 8 0) 5 80 3 b_8_0_80 b_8_0_85
lemma join_8_0_0_20 : span (rowCheck 8 0) 20 0 = true := @span_join (rowCheck 8 0) 10 0 10 join_8_0_0_10 join_8_0_10_10
lemma join_8_0_20_20 : span (rowCheck 8 0) 20 20 = true := @span_join (rowCheck 8 0) 10 20 10 join_8_0_20_10 join_8_0_30_10
lemma join_8_0_40_20 : span (rowCheck 8 0) 20 40 = true := @span_join (rowCheck 8 0) 10 40 10 join_8_0_40_10 join_8_0_50_10
lemma join_8_0_60_20 : span (rowCheck 8 0) 20 60 = true := @span_join (rowCheck 8 0) 10 60 10 join_8_0_60_10 join_8_0_70_10
lemma join_8_0_0_40 : span (rowCheck 8 0) 40 0 = true := @span_join (rowCheck 8 0) 20 0 20 join_8_0_0_20 join_8_0_20_20
lemma join_8_0_40_40 : span (rowCheck 8 0) 40 40 = true := @span_join (rowCheck 8 0) 20 40 20 join_8_0_40_20 join_8_0_60_20
lemma join_8_0_0_80 : span (rowCheck 8 0) 80 0 = true := @span_join (rowCheck 8 0) 40 0 40 join_8_0_0_40 join_8_0_40_40
lemma join_8_0_0_88 : span (rowCheck 8 0) 88 0 = true := @span_join (rowCheck 8 0) 80 0 8 join_8_0_0_80 join_8_0_80_8
lemma pass_8_0 : span (rowCheck 8 0) (checkpointCount 8 0) 0 = true := join_8_0_0_88
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_8_1_0 : span (rowCheck 8 1) 4 0 = true := by decide +kernel
lemma pass_8_1 : span (rowCheck 8 1) (checkpointCount 8 1) 0 = true := b_8_1_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_0_0 : span (rowCheck 9 0) 5 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_0_5 : span (rowCheck 9 0) 5 5 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_0_10 : span (rowCheck 9 0) 5 10 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_0_15 : span (rowCheck 9 0) 5 15 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_0_20 : span (rowCheck 9 0) 5 20 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_0_25 : span (rowCheck 9 0) 5 25 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_0_30 : span (rowCheck 9 0) 5 30 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_0_35 : span (rowCheck 9 0) 5 35 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_0_40 : span (rowCheck 9 0) 5 40 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_0_45 : span (rowCheck 9 0) 5 45 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_0_50 : span (rowCheck 9 0) 5 50 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_0_55 : span (rowCheck 9 0) 4 55 = true := by decide +kernel
lemma join_9_0_0_10 : span (rowCheck 9 0) 10 0 = true := @span_join (rowCheck 9 0) 5 0 5 b_9_0_0 b_9_0_5
lemma join_9_0_10_10 : span (rowCheck 9 0) 10 10 = true := @span_join (rowCheck 9 0) 5 10 5 b_9_0_10 b_9_0_15
lemma join_9_0_20_10 : span (rowCheck 9 0) 10 20 = true := @span_join (rowCheck 9 0) 5 20 5 b_9_0_20 b_9_0_25
lemma join_9_0_30_10 : span (rowCheck 9 0) 10 30 = true := @span_join (rowCheck 9 0) 5 30 5 b_9_0_30 b_9_0_35
lemma join_9_0_40_10 : span (rowCheck 9 0) 10 40 = true := @span_join (rowCheck 9 0) 5 40 5 b_9_0_40 b_9_0_45
lemma join_9_0_50_9 : span (rowCheck 9 0) 9 50 = true := @span_join (rowCheck 9 0) 5 50 4 b_9_0_50 b_9_0_55
lemma join_9_0_0_20 : span (rowCheck 9 0) 20 0 = true := @span_join (rowCheck 9 0) 10 0 10 join_9_0_0_10 join_9_0_10_10
lemma join_9_0_20_20 : span (rowCheck 9 0) 20 20 = true := @span_join (rowCheck 9 0) 10 20 10 join_9_0_20_10 join_9_0_30_10
lemma join_9_0_40_19 : span (rowCheck 9 0) 19 40 = true := @span_join (rowCheck 9 0) 10 40 9 join_9_0_40_10 join_9_0_50_9
lemma join_9_0_0_40 : span (rowCheck 9 0) 40 0 = true := @span_join (rowCheck 9 0) 20 0 20 join_9_0_0_20 join_9_0_20_20
lemma join_9_0_0_59 : span (rowCheck 9 0) 59 0 = true := @span_join (rowCheck 9 0) 40 0 19 join_9_0_0_40 join_9_0_40_19
lemma pass_9_0 : span (rowCheck 9 0) (checkpointCount 9 0) 0 = true := join_9_0_0_59
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_1_0 : span (rowCheck 9 1) 5 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_1_5 : span (rowCheck 9 1) 5 5 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_1_10 : span (rowCheck 9 1) 5 10 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_1_15 : span (rowCheck 9 1) 5 15 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_1_20 : span (rowCheck 9 1) 5 20 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_1_25 : span (rowCheck 9 1) 5 25 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_1_30 : span (rowCheck 9 1) 5 30 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_1_35 : span (rowCheck 9 1) 5 35 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_1_40 : span (rowCheck 9 1) 5 40 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_1_45 : span (rowCheck 9 1) 5 45 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_1_50 : span (rowCheck 9 1) 5 50 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_1_55 : span (rowCheck 9 1) 5 55 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_1_60 : span (rowCheck 9 1) 5 60 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_1_65 : span (rowCheck 9 1) 5 65 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_1_70 : span (rowCheck 9 1) 5 70 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_1_75 : span (rowCheck 9 1) 5 75 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_1_80 : span (rowCheck 9 1) 5 80 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_1_85 : span (rowCheck 9 1) 5 85 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_1_90 : span (rowCheck 9 1) 5 90 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_1_95 : span (rowCheck 9 1) 1 95 = true := by decide +kernel
lemma join_9_1_0_10 : span (rowCheck 9 1) 10 0 = true := @span_join (rowCheck 9 1) 5 0 5 b_9_1_0 b_9_1_5
lemma join_9_1_10_10 : span (rowCheck 9 1) 10 10 = true := @span_join (rowCheck 9 1) 5 10 5 b_9_1_10 b_9_1_15
lemma join_9_1_20_10 : span (rowCheck 9 1) 10 20 = true := @span_join (rowCheck 9 1) 5 20 5 b_9_1_20 b_9_1_25
lemma join_9_1_30_10 : span (rowCheck 9 1) 10 30 = true := @span_join (rowCheck 9 1) 5 30 5 b_9_1_30 b_9_1_35
lemma join_9_1_40_10 : span (rowCheck 9 1) 10 40 = true := @span_join (rowCheck 9 1) 5 40 5 b_9_1_40 b_9_1_45
lemma join_9_1_50_10 : span (rowCheck 9 1) 10 50 = true := @span_join (rowCheck 9 1) 5 50 5 b_9_1_50 b_9_1_55
lemma join_9_1_60_10 : span (rowCheck 9 1) 10 60 = true := @span_join (rowCheck 9 1) 5 60 5 b_9_1_60 b_9_1_65
lemma join_9_1_70_10 : span (rowCheck 9 1) 10 70 = true := @span_join (rowCheck 9 1) 5 70 5 b_9_1_70 b_9_1_75
lemma join_9_1_80_10 : span (rowCheck 9 1) 10 80 = true := @span_join (rowCheck 9 1) 5 80 5 b_9_1_80 b_9_1_85
lemma join_9_1_90_6 : span (rowCheck 9 1) 6 90 = true := @span_join (rowCheck 9 1) 5 90 1 b_9_1_90 b_9_1_95
lemma join_9_1_0_20 : span (rowCheck 9 1) 20 0 = true := @span_join (rowCheck 9 1) 10 0 10 join_9_1_0_10 join_9_1_10_10
lemma join_9_1_20_20 : span (rowCheck 9 1) 20 20 = true := @span_join (rowCheck 9 1) 10 20 10 join_9_1_20_10 join_9_1_30_10
lemma join_9_1_40_20 : span (rowCheck 9 1) 20 40 = true := @span_join (rowCheck 9 1) 10 40 10 join_9_1_40_10 join_9_1_50_10
lemma join_9_1_60_20 : span (rowCheck 9 1) 20 60 = true := @span_join (rowCheck 9 1) 10 60 10 join_9_1_60_10 join_9_1_70_10
lemma join_9_1_80_16 : span (rowCheck 9 1) 16 80 = true := @span_join (rowCheck 9 1) 10 80 6 join_9_1_80_10 join_9_1_90_6
lemma join_9_1_0_40 : span (rowCheck 9 1) 40 0 = true := @span_join (rowCheck 9 1) 20 0 20 join_9_1_0_20 join_9_1_20_20
lemma join_9_1_40_40 : span (rowCheck 9 1) 40 40 = true := @span_join (rowCheck 9 1) 20 40 20 join_9_1_40_20 join_9_1_60_20
lemma join_9_1_0_80 : span (rowCheck 9 1) 80 0 = true := @span_join (rowCheck 9 1) 40 0 40 join_9_1_0_40 join_9_1_40_40
lemma join_9_1_0_96 : span (rowCheck 9 1) 96 0 = true := @span_join (rowCheck 9 1) 80 0 16 join_9_1_0_80 join_9_1_80_16
lemma pass_9_1 : span (rowCheck 9 1) (checkpointCount 9 1) 0 = true := join_9_1_0_96
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_2_0 : span (rowCheck 9 2) 5 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_2_5 : span (rowCheck 9 2) 5 5 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_2_10 : span (rowCheck 9 2) 5 10 = true := by decide +kernel
lemma join_9_2_0_10 : span (rowCheck 9 2) 10 0 = true := @span_join (rowCheck 9 2) 5 0 5 b_9_2_0 b_9_2_5
lemma join_9_2_0_15 : span (rowCheck 9 2) 15 0 = true := @span_join (rowCheck 9 2) 10 0 5 join_9_2_0_10 b_9_2_10
lemma pass_9_2 : span (rowCheck 9 2) (checkpointCount 9 2) 0 = true := join_9_2_0_15
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_3_0 : span (rowCheck 9 3) 5 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_3_5 : span (rowCheck 9 3) 5 5 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_9_3_10 : span (rowCheck 9 3) 1 10 = true := by decide +kernel
lemma join_9_3_0_10 : span (rowCheck 9 3) 10 0 = true := @span_join (rowCheck 9 3) 5 0 5 b_9_3_0 b_9_3_5
lemma join_9_3_0_11 : span (rowCheck 9 3) 11 0 = true := @span_join (rowCheck 9 3) 10 0 1 join_9_3_0_10 b_9_3_10
lemma pass_9_3 : span (rowCheck 9 3) (checkpointCount 9 3) 0 = true := join_9_3_0_11
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_0_0 : span (rowCheck 10 0) 5 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_0_5 : span (rowCheck 10 0) 5 5 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_0_10 : span (rowCheck 10 0) 5 10 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_0_15 : span (rowCheck 10 0) 5 15 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_0_20 : span (rowCheck 10 0) 5 20 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_0_25 : span (rowCheck 10 0) 5 25 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_0_30 : span (rowCheck 10 0) 5 30 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_0_35 : span (rowCheck 10 0) 5 35 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_0_40 : span (rowCheck 10 0) 5 40 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_0_45 : span (rowCheck 10 0) 5 45 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_0_50 : span (rowCheck 10 0) 5 50 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_0_55 : span (rowCheck 10 0) 5 55 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_0_60 : span (rowCheck 10 0) 5 60 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_0_65 : span (rowCheck 10 0) 3 65 = true := by decide +kernel
lemma join_10_0_0_10 : span (rowCheck 10 0) 10 0 = true := @span_join (rowCheck 10 0) 5 0 5 b_10_0_0 b_10_0_5
lemma join_10_0_10_10 : span (rowCheck 10 0) 10 10 = true := @span_join (rowCheck 10 0) 5 10 5 b_10_0_10 b_10_0_15
lemma join_10_0_20_10 : span (rowCheck 10 0) 10 20 = true := @span_join (rowCheck 10 0) 5 20 5 b_10_0_20 b_10_0_25
lemma join_10_0_30_10 : span (rowCheck 10 0) 10 30 = true := @span_join (rowCheck 10 0) 5 30 5 b_10_0_30 b_10_0_35
lemma join_10_0_40_10 : span (rowCheck 10 0) 10 40 = true := @span_join (rowCheck 10 0) 5 40 5 b_10_0_40 b_10_0_45
lemma join_10_0_50_10 : span (rowCheck 10 0) 10 50 = true := @span_join (rowCheck 10 0) 5 50 5 b_10_0_50 b_10_0_55
lemma join_10_0_60_8 : span (rowCheck 10 0) 8 60 = true := @span_join (rowCheck 10 0) 5 60 3 b_10_0_60 b_10_0_65
lemma join_10_0_0_20 : span (rowCheck 10 0) 20 0 = true := @span_join (rowCheck 10 0) 10 0 10 join_10_0_0_10 join_10_0_10_10
lemma join_10_0_20_20 : span (rowCheck 10 0) 20 20 = true := @span_join (rowCheck 10 0) 10 20 10 join_10_0_20_10 join_10_0_30_10
lemma join_10_0_40_20 : span (rowCheck 10 0) 20 40 = true := @span_join (rowCheck 10 0) 10 40 10 join_10_0_40_10 join_10_0_50_10
lemma join_10_0_0_40 : span (rowCheck 10 0) 40 0 = true := @span_join (rowCheck 10 0) 20 0 20 join_10_0_0_20 join_10_0_20_20
lemma join_10_0_40_28 : span (rowCheck 10 0) 28 40 = true := @span_join (rowCheck 10 0) 20 40 8 join_10_0_40_20 join_10_0_60_8
lemma join_10_0_0_68 : span (rowCheck 10 0) 68 0 = true := @span_join (rowCheck 10 0) 40 0 28 join_10_0_0_40 join_10_0_40_28
lemma pass_10_0 : span (rowCheck 10 0) (checkpointCount 10 0) 0 = true := join_10_0_0_68
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_1_0 : span (rowCheck 10 1) 5 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_1_5 : span (rowCheck 10 1) 5 5 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_1_10 : span (rowCheck 10 1) 5 10 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_1_15 : span (rowCheck 10 1) 5 15 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_1_20 : span (rowCheck 10 1) 5 20 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_1_25 : span (rowCheck 10 1) 5 25 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_1_30 : span (rowCheck 10 1) 5 30 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_1_35 : span (rowCheck 10 1) 5 35 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_1_40 : span (rowCheck 10 1) 5 40 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_1_45 : span (rowCheck 10 1) 5 45 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_1_50 : span (rowCheck 10 1) 5 50 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_1_55 : span (rowCheck 10 1) 5 55 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_1_60 : span (rowCheck 10 1) 5 60 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_1_65 : span (rowCheck 10 1) 5 65 = true := by decide +kernel
lemma join_10_1_0_10 : span (rowCheck 10 1) 10 0 = true := @span_join (rowCheck 10 1) 5 0 5 b_10_1_0 b_10_1_5
lemma join_10_1_10_10 : span (rowCheck 10 1) 10 10 = true := @span_join (rowCheck 10 1) 5 10 5 b_10_1_10 b_10_1_15
lemma join_10_1_20_10 : span (rowCheck 10 1) 10 20 = true := @span_join (rowCheck 10 1) 5 20 5 b_10_1_20 b_10_1_25
lemma join_10_1_30_10 : span (rowCheck 10 1) 10 30 = true := @span_join (rowCheck 10 1) 5 30 5 b_10_1_30 b_10_1_35
lemma join_10_1_40_10 : span (rowCheck 10 1) 10 40 = true := @span_join (rowCheck 10 1) 5 40 5 b_10_1_40 b_10_1_45
lemma join_10_1_50_10 : span (rowCheck 10 1) 10 50 = true := @span_join (rowCheck 10 1) 5 50 5 b_10_1_50 b_10_1_55
lemma join_10_1_60_10 : span (rowCheck 10 1) 10 60 = true := @span_join (rowCheck 10 1) 5 60 5 b_10_1_60 b_10_1_65
lemma join_10_1_0_20 : span (rowCheck 10 1) 20 0 = true := @span_join (rowCheck 10 1) 10 0 10 join_10_1_0_10 join_10_1_10_10
lemma join_10_1_20_20 : span (rowCheck 10 1) 20 20 = true := @span_join (rowCheck 10 1) 10 20 10 join_10_1_20_10 join_10_1_30_10
lemma join_10_1_40_20 : span (rowCheck 10 1) 20 40 = true := @span_join (rowCheck 10 1) 10 40 10 join_10_1_40_10 join_10_1_50_10
lemma join_10_1_0_40 : span (rowCheck 10 1) 40 0 = true := @span_join (rowCheck 10 1) 20 0 20 join_10_1_0_20 join_10_1_20_20
lemma join_10_1_40_30 : span (rowCheck 10 1) 30 40 = true := @span_join (rowCheck 10 1) 20 40 10 join_10_1_40_20 join_10_1_60_10
lemma join_10_1_0_70 : span (rowCheck 10 1) 70 0 = true := @span_join (rowCheck 10 1) 40 0 30 join_10_1_0_40 join_10_1_40_30
lemma pass_10_1 : span (rowCheck 10 1) (checkpointCount 10 1) 0 = true := join_10_1_0_70
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_2_0 : span (rowCheck 10 2) 5 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_2_5 : span (rowCheck 10 2) 5 5 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_2_10 : span (rowCheck 10 2) 5 10 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_2_15 : span (rowCheck 10 2) 5 15 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_2_20 : span (rowCheck 10 2) 1 20 = true := by decide +kernel
lemma join_10_2_0_10 : span (rowCheck 10 2) 10 0 = true := @span_join (rowCheck 10 2) 5 0 5 b_10_2_0 b_10_2_5
lemma join_10_2_10_10 : span (rowCheck 10 2) 10 10 = true := @span_join (rowCheck 10 2) 5 10 5 b_10_2_10 b_10_2_15
lemma join_10_2_0_20 : span (rowCheck 10 2) 20 0 = true := @span_join (rowCheck 10 2) 10 0 10 join_10_2_0_10 join_10_2_10_10
lemma join_10_2_0_21 : span (rowCheck 10 2) 21 0 = true := @span_join (rowCheck 10 2) 20 0 1 join_10_2_0_20 b_10_2_20
lemma pass_10_2 : span (rowCheck 10 2) (checkpointCount 10 2) 0 = true := join_10_2_0_21
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_3_0 : span (rowCheck 10 3) 3 0 = true := by decide +kernel
lemma pass_10_3 : span (rowCheck 10 3) (checkpointCount 10 3) 0 = true := b_10_3_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_10_4_0 : span (rowCheck 10 4) 3 0 = true := by decide +kernel
lemma pass_10_4 : span (rowCheck 10 4) (checkpointCount 10 4) 0 = true := b_10_4_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_0_0 : span (rowCheck 11 0) 5 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_0_5 : span (rowCheck 11 0) 5 5 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_0_10 : span (rowCheck 11 0) 5 10 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_0_15 : span (rowCheck 11 0) 5 15 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_0_20 : span (rowCheck 11 0) 5 20 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_0_25 : span (rowCheck 11 0) 5 25 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_0_30 : span (rowCheck 11 0) 5 30 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_0_35 : span (rowCheck 11 0) 5 35 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_0_40 : span (rowCheck 11 0) 5 40 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_0_45 : span (rowCheck 11 0) 5 45 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_0_50 : span (rowCheck 11 0) 5 50 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_0_55 : span (rowCheck 11 0) 5 55 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_0_60 : span (rowCheck 11 0) 5 60 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_0_65 : span (rowCheck 11 0) 5 65 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_0_70 : span (rowCheck 11 0) 5 70 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_0_75 : span (rowCheck 11 0) 1 75 = true := by decide +kernel
lemma join_11_0_0_10 : span (rowCheck 11 0) 10 0 = true := @span_join (rowCheck 11 0) 5 0 5 b_11_0_0 b_11_0_5
lemma join_11_0_10_10 : span (rowCheck 11 0) 10 10 = true := @span_join (rowCheck 11 0) 5 10 5 b_11_0_10 b_11_0_15
lemma join_11_0_20_10 : span (rowCheck 11 0) 10 20 = true := @span_join (rowCheck 11 0) 5 20 5 b_11_0_20 b_11_0_25
lemma join_11_0_30_10 : span (rowCheck 11 0) 10 30 = true := @span_join (rowCheck 11 0) 5 30 5 b_11_0_30 b_11_0_35
lemma join_11_0_40_10 : span (rowCheck 11 0) 10 40 = true := @span_join (rowCheck 11 0) 5 40 5 b_11_0_40 b_11_0_45
lemma join_11_0_50_10 : span (rowCheck 11 0) 10 50 = true := @span_join (rowCheck 11 0) 5 50 5 b_11_0_50 b_11_0_55
lemma join_11_0_60_10 : span (rowCheck 11 0) 10 60 = true := @span_join (rowCheck 11 0) 5 60 5 b_11_0_60 b_11_0_65
lemma join_11_0_70_6 : span (rowCheck 11 0) 6 70 = true := @span_join (rowCheck 11 0) 5 70 1 b_11_0_70 b_11_0_75
lemma join_11_0_0_20 : span (rowCheck 11 0) 20 0 = true := @span_join (rowCheck 11 0) 10 0 10 join_11_0_0_10 join_11_0_10_10
lemma join_11_0_20_20 : span (rowCheck 11 0) 20 20 = true := @span_join (rowCheck 11 0) 10 20 10 join_11_0_20_10 join_11_0_30_10
lemma join_11_0_40_20 : span (rowCheck 11 0) 20 40 = true := @span_join (rowCheck 11 0) 10 40 10 join_11_0_40_10 join_11_0_50_10
lemma join_11_0_60_16 : span (rowCheck 11 0) 16 60 = true := @span_join (rowCheck 11 0) 10 60 6 join_11_0_60_10 join_11_0_70_6
lemma join_11_0_0_40 : span (rowCheck 11 0) 40 0 = true := @span_join (rowCheck 11 0) 20 0 20 join_11_0_0_20 join_11_0_20_20
lemma join_11_0_40_36 : span (rowCheck 11 0) 36 40 = true := @span_join (rowCheck 11 0) 20 40 16 join_11_0_40_20 join_11_0_60_16
lemma join_11_0_0_76 : span (rowCheck 11 0) 76 0 = true := @span_join (rowCheck 11 0) 40 0 36 join_11_0_0_40 join_11_0_40_36
lemma pass_11_0 : span (rowCheck 11 0) (checkpointCount 11 0) 0 = true := join_11_0_0_76
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_1_0 : span (rowCheck 11 1) 5 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_1_5 : span (rowCheck 11 1) 5 5 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_1_10 : span (rowCheck 11 1) 5 10 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_1_15 : span (rowCheck 11 1) 5 15 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_1_20 : span (rowCheck 11 1) 5 20 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_1_25 : span (rowCheck 11 1) 5 25 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_1_30 : span (rowCheck 11 1) 5 30 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_1_35 : span (rowCheck 11 1) 2 35 = true := by decide +kernel
lemma join_11_1_0_10 : span (rowCheck 11 1) 10 0 = true := @span_join (rowCheck 11 1) 5 0 5 b_11_1_0 b_11_1_5
lemma join_11_1_10_10 : span (rowCheck 11 1) 10 10 = true := @span_join (rowCheck 11 1) 5 10 5 b_11_1_10 b_11_1_15
lemma join_11_1_20_10 : span (rowCheck 11 1) 10 20 = true := @span_join (rowCheck 11 1) 5 20 5 b_11_1_20 b_11_1_25
lemma join_11_1_30_7 : span (rowCheck 11 1) 7 30 = true := @span_join (rowCheck 11 1) 5 30 2 b_11_1_30 b_11_1_35
lemma join_11_1_0_20 : span (rowCheck 11 1) 20 0 = true := @span_join (rowCheck 11 1) 10 0 10 join_11_1_0_10 join_11_1_10_10
lemma join_11_1_20_17 : span (rowCheck 11 1) 17 20 = true := @span_join (rowCheck 11 1) 10 20 7 join_11_1_20_10 join_11_1_30_7
lemma join_11_1_0_37 : span (rowCheck 11 1) 37 0 = true := @span_join (rowCheck 11 1) 20 0 17 join_11_1_0_20 join_11_1_20_17
lemma pass_11_1 : span (rowCheck 11 1) (checkpointCount 11 1) 0 = true := join_11_1_0_37
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_2_0 : span (rowCheck 11 2) 5 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_2_5 : span (rowCheck 11 2) 5 5 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_2_10 : span (rowCheck 11 2) 5 10 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_2_15 : span (rowCheck 11 2) 5 15 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_2_20 : span (rowCheck 11 2) 5 20 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_2_25 : span (rowCheck 11 2) 5 25 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_2_30 : span (rowCheck 11 2) 5 30 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_2_35 : span (rowCheck 11 2) 4 35 = true := by decide +kernel
lemma join_11_2_0_10 : span (rowCheck 11 2) 10 0 = true := @span_join (rowCheck 11 2) 5 0 5 b_11_2_0 b_11_2_5
lemma join_11_2_10_10 : span (rowCheck 11 2) 10 10 = true := @span_join (rowCheck 11 2) 5 10 5 b_11_2_10 b_11_2_15
lemma join_11_2_20_10 : span (rowCheck 11 2) 10 20 = true := @span_join (rowCheck 11 2) 5 20 5 b_11_2_20 b_11_2_25
lemma join_11_2_30_9 : span (rowCheck 11 2) 9 30 = true := @span_join (rowCheck 11 2) 5 30 4 b_11_2_30 b_11_2_35
lemma join_11_2_0_20 : span (rowCheck 11 2) 20 0 = true := @span_join (rowCheck 11 2) 10 0 10 join_11_2_0_10 join_11_2_10_10
lemma join_11_2_20_19 : span (rowCheck 11 2) 19 20 = true := @span_join (rowCheck 11 2) 10 20 9 join_11_2_20_10 join_11_2_30_9
lemma join_11_2_0_39 : span (rowCheck 11 2) 39 0 = true := @span_join (rowCheck 11 2) 20 0 19 join_11_2_0_20 join_11_2_20_19
lemma pass_11_2 : span (rowCheck 11 2) (checkpointCount 11 2) 0 = true := join_11_2_0_39
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_3_0 : span (rowCheck 11 3) 5 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_3_5 : span (rowCheck 11 3) 5 5 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_3_10 : span (rowCheck 11 3) 3 10 = true := by decide +kernel
lemma join_11_3_0_10 : span (rowCheck 11 3) 10 0 = true := @span_join (rowCheck 11 3) 5 0 5 b_11_3_0 b_11_3_5
lemma join_11_3_0_13 : span (rowCheck 11 3) 13 0 = true := @span_join (rowCheck 11 3) 10 0 3 join_11_3_0_10 b_11_3_10
lemma pass_11_3 : span (rowCheck 11 3) (checkpointCount 11 3) 0 = true := join_11_3_0_13
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_11_4_0 : span (rowCheck 11 4) 3 0 = true := by decide +kernel
lemma pass_11_4 : span (rowCheck 11 4) (checkpointCount 11 4) 0 = true := b_11_4_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_0_0 : span (rowCheck 12 0) 5 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_0_5 : span (rowCheck 12 0) 5 5 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_0_10 : span (rowCheck 12 0) 5 10 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_0_15 : span (rowCheck 12 0) 5 15 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_0_20 : span (rowCheck 12 0) 5 20 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_0_25 : span (rowCheck 12 0) 2 25 = true := by decide +kernel
lemma join_12_0_0_10 : span (rowCheck 12 0) 10 0 = true := @span_join (rowCheck 12 0) 5 0 5 b_12_0_0 b_12_0_5
lemma join_12_0_10_10 : span (rowCheck 12 0) 10 10 = true := @span_join (rowCheck 12 0) 5 10 5 b_12_0_10 b_12_0_15
lemma join_12_0_20_7 : span (rowCheck 12 0) 7 20 = true := @span_join (rowCheck 12 0) 5 20 2 b_12_0_20 b_12_0_25
lemma join_12_0_0_20 : span (rowCheck 12 0) 20 0 = true := @span_join (rowCheck 12 0) 10 0 10 join_12_0_0_10 join_12_0_10_10
lemma join_12_0_0_27 : span (rowCheck 12 0) 27 0 = true := @span_join (rowCheck 12 0) 20 0 7 join_12_0_0_20 join_12_0_20_7
lemma pass_12_0 : span (rowCheck 12 0) (checkpointCount 12 0) 0 = true := join_12_0_0_27
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_1_0 : span (rowCheck 12 1) 5 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_1_5 : span (rowCheck 12 1) 5 5 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_1_10 : span (rowCheck 12 1) 5 10 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_1_15 : span (rowCheck 12 1) 5 15 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_1_20 : span (rowCheck 12 1) 5 20 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_1_25 : span (rowCheck 12 1) 5 25 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_1_30 : span (rowCheck 12 1) 5 30 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_1_35 : span (rowCheck 12 1) 5 35 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_1_40 : span (rowCheck 12 1) 5 40 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_1_45 : span (rowCheck 12 1) 5 45 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_1_50 : span (rowCheck 12 1) 5 50 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_1_55 : span (rowCheck 12 1) 5 55 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_1_60 : span (rowCheck 12 1) 5 60 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_1_65 : span (rowCheck 12 1) 5 65 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_1_70 : span (rowCheck 12 1) 5 70 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_1_75 : span (rowCheck 12 1) 5 75 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_1_80 : span (rowCheck 12 1) 1 80 = true := by decide +kernel
lemma join_12_1_0_10 : span (rowCheck 12 1) 10 0 = true := @span_join (rowCheck 12 1) 5 0 5 b_12_1_0 b_12_1_5
lemma join_12_1_10_10 : span (rowCheck 12 1) 10 10 = true := @span_join (rowCheck 12 1) 5 10 5 b_12_1_10 b_12_1_15
lemma join_12_1_20_10 : span (rowCheck 12 1) 10 20 = true := @span_join (rowCheck 12 1) 5 20 5 b_12_1_20 b_12_1_25
lemma join_12_1_30_10 : span (rowCheck 12 1) 10 30 = true := @span_join (rowCheck 12 1) 5 30 5 b_12_1_30 b_12_1_35
lemma join_12_1_40_10 : span (rowCheck 12 1) 10 40 = true := @span_join (rowCheck 12 1) 5 40 5 b_12_1_40 b_12_1_45
lemma join_12_1_50_10 : span (rowCheck 12 1) 10 50 = true := @span_join (rowCheck 12 1) 5 50 5 b_12_1_50 b_12_1_55
lemma join_12_1_60_10 : span (rowCheck 12 1) 10 60 = true := @span_join (rowCheck 12 1) 5 60 5 b_12_1_60 b_12_1_65
lemma join_12_1_70_10 : span (rowCheck 12 1) 10 70 = true := @span_join (rowCheck 12 1) 5 70 5 b_12_1_70 b_12_1_75
lemma join_12_1_0_20 : span (rowCheck 12 1) 20 0 = true := @span_join (rowCheck 12 1) 10 0 10 join_12_1_0_10 join_12_1_10_10
lemma join_12_1_20_20 : span (rowCheck 12 1) 20 20 = true := @span_join (rowCheck 12 1) 10 20 10 join_12_1_20_10 join_12_1_30_10
lemma join_12_1_40_20 : span (rowCheck 12 1) 20 40 = true := @span_join (rowCheck 12 1) 10 40 10 join_12_1_40_10 join_12_1_50_10
lemma join_12_1_60_20 : span (rowCheck 12 1) 20 60 = true := @span_join (rowCheck 12 1) 10 60 10 join_12_1_60_10 join_12_1_70_10
lemma join_12_1_0_40 : span (rowCheck 12 1) 40 0 = true := @span_join (rowCheck 12 1) 20 0 20 join_12_1_0_20 join_12_1_20_20
lemma join_12_1_40_40 : span (rowCheck 12 1) 40 40 = true := @span_join (rowCheck 12 1) 20 40 20 join_12_1_40_20 join_12_1_60_20
lemma join_12_1_0_80 : span (rowCheck 12 1) 80 0 = true := @span_join (rowCheck 12 1) 40 0 40 join_12_1_0_40 join_12_1_40_40
lemma join_12_1_0_81 : span (rowCheck 12 1) 81 0 = true := @span_join (rowCheck 12 1) 80 0 1 join_12_1_0_80 b_12_1_80
lemma pass_12_1 : span (rowCheck 12 1) (checkpointCount 12 1) 0 = true := join_12_1_0_81
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_2_0 : span (rowCheck 12 2) 5 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_2_5 : span (rowCheck 12 2) 5 5 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_2_10 : span (rowCheck 12 2) 5 10 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_2_15 : span (rowCheck 12 2) 5 15 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_2_20 : span (rowCheck 12 2) 5 20 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_2_25 : span (rowCheck 12 2) 5 25 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_2_30 : span (rowCheck 12 2) 5 30 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_2_35 : span (rowCheck 12 2) 5 35 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_2_40 : span (rowCheck 12 2) 5 40 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_2_45 : span (rowCheck 12 2) 5 45 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_2_50 : span (rowCheck 12 2) 5 50 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_2_55 : span (rowCheck 12 2) 5 55 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_2_60 : span (rowCheck 12 2) 5 60 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_2_65 : span (rowCheck 12 2) 5 65 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_2_70 : span (rowCheck 12 2) 2 70 = true := by decide +kernel
lemma join_12_2_0_10 : span (rowCheck 12 2) 10 0 = true := @span_join (rowCheck 12 2) 5 0 5 b_12_2_0 b_12_2_5
lemma join_12_2_10_10 : span (rowCheck 12 2) 10 10 = true := @span_join (rowCheck 12 2) 5 10 5 b_12_2_10 b_12_2_15
lemma join_12_2_20_10 : span (rowCheck 12 2) 10 20 = true := @span_join (rowCheck 12 2) 5 20 5 b_12_2_20 b_12_2_25
lemma join_12_2_30_10 : span (rowCheck 12 2) 10 30 = true := @span_join (rowCheck 12 2) 5 30 5 b_12_2_30 b_12_2_35
lemma join_12_2_40_10 : span (rowCheck 12 2) 10 40 = true := @span_join (rowCheck 12 2) 5 40 5 b_12_2_40 b_12_2_45
lemma join_12_2_50_10 : span (rowCheck 12 2) 10 50 = true := @span_join (rowCheck 12 2) 5 50 5 b_12_2_50 b_12_2_55
lemma join_12_2_60_10 : span (rowCheck 12 2) 10 60 = true := @span_join (rowCheck 12 2) 5 60 5 b_12_2_60 b_12_2_65
lemma join_12_2_0_20 : span (rowCheck 12 2) 20 0 = true := @span_join (rowCheck 12 2) 10 0 10 join_12_2_0_10 join_12_2_10_10
lemma join_12_2_20_20 : span (rowCheck 12 2) 20 20 = true := @span_join (rowCheck 12 2) 10 20 10 join_12_2_20_10 join_12_2_30_10
lemma join_12_2_40_20 : span (rowCheck 12 2) 20 40 = true := @span_join (rowCheck 12 2) 10 40 10 join_12_2_40_10 join_12_2_50_10
lemma join_12_2_60_12 : span (rowCheck 12 2) 12 60 = true := @span_join (rowCheck 12 2) 10 60 2 join_12_2_60_10 b_12_2_70
lemma join_12_2_0_40 : span (rowCheck 12 2) 40 0 = true := @span_join (rowCheck 12 2) 20 0 20 join_12_2_0_20 join_12_2_20_20
lemma join_12_2_40_32 : span (rowCheck 12 2) 32 40 = true := @span_join (rowCheck 12 2) 20 40 12 join_12_2_40_20 join_12_2_60_12
lemma join_12_2_0_72 : span (rowCheck 12 2) 72 0 = true := @span_join (rowCheck 12 2) 40 0 32 join_12_2_0_40 join_12_2_40_32
lemma pass_12_2 : span (rowCheck 12 2) (checkpointCount 12 2) 0 = true := join_12_2_0_72
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_3_0 : span (rowCheck 12 3) 5 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_3_5 : span (rowCheck 12 3) 5 5 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_3_10 : span (rowCheck 12 3) 5 10 = true := by decide +kernel
lemma join_12_3_0_10 : span (rowCheck 12 3) 10 0 = true := @span_join (rowCheck 12 3) 5 0 5 b_12_3_0 b_12_3_5
lemma join_12_3_0_15 : span (rowCheck 12 3) 15 0 = true := @span_join (rowCheck 12 3) 10 0 5 join_12_3_0_10 b_12_3_10
lemma pass_12_3 : span (rowCheck 12 3) (checkpointCount 12 3) 0 = true := join_12_3_0_15
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_4_0 : span (rowCheck 12 4) 3 0 = true := by decide +kernel
lemma pass_12_4 : span (rowCheck 12 4) (checkpointCount 12 4) 0 = true := b_12_4_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_12_5_0 : span (rowCheck 12 5) 2 0 = true := by decide +kernel
lemma pass_12_5 : span (rowCheck 12 5) (checkpointCount 12 5) 0 = true := b_12_5_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_13_0_0 : span (rowCheck 13 0) 3 0 = true := by decide +kernel
lemma pass_13_0 : span (rowCheck 13 0) (checkpointCount 13 0) 0 = true := b_13_0_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_13_1_0 : span (rowCheck 13 1) 5 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_13_1_5 : span (rowCheck 13 1) 5 5 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_13_1_10 : span (rowCheck 13 1) 2 10 = true := by decide +kernel
lemma join_13_1_0_10 : span (rowCheck 13 1) 10 0 = true := @span_join (rowCheck 13 1) 5 0 5 b_13_1_0 b_13_1_5
lemma join_13_1_0_12 : span (rowCheck 13 1) 12 0 = true := @span_join (rowCheck 13 1) 10 0 2 join_13_1_0_10 b_13_1_10
lemma pass_13_1 : span (rowCheck 13 1) (checkpointCount 13 1) 0 = true := join_13_1_0_12
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_13_2_0 : span (rowCheck 13 2) 5 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_13_2_5 : span (rowCheck 13 2) 5 5 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_13_2_10 : span (rowCheck 13 2) 2 10 = true := by decide +kernel
lemma join_13_2_0_10 : span (rowCheck 13 2) 10 0 = true := @span_join (rowCheck 13 2) 5 0 5 b_13_2_0 b_13_2_5
lemma join_13_2_0_12 : span (rowCheck 13 2) 12 0 = true := @span_join (rowCheck 13 2) 10 0 2 join_13_2_0_10 b_13_2_10
lemma pass_13_2 : span (rowCheck 13 2) (checkpointCount 13 2) 0 = true := join_13_2_0_12
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_13_3_0 : span (rowCheck 13 3) 5 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_13_3_5 : span (rowCheck 13 3) 5 5 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_13_3_10 : span (rowCheck 13 3) 2 10 = true := by decide +kernel
lemma join_13_3_0_10 : span (rowCheck 13 3) 10 0 = true := @span_join (rowCheck 13 3) 5 0 5 b_13_3_0 b_13_3_5
lemma join_13_3_0_12 : span (rowCheck 13 3) 12 0 = true := @span_join (rowCheck 13 3) 10 0 2 join_13_3_0_10 b_13_3_10
lemma pass_13_3 : span (rowCheck 13 3) (checkpointCount 13 3) 0 = true := join_13_3_0_12
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_13_4_0 : span (rowCheck 13 4) 5 0 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_13_4_5 : span (rowCheck 13 4) 5 5 = true := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_13_4_10 : span (rowCheck 13 4) 2 10 = true := by decide +kernel
lemma join_13_4_0_10 : span (rowCheck 13 4) 10 0 = true := @span_join (rowCheck 13 4) 5 0 5 b_13_4_0 b_13_4_5
lemma join_13_4_0_12 : span (rowCheck 13 4) 12 0 = true := @span_join (rowCheck 13 4) 10 0 2 join_13_4_0_10 b_13_4_10
lemma pass_13_4 : span (rowCheck 13 4) (checkpointCount 13 4) 0 = true := join_13_4_0_12
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_13_5_0 : span (rowCheck 13 5) 3 0 = true := by decide +kernel
lemma pass_13_5 : span (rowCheck 13 5) (checkpointCount 13 5) 0 = true := b_13_5_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_14_0_0 : span (rowCheck 14 0) 1 0 = true := by decide +kernel
lemma pass_14_0 : span (rowCheck 14 0) (checkpointCount 14 0) 0 = true := b_14_0_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_14_1_0 : span (rowCheck 14 1) 2 0 = true := by decide +kernel
lemma pass_14_1 : span (rowCheck 14 1) (checkpointCount 14 1) 0 = true := b_14_1_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_14_2_0 : span (rowCheck 14 2) 2 0 = true := by decide +kernel
lemma pass_14_2 : span (rowCheck 14 2) (checkpointCount 14 2) 0 = true := b_14_2_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_14_3_0 : span (rowCheck 14 3) 2 0 = true := by decide +kernel
lemma pass_14_3 : span (rowCheck 14 3) (checkpointCount 14 3) 0 = true := b_14_3_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_14_4_0 : span (rowCheck 14 4) 2 0 = true := by decide +kernel
lemma pass_14_4 : span (rowCheck 14 4) (checkpointCount 14 4) 0 = true := b_14_4_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_14_5_0 : span (rowCheck 14 5) 2 0 = true := by decide +kernel
lemma pass_14_5 : span (rowCheck 14 5) (checkpointCount 14 5) 0 = true := b_14_5_0
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma b_14_6_0 : span (rowCheck 14 6) 2 0 = true := by decide +kernel
lemma pass_14_6 : span (rowCheck 14 6) (checkpointCount 14 6) 0 = true := b_14_6_0
lemma spans (k t : Nat) (hk : k ≤ 14) (ht : t ≤ 6) : span (rowCheck k t) (checkpointCount k t) 0 = true := by
  interval_cases k
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  · interval_cases t
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  · interval_cases t
    · exact pass_7_0
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  · interval_cases t
    · exact pass_8_0
    · exact pass_8_1
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
  · interval_cases t
    · exact pass_9_0
    · exact pass_9_1
    · exact pass_9_2
    · exact pass_9_3
    · rfl
    · rfl
    · rfl
  · interval_cases t
    · exact pass_10_0
    · exact pass_10_1
    · exact pass_10_2
    · exact pass_10_3
    · exact pass_10_4
    · rfl
    · rfl
  · interval_cases t
    · exact pass_11_0
    · exact pass_11_1
    · exact pass_11_2
    · exact pass_11_3
    · exact pass_11_4
    · rfl
    · rfl
  · interval_cases t
    · exact pass_12_0
    · exact pass_12_1
    · exact pass_12_2
    · exact pass_12_3
    · exact pass_12_4
    · exact pass_12_5
    · rfl
  · interval_cases t
    · exact pass_13_0
    · exact pass_13_1
    · exact pass_13_2
    · exact pass_13_3
    · exact pass_13_4
    · exact pass_13_5
    · rfl
  · interval_cases t
    · exact pass_14_0
    · exact pass_14_1
    · exact pass_14_2
    · exact pass_14_3
    · exact pass_14_4
    · exact pass_14_5
    · exact pass_14_6
lemma sound (k : Nat) (hk : k ≤ 14) (t : Nat) (ht : t ≤ 6) (i : Nat)
    (hi : i < checkpointCount k t) : Impossible k t (checkpoint k t i) := by
  induction k generalizing t i with
  | zero =>
    have checked := span_ok (spans 0 t hk ht) i (Nat.zero_le i) (by simpa only [Nat.zero_add] using hi)
    simp only [rowCheck,Bool.not_eq_true'] at checked
    exact exclude_search checked
  | succ k ih =>
    have checked := span_ok (spans (k+1) t hk ht) i (Nat.zero_le i) (by simpa only [Nat.zero_add] using hi)
    simp only [rowCheck,Bool.not_eq_true'] at checked
    apply exclude_step _ _ checked
    · intro w ok
      apply resumeImpossible _ ok
      intro j hj
      exact ih (by omega) (t-1) (by omega) j hj
    · intro w ok
      apply resumeImpossible _ ok
      intro j hj
      exact ih (by omega) t ht j hj


end ProofTable
namespace VerifiedRows

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaOriginalStart_0 : ProofTable.matched 10 0 (bare thetaOriginalBits) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaOriginalStart_1 : ProofTable.matched 10 1 (bare thetaOriginalBits) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaOriginalStart_2 : ProofTable.matched 10 2 (bare thetaOriginalBits) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaOriginalStart_3 : ProofTable.matched 10 3 (bare thetaOriginalBits) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma thetaOriginalStart_4 : ProofTable.matched 10 4 (bare thetaOriginalBits) = true := by decide +kernel

lemma thetaOriginal : ∀ t ≤ 4, Impossible 10 t (bare thetaOriginalBits) := by

  intro t small

  have ok : ProofTable.matched 10 t (bare thetaOriginalBits) = true := by
    interval_cases t

    · exact thetaOriginalStart_0

    · exact thetaOriginalStart_1

    · exact thetaOriginalStart_2

    · exact thetaOriginalStart_3

    · exact thetaOriginalStart_4

  exact ProofTable.matchedImpossible (fun i hi => ProofTable.sound 10 (by decide) t (by omega) i hi) ok

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma theta3Start_0 : ProofTable.matched 10 0 (bare theta3Bits) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma theta3Start_1 : ProofTable.matched 10 1 (bare theta3Bits) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma theta3Start_2 : ProofTable.matched 10 2 (bare theta3Bits) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma theta3Start_3 : ProofTable.matched 10 3 (bare theta3Bits) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma theta3Start_4 : ProofTable.matched 10 4 (bare theta3Bits) = true := by decide +kernel

lemma theta3 : ∀ t ≤ 4, Impossible 10 t (bare theta3Bits) := by

  intro t small

  have ok : ProofTable.matched 10 t (bare theta3Bits) = true := by
    interval_cases t

    · exact theta3Start_0

    · exact theta3Start_1

    · exact theta3Start_2

    · exact theta3Start_3

    · exact theta3Start_4

  exact ProofTable.matchedImpossible (fun i hi => ProofTable.sound 10 (by decide) t (by omega) i hi) ok

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma theta6Start_0 : ProofTable.matched 10 0 (bare theta6Bits) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma theta6Start_1 : ProofTable.matched 10 1 (bare theta6Bits) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma theta6Start_2 : ProofTable.matched 10 2 (bare theta6Bits) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma theta6Start_3 : ProofTable.matched 10 3 (bare theta6Bits) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma theta6Start_4 : ProofTable.matched 10 4 (bare theta6Bits) = true := by decide +kernel

lemma theta6 : ∀ t ≤ 4, Impossible 10 t (bare theta6Bits) := by

  intro t small

  have ok : ProofTable.matched 10 t (bare theta6Bits) = true := by
    interval_cases t

    · exact theta6Start_0

    · exact theta6Start_1

    · exact theta6Start_2

    · exact theta6Start_3

    · exact theta6Start_4

  exact ProofTable.matchedImpossible (fun i hi => ProofTable.sound 10 (by decide) t (by omega) i hi) ok

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma theta7Start_0 : ProofTable.matched 10 0 (bare theta7Bits) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma theta7Start_1 : ProofTable.matched 10 1 (bare theta7Bits) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma theta7Start_2 : ProofTable.matched 10 2 (bare theta7Bits) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma theta7Start_3 : ProofTable.matched 10 3 (bare theta7Bits) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma theta7Start_4 : ProofTable.matched 10 4 (bare theta7Bits) = true := by decide +kernel

lemma theta7 : ∀ t ≤ 4, Impossible 10 t (bare theta7Bits) := by

  intro t small

  have ok : ProofTable.matched 10 t (bare theta7Bits) = true := by
    interval_cases t

    · exact theta7Start_0

    · exact theta7Start_1

    · exact theta7Start_2

    · exact theta7Start_3

    · exact theta7Start_4

  exact ProofTable.matchedImpossible (fun i hi => ProofTable.sound 10 (by decide) t (by omega) i hi) ok

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma eightStart_0 : ProofTable.matched 12 0 (eightWires) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma eightStart_1 : ProofTable.matched 12 1 (eightWires) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma eightStart_2 : ProofTable.matched 12 2 (eightWires) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma eightStart_3 : ProofTable.matched 12 3 (eightWires) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma eightStart_4 : ProofTable.matched 12 4 (eightWires) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma eightStart_5 : ProofTable.matched 12 5 (eightWires) = true := by decide +kernel

lemma eight : ∀ t ≤ 5, Impossible 12 t (eightWires) := by

  intro t small

  have ok : ProofTable.matched 12 t (eightWires) = true := by
    interval_cases t

    · exact eightStart_0

    · exact eightStart_1

    · exact eightStart_2

    · exact eightStart_3

    · exact eightStart_4

    · exact eightStart_5

  exact ProofTable.matchedImpossible (fun i hi => ProofTable.sound 12 (by decide) t (by omega) i hi) ok

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ordinaryEightStart_0 : ProofTable.matched 12 0 (ordinaryEightWires) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ordinaryEightStart_1 : ProofTable.matched 12 1 (ordinaryEightWires) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ordinaryEightStart_2 : ProofTable.matched 12 2 (ordinaryEightWires) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ordinaryEightStart_3 : ProofTable.matched 12 3 (ordinaryEightWires) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ordinaryEightStart_4 : ProofTable.matched 12 4 (ordinaryEightWires) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ordinaryEightStart_5 : ProofTable.matched 12 5 (ordinaryEightWires) = true := by decide +kernel

lemma ordinaryEight : ∀ t ≤ 5, Impossible 12 t (ordinaryEightWires) := by

  intro t small

  have ok : ProofTable.matched 12 t (ordinaryEightWires) = true := by
    interval_cases t

    · exact ordinaryEightStart_0

    · exact ordinaryEightStart_1

    · exact ordinaryEightStart_2

    · exact ordinaryEightStart_3

    · exact ordinaryEightStart_4

    · exact ordinaryEightStart_5

  exact ProofTable.matchedImpossible (fun i hi => ProofTable.sound 12 (by decide) t (by omega) i hi) ok

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma mainStart_1 : ProofTable.matched 14 1 (fullWires) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma mainStart_2 : ProofTable.matched 14 2 (fullWires) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma mainStart_3 : ProofTable.matched 14 3 (fullWires) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma mainStart_4 : ProofTable.matched 14 4 (fullWires) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma mainStart_5 : ProofTable.matched 14 5 (fullWires) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma mainStart_6 : ProofTable.matched 14 6 (fullWires) = true := by decide +kernel

lemma main : ∀ t, 0 < t → t ≤ 6 → Impossible 14 t (fullWires) := by

  intro t pos small

  have ok : ProofTable.matched 14 t (fullWires) = true := by
    interval_cases t

    · exact mainStart_1

    · exact mainStart_2

    · exact mainStart_3

    · exact mainStart_4

    · exact mainStart_5

    · exact mainStart_6

  exact ProofTable.matchedImpossible (fun i hi => ProofTable.sound 14 (by decide) t (by omega) i hi) ok

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ordinaryMainStart_0 : ProofTable.matched 14 0 (rootWires) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ordinaryMainStart_1 : ProofTable.matched 14 1 (rootWires) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ordinaryMainStart_2 : ProofTable.matched 14 2 (rootWires) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ordinaryMainStart_3 : ProofTable.matched 14 3 (rootWires) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ordinaryMainStart_4 : ProofTable.matched 14 4 (rootWires) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ordinaryMainStart_5 : ProofTable.matched 14 5 (rootWires) = true := by decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma ordinaryMainStart_6 : ProofTable.matched 14 6 (rootWires) = true := by decide +kernel

lemma ordinaryMain : ∀ t ≤ 6, Impossible 14 t (rootWires) := by

  intro t small

  have ok : ProofTable.matched 14 t (rootWires) = true := by
    interval_cases t

    · exact ordinaryMainStart_0

    · exact ordinaryMainStart_1

    · exact ordinaryMainStart_2

    · exact ordinaryMainStart_3

    · exact ordinaryMainStart_4

    · exact ordinaryMainStart_5

    · exact ordinaryMainStart_6

  exact ProofTable.matchedImpossible (fun i hi => ProofTable.sound 14 (by decide) t (by omega) i hi) ok

end VerifiedRows

lemma thetaOriginalBound : smallerBound 10 thetaOriginalBits :=
  tableLower thetaOriginalBits (bare thetaOriginalBits) (fun _ => .tNone) 10 4 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (bareRep _ (by decide +kernel)) (fun _ _ _ h => bareConstrain _ _ _ h) (VerifiedRows.thetaOriginal)


lemma theta3Bound : smallerBound 10 theta3Bits :=
  tableLower theta3Bits (bare theta3Bits) (fun _ => .tNone) 10 4 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (bareRep _ (by decide +kernel)) (fun _ _ _ h => bareConstrain _ _ _ h) (VerifiedRows.theta3)


lemma theta6Bound : smallerBound 10 theta6Bits :=
  tableLower theta6Bits (bare theta6Bits) (fun _ => .tNone) 10 4 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (bareRep _ (by decide +kernel)) (fun _ _ _ h => bareConstrain _ _ _ h) (VerifiedRows.theta6)


lemma theta7Bound : smallerBound 10 theta7Bits :=
  tableLower theta7Bits (bare theta7Bits) (fun _ => .tNone) 10 4 (by decide)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (bareRep _ (by decide +kernel)) (fun _ _ _ h => bareConstrain _ _ _ h) (VerifiedRows.theta7)


lemma eightBound : smallerBound 12 eightBits :=
  tableLower eightBits eightWires eightTag 12 5 (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) eightRep
    (fun k hk t hl => VariableProjection.restrict_live hl (eightTagOk thetaOriginalBound theta6Bound theta3Bound hk)) (VerifiedRows.eight)


lemma ordinaryEightBound : smallerBound 12 ordinaryEightBits :=
  tableLower ordinaryEightBits ordinaryEightWires ordinaryEightTag 12 5 (by decide) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ordinaryEightRep
    (fun k hk t hl => VariableProjection.restrict_live hl (ordinaryEightTagOk thetaOriginalBound hk)) (VerifiedRows.ordinaryEight)


set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma originalThetaTable : thetaInputs = thetaOriginalBits := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma signedThetaSix : signedThetaAt 6 = theta6Bits := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma signedThetaSeven : signedThetaAt 7 = theta7Bits := by decide +kernel
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma signedEightTable : signedEight = eightBits := by decide +kernel

lemma root_project4_impossible : ¬ Feasible homProject4 12 raw.toFinset := by
  apply fromMinor _ _ ordinaryEightBits _ _ ordinaryEightBound
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma bit232_unique : raw.all (fun a => decide (a = raw4) || !(sep true (project0 a)).testBit 232) = true := by
  decide +kernel
lemma root_project0_impossible : ¬ Feasible homProject0 11 raw.toFinset := by
  rintro ⟨m, hm, t, T, hl, hsub⟩
  have h4 : project0 raw4 ∈ T := by
    obtain ⟨x, hxT, hsep⟩ := live_sep hl 232 (by omega)
    obtain ⟨a, haRaw, rfl⟩ := Finset.mem_image.mp (hsub hxT)
    have hsw := sep_weaken t (live_proper hl _ hxT).1 232 (by omega) hsep
    have hall := List.all_eq_true.mp bit232_unique a (List.mem_toFinset.mp haRaw)
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hall
    rcases hall with rfl | hf
    · exact hxT
    · exact False.elim (by rw [hsw] at hf; contradiction)
  have hz4 : ¬ proper (homProjectLeaf.fn (project0 raw4)) := fun hp =>
    hp.2.1 projectLeaf_project0_raw4
  obtain ⟨q, hq, m', hm', t', T', hl', hT'⟩ := feasible_const hl homProjectLeaf (project0 raw4) h4 hz4
  have hsubTheta : ∀ a ∈ T', a ∈ thetaInputs := by
    intro a ha
    obtain ⟨b, hbT, rfl⟩ := Finset.mem_image.mp (hT' ha)
    obtain ⟨c, hcRaw, rfl⟩ := Finset.mem_image.mp (hsub hbT)
    have hcm := List.mem_toFinset.mp hcRaw
    by_cases hc0 : c = raw0
    · subst c
      have h0 : projectLeaf (project0 raw0) = zero := by
        rw [project0_raw0]; exact homProjectLeaf.hzero
      exact False.elim ((live_proper hl' _ ha).2.1 h0)
    by_cases hc4 : c = raw4
    · subst c
      exact False.elim ((live_proper hl' _ ha).2.1 projectLeaf_project0_raw4)
    · have hmem : c ∈ thetaOrder := by
        simp only [raw, thetaOrder, List.mem_cons, List.not_mem_nil, or_false] at hcm ⊢
        rcases hcm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
      exact List.mem_map_of_mem hmem
  rw [originalThetaTable] at hsubTheta
  exact thetaOriginalBound m' (by omega) t' T' hl' hsubTheta

lemma root_project_deg2 (i : Fin 9) (hi : i.val = 4 ∨ i.val = 6 ∨ i.val = 7) :
    ¬ Feasible (homProject i) 12 raw.toFinset := by
  intro h
  apply root_project4_impossible
  obtain ⟨m, hm, t, T, hl, hsub⟩ := h
  refine ⟨m, hm, t, T, hl, ?_⟩
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (hsub hx)
  simp only [homProject, hi, ite_true, compHom]
  exact Finset.mem_image_of_mem _ (action_raw_subset (gOfV i) (Finset.mem_image_of_mem _ ha))
lemma root_project_deg3 (i : Fin 9) (hi : ¬ (i.val = 4 ∨ i.val = 6 ∨ i.val = 7)) :
    ¬ Feasible (homProject i) 11 raw.toFinset := by
  intro h
  apply root_project0_impossible
  obtain ⟨m, hm, t, T, hl, hsub⟩ := h
  refine ⟨m, hm, t, T, hl, ?_⟩
  intro x hx
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp (hsub hx)
  simp only [homProject, hi, ite_false, compHom]
  exact Finset.mem_image_of_mem _ (action_raw_subset (gOfV i) (Finset.mem_image_of_mem _ ha))

lemma rootTag_ok {k : Nat} (hk : k ≤ 14) : TagOk k raw.toFinset rootTag := by
  intro a ha
  have hm := List.mem_toFinset.mp ha
  have checkV (i : Fin 9) (heq : a = raw.getD i.val zero) : WireTagOk k raw.toFinset a (rootTag a) := by
    subst heq
    have hpz := project_raw_zero i
    fin_cases i
    · have hrt : rootTag (raw.getD 0 zero) = .tDeg3 := by decide +kernel
      rw [hrt]; exact ⟨0, hpz, fun q hq hf => root_project_deg3 0 (by decide) (feasible_mono hf (by omega))⟩
    · have hrt : rootTag (raw.getD 1 zero) = .tDeg3 := by decide +kernel
      rw [hrt]; exact ⟨1, hpz, fun q hq hf => root_project_deg3 1 (by decide) (feasible_mono hf (by omega))⟩
    · have hrt : rootTag (raw.getD 2 zero) = .tDeg3 := by decide +kernel
      rw [hrt]; exact ⟨2, hpz, fun q hq hf => root_project_deg3 2 (by decide) (feasible_mono hf (by omega))⟩
    · have hrt : rootTag (raw.getD 3 zero) = .tDeg3 := by decide +kernel
      rw [hrt]; exact ⟨3, hpz, fun q hq hf => root_project_deg3 3 (by decide) (feasible_mono hf (by omega))⟩
    · have hrt : rootTag (raw.getD 4 zero) = .tSpec0 := by decide +kernel
      rw [hrt]; exact ⟨4, hpz, fun q hq hf => root_project_deg2 4 (by decide) (feasible_mono hf (by omega))⟩
    · have hrt : rootTag (raw.getD 5 zero) = .tDeg3 := by decide +kernel
      rw [hrt]; exact ⟨5, hpz, fun q hq hf => root_project_deg3 5 (by decide) (feasible_mono hf (by omega))⟩
    · have hrt : rootTag (raw.getD 6 zero) = .tSpec0 := by decide +kernel
      rw [hrt]; exact ⟨6, hpz, fun q hq hf => root_project_deg2 6 (by decide) (feasible_mono hf (by omega))⟩
    · have hrt : rootTag (raw.getD 7 zero) = .tSpec0 := by decide +kernel
      rw [hrt]; exact ⟨7, hpz, fun q hq hf => root_project_deg2 7 (by decide) (feasible_mono hf (by omega))⟩
    · have hrt : rootTag (raw.getD 8 zero) = .tDeg3 := by decide +kernel
      rw [hrt]; exact ⟨8, hpz, fun q hq hf => root_project_deg3 8 (by decide) (feasible_mono hf (by omega))⟩
  simp only [raw, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact checkV 0 rfl
  · exact checkV 1 rfl
  · exact checkV 2 rfl
  · exact checkV 3 rfl
  · exact checkV 4 rfl
  · exact checkV 5 rfl
  · exact checkV 6 rfl
  · exact checkV 7 rfl
  · exact checkV 8 rfl

lemma rootWires_rep : Represents rootWires raw.toFinset rootTag := by
  refine ⟨raw_nd, rfl, ?_⟩
  intro w hw
  simp only [rootWires, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

lemma neg4Valid : Valid (neg raw4) := valid_neg (raw_valid raw4 (by simp [raw]))
lemma signedSubset : signedRaw.toFinset ⊆ insert (neg raw4) raw.toFinset := by
  intro a ha
  simp [signedRaw] at ha
  simp [raw]
  tauto
lemma signedValid (a : Sig) (ha : a ∈ signedRaw) : Valid a := by
  obtain e | hm := Finset.mem_insert.mp (signedSubset (List.mem_toFinset.mpr ha))
  · exact e ▸ neg4Valid
  · exact raw_valid a (List.mem_toFinset.mp hm)
lemma signedNecessary {k t S} (l : Live k t S) (hs : ∀ a ∈ S, a ∈ signedRaw) :
    signedRaw.toFinset = S := by
  have every : signedRaw.all (fun a => unionSep true (signedRaw.erase a) != top) = true := by decide +kernel
  ext a
  rw [List.mem_toFinset]
  refine ⟨fun hr => ?_, hs a⟩
  by_contra hn
  have fail := List.all_eq_true.mp every a hr
  have cov : unionSep true (signedRaw.erase a) = top := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [testBit_top]
    by_cases hi : i < 414
    · simp only [hi,decide_true]
      obtain ⟨b,hb,h⟩ := live_sep l i hi
      have ba : b ≠ a := fun he => hn (he ▸ hb)
      have hm := (List.mem_erase_of_ne ba).mpr (hs _ hb)
      exact (mem_unionSep true _ _).2 ⟨b,hm,sep_weaken _ (live_proper l b hb).1 i hi h⟩
    · simp only [hi,decide_false]
      exact valid_unionSep (fun x hx => signedValid x (List.mem_of_mem_erase hx)) i (by omega)
  simp [cov] at fail
lemma projectNotFour : (homProject (4 : Fin 9)).fn (neg raw4) = one := by
  rw [(homProject (4 : Fin 9)).hneg (raw_valid raw4 (by simp [raw]))]
  have h : (homProject (4 : Fin 9)).fn raw4 = zero := project_raw_zero 4
  rw [h,neg_laws.1]
lemma projectDropConstant {S : Finset Sig} (hs : S ⊆ insert (neg raw4) raw.toFinset)
    {q : Nat} (h : Feasible (homProject (4 : Fin 9)) q S) :
    Feasible (homProject (4 : Fin 9)) q raw.toFinset := by
  obtain ⟨m,hm,t,U,live,sub⟩ := h
  refine ⟨m,hm,t,U,live,?_⟩
  intro z hz
  obtain ⟨s,hs',rfl⟩ := Finset.mem_image.mp (sub hz)
  obtain rfl | hr := Finset.mem_insert.mp (hs hs')
  · exact False.elim ((live_proper live _ hz).2.2 projectNotFour)
  · exact Finset.mem_image_of_mem _ hr
lemma projectPayNot (i : Fin 9) (q : Nat) (h : Feasible (homProject i) q signedRaw.toFinset) :
    Feasible (homProject i) (q + 1) raw.toFinset := by
  apply feasible_pull (g := neg raw4) signedSubset _ h
  rw [(homProject i).hneg (raw_valid raw4 (by simp [raw]))]
  exact neg_rep _ ((homProject i).valid raw4)
    (Finset.mem_toList.mpr (Finset.mem_image_of_mem _ (by simp [raw])))
set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma signedZeroImpossible : ¬ Feasible homProject0 11 signedRaw.toFinset := by
  rintro ⟨m,hm,t,T,active,sub⟩
  have uniqueBit : signedRaw.all
      (fun a => decide (a = neg raw4) || !(sep true (project0 a)).testBit 232) = true := by
    decide +kernel
  have leaf : project0 (neg raw4) ∈ T := by
    obtain ⟨x,hx,hdiff⟩ := live_sep active 232 (by omega)
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (sub hx)
    have sepAt := sep_weaken t (live_proper active _ hx).1 232 (by omega) hdiff
    have only := List.all_eq_true.mp uniqueBit a (List.mem_toFinset.mp ha)
    simp only [Bool.or_eq_true,decide_eq_true_eq,Bool.not_eq_true'] at only
    obtain rfl | wrong := only
    · exact hx
    · exact False.elim (Bool.false_ne_true (wrong.symm.trans sepAt))
  have leafOne : projectLeaf (project0 (neg raw4)) = one := by
    calc
      projectLeaf (project0 (neg raw4)) = projectLeaf (neg (project0 raw4)) :=
        congrArg projectLeaf (homProject0.hneg (raw_valid raw4 (by simp [raw])))
      _ = neg (projectLeaf (project0 raw4)) := homProjectLeaf.hneg (homProject0.valid raw4)
      _ = one := by rw [projectLeaf_project0_raw4,neg_laws.1]
  obtain ⟨q,hq,m',hm',t',T',live,sub'⟩ :=
    feasible_const active homProjectLeaf (project0 (neg raw4)) leaf (fun hp => hp.2.2 leafOne)
  have thetaSub : ∀ a ∈ T', a ∈ thetaInputs := by
    intro a ha
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp (sub' ha)
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp (sub hb)
    have hcm := List.mem_toFinset.mp hc
    by_cases h0 : c = raw0
    · subst c
      have z : projectLeaf (project0 raw0) = zero := by
        rw [project0_raw0]; exact homProjectLeaf.hzero
      exact False.elim ((live_proper live _ ha).2.1 z)
    by_cases h4 : c = neg raw4
    · subst c
      exact False.elim ((live_proper live _ ha).2.2 leafOne)
    · have mem : c ∈ thetaOrder := by
        simp only [signedRaw,thetaOrder,List.mem_cons,List.not_mem_nil,or_false] at hcm ⊢
        rcases hcm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all
      exact List.mem_map_of_mem mem
  rw [originalThetaTable] at thetaSub
  exact thetaOriginalBound m' (by omega) t' T' live thetaSub

lemma signedAction {g : Fin 12} (fixes : rawImage g 4 = raw4) :
    signedRaw.toFinset.image (action g) ⊆ signedRaw.toFinset := by
  have fixed : action g raw4 = raw4 := (rawImage_eq g 4).symm.trans fixes
  have sets : signedRaw.toFinset = insert (neg raw4) (raw.toFinset.erase raw4) := by decide +kernel
  rw [sets]
  intro z hz
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
  obtain rfl | h := Finset.mem_insert.mp ha
  · rw [action_neg g (raw_valid raw4 (by simp [raw])),fixed]
    exact Finset.mem_insert_self _ _
  · obtain ⟨ne,hm⟩ := Finset.mem_erase.mp h
    apply Finset.mem_insert_of_mem
    apply Finset.mem_erase.mpr
    refine ⟨?_,action_raw_subset g (Finset.mem_image_of_mem _ hm)⟩
    intro he
    exact ne (action_inj (raw_valid _ (List.mem_toFinset.mp hm))
      (raw_valid raw4 (by simp [raw])) (he.trans fixed.symm))
lemma neighborImpossible (i : Fin 9) (hi : i = 0 ∨ i = 3) :
    ¬ Feasible (homProject i) 11 signedRaw.toFinset := by
  intro h
  have degree : ¬(i.val = 4 ∨ i.val = 6 ∨ i.val = 7) := by
    obtain rfl | rfl := hi <;> decide
  have fixed : rawImage (gOfV i) 4 = raw4 := by
    obtain rfl | rfl := hi <;> decide +kernel
  obtain ⟨m,hm,t,T,live,sub⟩ := h
  apply signedZeroImpossible
  refine ⟨m,hm,t,T,live,?_⟩
  intro z hz
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (sub hz)
  simp only [homProject,degree,ite_false,compHom]
  exact Finset.mem_image_of_mem _ (signedAction fixed (Finset.mem_image_of_mem _ ha))

lemma signedPositiveT {k t : Nat} (l : Live k t signedRaw.toFinset) : 0 < t := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · have cover := live_cover l (v := signedRaw) rfl
    have neq : unionSep false signedRaw ≠ top := by decide +kernel
    exact False.elim (neq cover)
  · exact ht
lemma splitRails (tail : List Gate)
    (legal : ∀ g ∈ tail, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (small : tail.length ≤ 14) (reached : target ∈ execute tail (raw ++ [neg raw4])) :
    ∃ k ≤ 14, ∃ t, 0 < t ∧ t ≤ 6 ∧ Live k t signedRaw.toFinset := by
  have valid : ∀ z ∈ raw ++ [neg raw4], Valid z := by
    intro z hz
    obtain hm | he := List.mem_append.mp hz
    · exact raw_valid z hm
    · obtain rfl := List.mem_singleton.mp he
      exact neg4Valid
  obtain ⟨k,t,S,hk,live,sub⟩ := extract tail _ valid legal reached
  have bound := hk.trans small
  by_cases hn : neg raw4 ∈ S
  · by_cases hp : raw4 ∈ S
    · have z : (homProject (4 : Fin 9)).fn raw4 = zero := project_raw_zero 4
      have neq : raw4 ≠ neg raw4 := by decide +kernel
      obtain ⟨q,hq,hf⟩ := feasible_two_consts live (homProject (4 : Fin 9)) raw4 (neg raw4)
        hp hn neq (fun h => h.2.1 z) (fun h => h.2.2 projectNotFour)
      have sub' : S ⊆ insert (neg raw4) raw.toFinset := by
        intro s hs
        obtain hr | he := List.mem_append.mp (sub s hs)
        · exact Finset.mem_insert_of_mem (List.mem_toFinset.mpr hr)
        · exact Finset.mem_insert.mpr (Or.inl (List.mem_singleton.mp he))
      exact False.elim (root_project_deg2 4 (by decide)
        (feasible_mono (projectDropConstant sub' hf) (by omega)))
    · have sub' : ∀ s ∈ S, s ∈ signedRaw := by
        intro s hs
        have ne : s ≠ raw4 := fun h => hp (h ▸ hs)
        obtain hr | he := List.mem_append.mp (sub s hs)
        · simp only [raw,List.mem_cons,List.not_mem_nil,or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp_all [signedRaw]
        · obtain rfl := List.mem_singleton.mp he
          simp [signedRaw]
      have eq := signedNecessary live sub'
      subst S
      have sz := live_size live
      have card : signedRaw.toFinset.card = 9 := by decide +kernel
      exact ⟨k,bound,t,signedPositiveT live,by omega,live⟩
  · have sub' : ∀ s ∈ S, s ∈ raw := by
      intro s hs
      obtain hr | he := List.mem_append.mp (sub s hs)
      · exact hr
      · exact False.elim (hn ((List.mem_singleton.mp he) ▸ hs))
    have eq := necessary live sub'
    subst S
    have sz := live_size live
    rw [List.toFinset_card_of_nodup raw_nd] at sz
    have nine : raw.length = 9 := rfl
    exact False.elim (VerifiedRows.ordinaryMain t (by omega) k bound _ _ rootWires_rep
      (restrict_live live (rootTag_ok bound)))



lemma rotateSources {g : Fin 12} {j : Fin 9} (mapped : rawImage g 4 = raw.getD j.val zero) :
    signedRaw.toFinset.image (action g) ⊆ (sourcesAt j).toFinset := by
  have rotated : action g raw4 = raw.getD j.val zero := (rawImage_eq g 4).symm.trans mapped
  have asSet : signedRaw.toFinset = insert (neg raw4) (raw.toFinset.erase raw4) := by decide +kernel
  intro z hz
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hz
  rw [asSet] at ha
  obtain rfl | other := Finset.mem_insert.mp ha
  · rw [action_neg g (raw_valid raw4 (by simp [raw])),rotated]
    exact List.mem_toFinset.mpr (List.mem_append_right _ (by simp))
  · obtain ⟨ne,hm⟩ := Finset.mem_erase.mp other
    have different : action g a ≠ raw.getD j.val zero := fun he =>
      ne (action_inj (raw_valid _ (List.mem_toFinset.mp hm))
        (raw_valid raw4 (by simp [raw])) (he.trans rotated.symm))
    have present := List.mem_toFinset.mp (action_raw_subset g (Finset.mem_image_of_mem _ hm))
    exact List.mem_toFinset.mpr (List.mem_append_left _ ((List.mem_erase_of_ne different).mpr present))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
lemma remoteProjected (j : Fin 9) (typeJ : j = 6 ∨ j = 7)
    (bound : smallerBound 10 (signedThetaAt j)) : ¬ Feasible homProject0 11 (sourcesAt j).toFinset := by
  rintro ⟨m,hm,t,T,live,sub⟩
  have uniqueBit : (sourcesAt j).all
      (fun a => decide (a = raw4) || !(sep true (project0 a)).testBit 232) = true := by
    rcases typeJ with rfl | rfl <;> decide +kernel
  have required : project0 raw4 ∈ T := by
    obtain ⟨x,hx,hdiff⟩ := live_sep live 232 (by omega)
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (sub hx)
    have sepAt := sep_weaken t (live_proper live _ hx).1 232 (by omega) hdiff
    have only := List.all_eq_true.mp uniqueBit a (List.mem_toFinset.mp ha)
    simp only [Bool.or_eq_true,decide_eq_true_eq,Bool.not_eq_true'] at only
    obtain rfl | wrong := only
    · exact hx
    · exact False.elim (Bool.false_ne_true (wrong.symm.trans sepAt))
  obtain ⟨q,hq,m',hm',t',U,active,sub'⟩ :=
    feasible_const live homProjectLeaf (project0 raw4) required (fun hp => hp.2.1 projectLeaf_project0_raw4)
  have remaining : (sourcesAt j).all
      (fun a => decide (a = raw0 ∨ a = raw4 ∨ a ∈ thetaOrder.map (valueAt j))) = true := by
    rcases typeJ with rfl | rfl <;> decide +kernel
  apply bound m' (by omega) t' U active
  intro a ha
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp (sub' ha)
  obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp (sub hb)
  obtain rfl | rfl | present := of_decide_eq_true (List.all_eq_true.mp remaining c (List.mem_toFinset.mp hc))
  · have z : projectLeaf (project0 raw0) = zero := by
      rw [project0_raw0]; exact homProjectLeaf.hzero
    exact False.elim ((live_proper active _ ha).2.1 z)
  · exact False.elim ((live_proper active _ ha).2.1 projectLeaf_project0_raw4)
  · exact List.mem_map_of_mem present

lemma remoteImpossible (i : Fin 9) (hi : i = 1 ∨ i = 2 ∨ i = 5 ∨ i = 8)
    (h6 : smallerBound 10 (signedThetaAt 6)) (h7 : smallerBound 10 (signedThetaAt 7)) :
    ¬ Feasible (homProject i) 11 signedRaw.toFinset := by
  have degree : ¬(i.val = 4 ∨ i.val = 6 ∨ i.val = 7) := by
    rcases hi with rfl | rfl | rfl | rfl <;> decide
  have existsImage : ∃ j : Fin 9, (j = 6 ∨ j = 7) ∧ rawImage (gOfV i) 4 = raw.getD j.val zero := by
    rcases hi with rfl | rfl | rfl | rfl
    · exact ⟨6,Or.inl rfl,by decide +kernel⟩
    · exact ⟨7,Or.inr rfl,by decide +kernel⟩
    · exact ⟨6,Or.inl rfl,by decide +kernel⟩
    · exact ⟨7,Or.inr rfl,by decide +kernel⟩
  obtain ⟨j,hj,mapped⟩ := existsImage
  have lower : smallerBound 10 (signedThetaAt j) := by
    obtain rfl | rfl := hj
    · exact h6
    · exact h7
  rintro ⟨m,hm,t,T,live,sub⟩
  apply remoteProjected j hj lower
  refine ⟨m,hm,t,T,live,?_⟩
  intro z hz
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (sub hz)
  simp only [homProject,degree,ite_false,compHom]
  exact Finset.mem_image_of_mem _ (rotateSources mapped (Finset.mem_image_of_mem _ ha))

lemma otherDegreeTwo (i : Fin 9) (hi : i = 6 ∨ i = 7) (h8 : smallerBound 12 signedEight) :
    ¬ Feasible (homProject i) 12 signedRaw.toFinset := by
  have degree : i.val = 4 ∨ i.val = 6 ∨ i.val = 7 := by
    rcases hi with rfl | rfl <;> decide
  have mapped : rawImage (gOfV i) 4 = raw.getD 6 zero := by
    rcases hi with rfl | rfl <;> decide +kernel
  have complete : (sourcesAt 6).all
      (fun a => decide (a = raw4 ∨ a ∈ raw1007Order.map (valueAt 6))) = true := by decide +kernel
  rintro ⟨m,hm,t,T,live,sub⟩
  apply h8 m hm t T live
  intro z hz
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp (sub hz)
  simp only [homProject,degree,ite_true,compHom]
  have present := List.mem_toFinset.mp (rotateSources (g := gOfV i) (j := 6) mapped (Finset.mem_image_of_mem _ ha))
  obtain e | keep := of_decide_eq_true (List.all_eq_true.mp complete _ present)
  · have dead : (homProject i).fn a = zero := by
      simp only [homProject,degree,ite_true,compHom]
      change project4 (action (gOfV i) a) = zero
      rw [e]
      exact project4_raw4
    exact False.elim ((live_proper live _ hz).2.1 dead)
  · exact List.mem_map_of_mem keep


lemma fullRep : Represents fullWires signedRaw.toFinset fullTag := by
  refine ⟨by decide +kernel,rfl,?_⟩
  intro w hw
  simp only [fullWires,List.mem_cons,List.not_mem_nil,or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

lemma fullTagOk (h6 : smallerBound 10 (signedThetaAt 6)) (h7 : smallerBound 10 (signedThetaAt 7))
    (h8 : smallerBound 12 signedEight) {k : Nat} (budget : k ≤ 14) : TagOk k signedRaw.toFinset fullTag := by
  have degree3 (i : Fin 9) (htag : fullTag (raw.getD i.val zero) = .tDeg3)
      (hmin : ¬ Feasible (homProject i) 11 signedRaw.toFinset) :
      WireTagOk k signedRaw.toFinset (raw.getD i.val zero) (fullTag (raw.getD i.val zero)) := by
    rw [htag]
    exact ⟨i,project_raw_zero i,fun q hq hf => hmin (feasible_mono hf (by omega))⟩
  have degree2 (i : Fin 9) (htag : fullTag (raw.getD i.val zero) = .tSpec0) (typeI : i=6 ∨ i=7) :
      WireTagOk k signedRaw.toFinset (raw.getD i.val zero) (fullTag (raw.getD i.val zero)) := by
    rw [htag]
    exact ⟨i,project_raw_zero i,fun q hq hf => otherDegreeTwo i typeI h8 (feasible_mono hf (by omega))⟩
  intro a ha
  simp only [signedRaw,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact degree3 0 (by decide +kernel) (neighborImpossible 0 (by decide))
  · exact degree3 1 (by decide +kernel) (remoteImpossible 1 (by decide) h6 h7)
  · exact degree3 2 (by decide +kernel) (remoteImpossible 2 (by decide) h6 h7)
  · exact degree3 3 (by decide +kernel) (neighborImpossible 3 (by decide))
  · have e : fullTag (neg raw4) = .tSpec1 := by decide +kernel
    rw [e]
    exact ⟨4,projectNotFour,fun q hq hf =>
      root_project_deg2 4 (by decide) (feasible_mono (projectDropConstant signedSubset hf) (by omega))⟩
  · exact degree3 5 (by decide +kernel) (remoteImpossible 5 (by decide) h6 h7)
  · exact degree2 6 (by decide +kernel) (by decide)
  · exact degree2 7 (by decide +kernel) (by decide)
  · exact degree3 8 (by decide +kernel) (remoteImpossible 8 (by decide) h6 h7)



lemma deskBridge (h6 : smallerBound 10 (signedThetaAt 6)) (h7 : smallerBound 10 (signedThetaAt 7))
    (h8 : smallerBound 12 signedEight) (hRoot : ∀ t,0 < t → t ≤ 6 → Impossible 14 t fullWires) :
  ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate), x1.length = (15 : ℕ) → x1.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [(4 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } → (∀ (x4 : Fin x1.length), (∃ (x5 : ℕ) (x6 : ℕ), x5 ≤ x6 ∧ x6 ≤ (9 : ℕ) + ↑x4 ∧ (x1.get x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∨ x1.get x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate })) ∨ ∃ x5 ≤ (9 : ℕ) + ↑x4, x1.get x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [x5] : PEqualNP.CircuitLowerBounds.Gate }) → ∃ (x5 : Fin (9 : ℕ) → Bool), { gates := x1, output := (23 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x5) ≠ (fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) x5 := by
  intro gs len head gates
  by_contra! implementsTarget
  cases gs with
  | nil => simp at len
  | cons g tail =>
    have eg : g = (⟨.not,[4]⟩ : Gate) := Option.some.inj head
    subst g
    let C : Circuit := ⟨(⟨.not,[4]⟩ : Gate)::tail,23⟩
    have fan : PEqualNP.MetaComplexity.FanInTwo C := by
      intro g hg
      obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hg
      obtain ⟨a,b,_,_,e | e⟩ | ⟨a,_,e⟩ := gates i
      · change _ = _ at e
        rw [show C.gates.get i = _ from e]
        simp
      · rw [show C.gates.get i = _ from e]
        simp
      · rw [show C.gates.get i = _ from e]
        simp
    have reached := circuit_target C fan (fun x => implementsTarget x)
    change target ∈ execute tail (raw ++ [gv raw (⟨.not,[4]⟩ : Gate)]) at reached
    have value : gv raw (⟨.not,[4]⟩ : Gate) = neg raw4 := by decide +kernel
    rw [value] at reached
    obtain ⟨k,hk,t,pos,ht,base⟩ := splitRails tail
      (fun g hg => fan g (List.mem_cons_of_mem _ hg)) (by simp only [List.length_cons] at len; omega) reached
    exact hRoot t pos ht k hk _ _ fullRep (restrict_live base (fullTagOk h6 h7 h8 hk))



lemma verifiedDesk : ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate), x1.length = (15 : ℕ) → x1.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [(4 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } → (∀ (x4 : Fin x1.length), (∃ (x5 : ℕ) (x6 : ℕ), x5 ≤ x6 ∧ x6 ≤ (9 : ℕ) + ↑x4 ∧ (x1.get x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∨ x1.get x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate })) ∨ ∃ x5 ≤ (9 : ℕ) + ↑x4, x1.get x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [x5] : PEqualNP.CircuitLowerBounds.Gate }) → ∃ (x5 : Fin (9 : ℕ) → Bool), { gates := x1, output := (23 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x5) ≠ (fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) x5 := by
  apply deskBridge
  · rw [signedThetaSix]; exact theta6Bound
  · rw [signedThetaSeven]; exact theta7Bound
  · rw [signedEightTable]; exact eightBound
  · exact VerifiedRows.main

end PEqualNP.Outside.L_meta_1920

theorem PEqualNP.Outside.L_meta_1920 :
  ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate), x1.length = (15 : ℕ) → x1.head? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [(4 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } → (∀ (x4 : Fin x1.length), (∃ (x5 : ℕ) (x6 : ℕ), x5 ≤ x6 ∧ x6 ≤ (9 : ℕ) + ↑x4 ∧ (x1.get x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate } ∨ x1.get x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x5, x6] : PEqualNP.CircuitLowerBounds.Gate })) ∨ ∃ x5 ≤ (9 : ℕ) + ↑x4, x1.get x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.not, inputs := [x5] : PEqualNP.CircuitLowerBounds.Gate }) → ∃ (x5 : Fin (9 : ℕ) → Bool), { gates := x1, output := (23 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.eval (List.ofFn x5) ≠ (fun (x6 : Fin (9 : ℕ) → Bool) => x6 (0 : Fin (9 : ℕ)) && x6 (1 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (2 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (3 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (4 : Fin (9 : ℕ)) || x6 (4 : Fin (9 : ℕ)) && x6 (0 : Fin (9 : ℕ)) || x6 (0 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ)) || x6 (1 : Fin (9 : ℕ)) && x6 (6 : Fin (9 : ℕ)) || x6 (2 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (3 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (5 : Fin (9 : ℕ)) && x6 (7 : Fin (9 : ℕ)) || x6 (6 : Fin (9 : ℕ)) && x6 (8 : Fin (9 : ℕ)) || x6 (8 : Fin (9 : ℕ)) && x6 (5 : Fin (9 : ℕ))) x5 :=
  PEqualNP.Outside.L_meta_1920.verifiedDesk
