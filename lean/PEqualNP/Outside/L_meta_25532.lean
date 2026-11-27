import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_25532_aux

def B (k y x : ℕ) : Bool := y.testBit (x % k)

def rot (k s bits : ℕ) : ℕ := ((bits <<< (s % k)) ||| (bits >>> (k - s % k))) % 2 ^ k

def step (k mixed : ℕ) : ℕ :=
  (List.range k).foldl (fun acc place =>
    acc ||| ((xor (mixed.testBit place)
      (!(mixed.testBit ((place + 1) % k)) && mixed.testBit ((place + 2) % k))).toNat <<< place)) 0

theorem tb_high {y k j : ℕ} (hy : y < 2 ^ k) (hj : k ≤ j) : y.testBit j = false :=
  Nat.testBit_lt_two_pow (lt_of_lt_of_le hy (Nat.pow_le_pow_right (by norm_num) hj))

theorem rot_lt (k s y : ℕ) : rot k s y < 2 ^ k := Nat.mod_lt _ (by positivity)

theorem rot_tb {k y : ℕ} (s : ℕ) (hk : 0 < k) (hy : y < 2 ^ k) {j : ℕ} (hj : j < k) :
    (rot k s y).testBit j = y.testBit ((j + k - s % k) % k) := by
  have hc : s % k < k := Nat.mod_lt _ hk
  unfold rot
  rw [Nat.testBit_mod_two_pow, Nat.testBit_or, Nat.testBit_shiftLeft, Nat.testBit_shiftRight]
  simp only [hj, decide_true, Bool.true_and]
  by_cases h : s % k ≤ j
  · have e1 : (j + k - s % k) % k = j - s % k := by
      have : j + k - s % k = (j - s % k) + k := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [e1, tb_high hy (by omega : k ≤ k - s % k + j)]
    simp [h]
  · have e1 : (j + k - s % k) % k = k - s % k + j := by
      rw [Nat.mod_eq_of_lt (by omega)]; omega
    rw [e1]
    simp [h]

theorem B_rot {k y : ℕ} (hk : 0 < k) (hy : y < 2 ^ k) (s x : ℕ) :
    B k (rot k s y) (x + s) = B k y x := by
  unfold B
  rw [rot_tb s hk hy (Nat.mod_lt _ hk)]
  congr 1
  have hc : s % k < k := Nat.mod_lt _ hk
  have h1 : ((x + s) % k + k - s % k) + s % k = (x + s) % k + k := by omega
  have h2 : ((x + s) % k + k - s % k) + s % k ≡ x + s [MOD k] := by
    rw [h1]; unfold Nat.ModEq; rw [Nat.add_mod_right, Nat.mod_mod]
  exact Nat.ModEq.add_right_cancel (Nat.mod_modEq s k) h2

theorem B_add_k (k y x : ℕ) : B k y (x + k) = B k y x := by
  unfold B; rw [Nat.add_mod_right]

theorem B_xor (k a b x : ℕ) : B k (a ^^^ b) x = xor (B k a x) (B k b x) := by
  unfold B; rw [Nat.testBit_xor]

theorem bit_tb (n j : ℕ) (b : Bool) : (b.toNat <<< n).testBit j = (decide (n = j) && b) := by
  cases b <;> simp [Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem fold_tb (f : ℕ → Bool) : ∀ n j : ℕ,
    ((List.range n).foldl (fun acc p => acc ||| ((f p).toNat <<< p)) 0).testBit j = (decide (j < n) && f j)
  | 0, j => by simp
  | n + 1, j => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Nat.testBit_or, fold_tb f n j,
      bit_tb]
    by_cases h1 : j < n
    · have h2 : n ≠ j := by omega
      simp [h1, h2, Nat.lt_succ_of_lt h1]
    · by_cases h2 : n = j
      · subst h2; simp
      · have h3 : ¬ j < n + 1 := by omega
        simp [h1, h2, h3]

theorem step_tb (k y : ℕ) (j : ℕ) : (step k y).testBit j = (decide (j < k) &&
    xor (y.testBit j) (!(y.testBit ((j + 1) % k)) && y.testBit ((j + 2) % k))) := by
  unfold step
  exact fold_tb (fun place => xor (y.testBit place)
    (!(y.testBit ((place + 1) % k)) && y.testBit ((place + 2) % k))) k j

theorem step_lt (k y : ℕ) : step k y < 2 ^ k := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rw [step_tb]
  simp [Nat.not_lt.mpr hj]

theorem B_step {k : ℕ} (hk : 0 < k) (y x : ℕ) : B k (step k y) x =
    xor (B k y x) (!(B k y (x + 1)) && B k y (x + 2)) := by
  unfold B
  rw [step_tb, Nat.mod_add_mod, Nat.mod_add_mod]
  simp [Nat.mod_lt _ hk]

def rnd (k keyv : ℕ) (constant : ℕ → Fin (2 ^ k)) (prev roundNo : ℕ) : ℕ :=
  step k (prev ^^^ rot k 1 prev ^^^ rot k (k - 1) prev) ^^^ rot k (2 * roundNo) keyv ^^^
    (constant (roundNo + 1)).val

def Z (k rowv : ℕ) (constant : ℕ → Fin (2 ^ k)) (start n : ℕ) : ℕ :=
  (List.range n).foldl (rnd k (rot k (k - 1) (start ^^^ rowv)) constant) start

theorem Z_succ (k rowv : ℕ) (constant : ℕ → Fin (2 ^ k)) (start n : ℕ) :
    Z k rowv constant start (n + 1) =
      rnd k (rot k (k - 1) (start ^^^ rowv)) constant (Z k rowv constant start n) n := by
  unfold Z; rw [List.range_succ, List.foldl_append]; rfl

theorem rnd_lt (k keyv : ℕ) (constant : ℕ → Fin (2 ^ k)) (prev n : ℕ) :
    rnd k keyv constant prev n < 2 ^ k := by
  unfold rnd
  exact Nat.xor_lt_two_pow (Nat.xor_lt_two_pow (step_lt _ _) (rot_lt _ _ _)) (constant (n + 1)).isLt

theorem Z_lt (k rowv : ℕ) (constant : ℕ → Fin (2 ^ k)) {start : ℕ} (hs : start < 2 ^ k) :
    ∀ n, Z k rowv constant start n < 2 ^ k
  | 0 => by simpa [Z] using hs
  | n + 1 => by rw [Z_succ]; exact rnd_lt _ _ _ _ _

theorem B_lin {k p : ℕ} (hk : 0 < k) (hp : p < 2 ^ k) {y : ℕ} (hy : 1 ≤ y) :
    B k (p ^^^ rot k 1 p ^^^ rot k (k - 1) p) y =
      xor (xor (B k p y) (B k p (y - 1))) (B k p (y + 1)) := by
  rw [B_xor, B_xor]
  have e1 : B k (rot k 1 p) y = B k p (y - 1) := by
    have h := B_rot hk hp 1 (y - 1)
    rwa [Nat.sub_add_cancel hy] at h
  have e2 : B k (rot k (k - 1) p) y = B k p (y + 1) := by
    have h := B_rot hk hp (k - 1) (y + 1)
    rw [show y + 1 + (k - 1) = y + k by omega, B_add_k] at h
    exact h
  rw [e1, e2]

theorem B_rnd {k p u : ℕ} (constant : ℕ → Fin (2 ^ k)) (hk : 0 < k) (hp : p < 2 ^ k) (hu : u < 2 ^ k)
    {x n : ℕ} (hx : 1 ≤ x) (hn : 2 * n ≤ x) :
    B k (rnd k (rot k (k - 1) u) constant p n) x =
      xor (xor (xor (xor (xor (B k p x) (B k p (x - 1))) (B k p (x + 1)))
        (!(xor (xor (B k p (x + 1)) (B k p x)) (B k p (x + 2))) &&
          xor (xor (B k p (x + 2)) (B k p (x + 1))) (B k p (x + 3))))
        (B k u (x + 1 - 2 * n))) (B k (constant (n + 1)).val x) := by
  have e : B k (rot k (2 * n) (rot k (k - 1) u)) x = B k u (x + 1 - 2 * n) := by
    have h1 := B_rot hk (rot_lt k (k - 1) u) (2 * n) (x - 2 * n)
    rw [Nat.sub_add_cancel hn] at h1
    have h2 := B_rot hk hu (k - 1) (x + 1 - 2 * n)
    rw [show x + 1 - 2 * n + (k - 1) = (x - 2 * n) + k by omega, B_add_k] at h2
    rw [h1, h2]
  unfold rnd
  rw [B_xor, B_xor, B_step hk, B_lin hk hp hx, B_lin hk hp (by omega : 1 ≤ x + 1),
    B_lin hk hp (by omega : 1 ≤ x + 2), e]
  rw [show x + 1 - 1 = x by omega, show x + 1 + 1 = x + 2 by omega, show x + 2 - 1 = x + 1 by omega,
    show x + 2 + 1 = x + 3 by omega]

theorem bool4 (c a a' e : Bool) : xor (xor c a) e = xor (xor (xor c a') e) (xor a a') := by
  cases c <;> cases a <;> cases a' <;> cases e <;> rfl

theorem rnd_agree {k p p' u u' : ℕ} (constant : ℕ → Fin (2 ^ k)) (hk : 0 < k) (hp : p < 2 ^ k)
    (hp' : p' < 2 ^ k) (hu : u < 2 ^ k) (hu' : u' < 2 ^ k) {x n : ℕ} (hx : 1 ≤ x) (hn : 2 * n ≤ x)
    (h : ∀ y, x ≤ y + 1 → y ≤ x + 3 → B k p y = B k p' y) :
    B k (rnd k (rot k (k - 1) u) constant p n) x =
      xor (B k (rnd k (rot k (k - 1) u') constant p' n) x)
        (xor (B k u (x + 1 - 2 * n)) (B k u' (x + 1 - 2 * n))) := by
  rw [B_rnd constant hk hp hu hx hn, B_rnd constant hk hp' hu' hx hn,
    h (x - 1) (by omega) (by omega), h x (by omega) (by omega), h (x + 1) (by omega) (by omega),
    h (x + 2) (by omega) (by omega), h (x + 3) (by omega) (by omega)]
  exact bool4 _ _ _ _

theorem Z_agree {k rowv s s' : ℕ} (constant : ℕ → Fin (2 ^ k)) (hk : 0 < k) (hrow : rowv < 2 ^ k)
    (hs : s < 2 ^ k) (hs' : s' < 2 ^ k) {b T : ℕ} (hT : 5 ≤ T) (hb : 2 * T ≤ b)
    (hag : ∀ y, b + 5 < y + 2 * T → y + 1 ≤ b + 3 * T → B k s y = B k s' y) :
    ∀ n, n + 2 ≤ T → ∀ x, b + n + 1 ≤ x + T → x + 3 * n + 1 ≤ b + 3 * T →
      B k (Z k rowv constant s n) x = B k (Z k rowv constant s' n) x
  | 0, _, x, h1, h2 => by
    show B k s x = B k s' x
    exact hag x (by omega) (by omega)
  | n + 1, hn, x, h1, h2 => by
    rw [Z_succ, Z_succ,
      rnd_agree constant hk (Z_lt k rowv constant hs n) (Z_lt k rowv constant hs' n)
        (Nat.xor_lt_two_pow hs hrow) (Nat.xor_lt_two_pow hs' hrow) (by omega) (by omega)
        (fun y hy1 hy2 => Z_agree constant hk hrow hs hs' hT hb hag n (by omega) y (by omega) (by omega)),
      B_xor, B_xor, hag (x + 1 - 2 * n) (by omega) (by omega)]
    simp

theorem boolG (z0 z1 z2 a a' r0 c1 c2 : Bool) :
    xor (xor (xor z0 (xor (xor a r0) (xor a' r0))) (xor z1 (xor c1 c1))) (xor z2 (xor c2 c2)) =
      xor (xor (xor z0 z1) z2) (xor a a') := by
  cases z0 <;> cases z1 <;> cases z2 <;> cases a <;> cases a' <;> cases r0 <;> cases c1 <;> cases c2 <;> rfl

theorem guard_toggle {k rowv s s' : ℕ} (constant : ℕ → Fin (2 ^ k)) (hk : 0 < k) (hrow : rowv < 2 ^ k)
    (hs : s < 2 ^ k) (hs' : s' < 2 ^ k) {b T : ℕ} (hT : 5 ≤ T) (hb : 2 * T ≤ b)
    (hag : ∀ y, b + 5 < y + 2 * T → y + 1 ≤ b + 3 * T → B k s y = B k s' y) :
    xor (xor (B k (Z k rowv constant s (T - 1)) b) (B k (Z k rowv constant s (T - 1)) (b + 1)))
        (B k (Z k rowv constant s (T - 1)) (b + 2)) =
      xor (xor (xor (B k (Z k rowv constant s' (T - 1)) b) (B k (Z k rowv constant s' (T - 1)) (b + 1)))
        (B k (Z k rowv constant s' (T - 1)) (b + 2)))
        (xor (B k s (b + 5 - 2 * T)) (B k s' (b + 5 - 2 * T))) := by
  obtain ⟨n, rfl⟩ : ∃ n, T = n + 2 := ⟨T - 2, by omega⟩
  have hprev : ∀ y, b ≤ y + 1 → y ≤ b + 5 →
      B k (Z k rowv constant s n) y = B k (Z k rowv constant s' n) y :=
    fun y h1 h2 => Z_agree constant hk hrow hs hs' hT hb hag n (by omega) y (by omega) (by omega)
  have hu := Nat.xor_lt_two_pow hs hrow
  have hu' := Nat.xor_lt_two_pow hs' hrow
  have key : ∀ x, b ≤ x → x ≤ b + 2 → B k (Z k rowv constant s (n + 1)) x =
      xor (B k (Z k rowv constant s' (n + 1)) x)
        (xor (xor (B k s (x + 1 - 2 * n)) (B k rowv (x + 1 - 2 * n)))
          (xor (B k s' (x + 1 - 2 * n)) (B k rowv (x + 1 - 2 * n)))) := by
    intro x h1 h2
    rw [Z_succ, Z_succ, ← B_xor, ← B_xor]
    exact rnd_agree constant hk (Z_lt k rowv constant hs n) (Z_lt k rowv constant hs' n) hu hu'
      (by omega) (by omega) (fun y hy1 hy2 => hprev y (by omega) (by omega))
  have e0 := key b (by omega) (by omega)
  have e1 := key (b + 1) (by omega) (by omega)
  have e2 := key (b + 2) (by omega) (by omega)
  rw [hag (b + 1 + 1 - 2 * n) (by omega) (by omega)] at e1
  rw [hag (b + 2 + 1 - 2 * n) (by omega) (by omega)] at e2
  rw [show b + 1 - 2 * n = b + 5 - 2 * (n + 2) by omega] at e0
  rw [show n + 2 - 1 = n + 1 by omega, e0, e1, e2]
  exact boolG _ _ _ _ _ _ _ _

def tog (pv : ℕ → ℕ) (g : ℕ → ℕ → Bool) (trial visit : ℕ) : ℕ :=
  if g visit trial then trial ^^^ (1 <<< pv visit) else trial

def Good (k : ℕ) (pv : ℕ → ℕ) (g : ℕ → ℕ → Bool) : List ℕ → Prop
  | [] => True
  | t :: L => (pv t < k ∧ pv t ∉ L.map pv ∧
      ∀ x x' : ℕ, x < 2 ^ k → x' < 2 ^ k →
        (∀ j, j < k → j ≠ pv t → j ∉ L.map pv → x.testBit j = x'.testBit j) →
        g t x = xor (g t x') (xor (x.testBit (pv t)) (x'.testBit (pv t)))) ∧ Good k pv g L

theorem good_nodup {k : ℕ} {pv : ℕ → ℕ} {g : ℕ → ℕ → Bool} :
    ∀ L : List ℕ, Good k pv g L → (L.map pv).Nodup
  | [], _ => List.nodup_nil
  | t :: L, h => by
    rw [List.map_cons, List.nodup_cons]
    exact ⟨h.1.2.1, good_nodup L h.2⟩

theorem flip_tb (x p j : ℕ) : (x ^^^ (1 <<< p)).testBit j = xor (x.testBit j) (decide (p = j)) := by
  rw [Nat.testBit_xor, Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem dec_spec (k : ℕ) (pv : ℕ → ℕ) (g : ℕ → ℕ → Bool) :
    ∀ L : List ℕ, Good k pv g L → ∀ x, x < 2 ^ k →
      L.foldl (tog pv g) x < 2 ^ k ∧
      (∀ j, j < k → j ∉ L.map pv → (L.foldl (tog pv g) x).testBit j = x.testBit j) ∧
      (∀ t ∈ L, g t (L.foldl (tog pv g) x) = false) ∧
      (∀ target, target < 2 ^ k → (∀ j, j < k → j ∉ L.map pv → target.testBit j = x.testBit j) →
        (∀ t ∈ L, g t target = false) → target = L.foldl (tog pv g) x)
  | [], _, x, hx => by
    refine ⟨hx, fun _ _ _ => rfl, fun t ht => absurd ht (List.not_mem_nil), ?_⟩
    intro target ht hbits _
    show target = x
    apply Nat.eq_of_testBit_eq
    intro j
    by_cases hj : j < k
    · exact hbits j hj (by simp)
    · exact (tb_high ht (by omega)).trans (tb_high hx (by omega)).symm
  | t :: L, hG, x, hx => by
    obtain ⟨⟨hpk, hnin, hA⟩, hGL⟩ := hG
    have hbitlt : 1 <<< pv t < 2 ^ k := by
      rw [Nat.one_shiftLeft]; exact Nat.pow_lt_pow_right (by norm_num) hpk
    have hx1 : tog pv g x t < 2 ^ k := by
      unfold tog; split
      · exact Nat.xor_lt_two_pow hx hbitlt
      · exact hx
    have hx1bit : ∀ j, j ≠ pv t → (tog pv g x t).testBit j = x.testBit j := by
      intro j hj
      unfold tog; split
      · rw [flip_tb]; simp [Ne.symm hj]
      · rfl
    have hg1 : g t (tog pv g x t) = false := by
      by_cases hgx : g t x = true
      · have e : tog pv g x t = x ^^^ (1 <<< pv t) := by simp [tog, hgx]
        have h := hA (x ^^^ (1 <<< pv t)) x (Nat.xor_lt_two_pow hx hbitlt) hx
          (fun j _ hj _ => by rw [flip_tb]; simp [Ne.symm hj])
        rw [e, h, flip_tb, hgx]
        simp
      · have e : tog pv g x t = x := by simp [tog, hgx]
        rw [e]; simpa using hgx
    obtain ⟨hlt, hoff, hgz, huniq⟩ := dec_spec k pv g L hGL (tog pv g x t) hx1
    rw [List.foldl_cons]
    refine ⟨hlt, ?_, ?_, ?_⟩
    · intro j hj hjn
      rw [List.map_cons, List.mem_cons, not_or] at hjn
      rw [hoff j hj hjn.2, hx1bit j hjn.1]
    · intro t' ht'
      rcases List.mem_cons.mp ht' with rfl | h
      · have h := hA (L.foldl (tog pv g) (tog pv g x t')) (tog pv g x t') hlt hx1
          (fun j hj _ hjn => hoff j hj hjn)
        rw [h, hg1, hoff (pv t') hpk hnin]
        simp
      · exact hgz t' h
    · intro target ht hbits hgt
      apply huniq target ht
      · intro j hj hjn
        by_cases hjp : j = pv t
        · subst hjp
          have h := hA target (tog pv g x t) ht hx1 (fun j' hj' hne hjn' => by
            rw [hx1bit j' hne]
            exact hbits j' hj' (by rw [List.map_cons, List.mem_cons, not_or]; exact ⟨hne, hjn'⟩))
          rw [hgt t (List.mem_cons_self), hg1] at h
          revert h
          cases target.testBit (pv t) <;> cases (tog pv g x t).testBit (pv t) <;> simp
        · rw [hx1bit j hjp]
          exact hbits j hj (by rw [List.map_cons, List.mem_cons, not_or]; exact ⟨hjp, hjn⟩)
      · intro t' ht'
        exact hgt t' (List.mem_cons_of_mem _ ht')

theorem hidden_tb (pv : ℕ → ℕ) : ∀ (L : List ℕ) (init j : ℕ), j ∉ L.map pv →
    (L.foldl (fun mask entry => mask ||| (1 <<< pv entry)) init).testBit j = init.testBit j
  | [], _, _, _ => rfl
  | t :: L, init, j, h => by
    rw [List.map_cons, List.mem_cons, not_or] at h
    rw [List.foldl_cons, hidden_tb pv L _ j h.2, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow]
    simp [Ne.symm h.1]

def posF (k r i : ℕ) (d : ℕ → ℕ) (t : ℕ) : ℕ := k + i + 3 * (r - t) - d t

def pivotF (k r i : ℕ) (d : ℕ → ℕ) (t : ℕ) : ℕ := (posF k r i d t + 5 - 2 * t) % k

def guardF (k r i : ℕ) (row : Fin (2 ^ k)) (constant : ℕ → Fin (2 ^ k)) (d : ℕ → ℕ)
    (guardTime start : ℕ) : Bool :=
  xor (xor ((Z k row.val constant start (guardTime - 1)).testBit (posF k r i d guardTime % k))
    ((Z k row.val constant start (guardTime - 1)).testBit ((posF k r i d guardTime + 1) % k)))
    ((Z k row.val constant start (guardTime - 1)).testBit ((posF k r i d guardTime + 2) % k))

theorem mod_ne {a y k : ℕ} (h1 : a < y) (h2 : y < a + k) : y % k ≠ a % k := by
  intro h
  have h3 : a ≡ y [MOD k] := h.symm
  have h4 : k ∣ y - a := (Nat.modEq_iff_dvd' (le_of_lt h1)).mp h3
  have h5 := Nat.le_of_dvd (by omega) h4
  omega

theorem good_recs {k r e q i : ℕ} (row : Fin (2 ^ k)) (constant : ℕ → Fin (2 ^ k)) (d : ℕ → ℕ)
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hk : k + e + 3 = 5 * r)
    (h1 : ∀ t, e + q + 3 ≤ t → t ≤ r → d t < e + q ∧ d t ≤ 4 * (r - t)) :
    ∀ L : List ℕ, (∀ t ∈ L, e + q + 3 < t ∧ t ≤ r - e) →
      L.Pairwise (fun a b => a < b ∧ a + d a < b + d b) →
      Good k (pivotF k r i d) (guardF k r i row constant d) L
  | [], _, _ => trivial
  | t :: L, hmem, hpw => by
    have hkpos : 0 < k := by omega
    obtain ⟨hlt, hpwL⟩ := List.pairwise_cons.mp hpw
    obtain ⟨htc, hte⟩ := hmem t (List.mem_cons_self)
    have hdt := (h1 t (by omega) (by omega)).2
    have hb : posF k r i d t = k + i + 3 * (r - t) - d t := rfl
    have hsep : ∀ t' ∈ L, ∀ y, posF k r i d t + 5 - 2 * t ≤ y → y + 1 ≤ posF k r i d t + 3 * t →
        y % k ≠ pivotF k r i d t' := by
      intro t' ht' y hy1 hy2
      obtain ⟨htc', hte'⟩ := hmem t' (List.mem_cons_of_mem _ ht')
      have hdt' := (h1 t' (by omega) (by omega)).2
      obtain ⟨hl1, hl2⟩ := hlt t' ht'
      have hb' : posF k r i d t' = k + i + 3 * (r - t') - d t' := rfl
      show y % k ≠ (posF k r i d t' + 5 - 2 * t') % k
      apply mod_ne
      · omega
      · omega
    refine ⟨⟨Nat.mod_lt _ hkpos, ?_, ?_⟩,
      good_recs row constant d hq hr hk h1 L (fun t' ht' => hmem t' (List.mem_cons_of_mem _ ht')) hpwL⟩
    · intro hin
      obtain ⟨t', ht', heq⟩ := List.mem_map.mp hin
      exact hsep t' ht' (posF k r i d t + 5 - 2 * t) (le_refl _) (by omega) heq.symm
    · intro x x' hx hx' hagree
      refine guard_toggle constant hkpos row.isLt hx hx' (b := posF k r i d t) (T := t)
        (by omega) (by omega) ?_
      intro y hy1 hy2
      apply hagree (y % k) (Nat.mod_lt _ hkpos)
      · show y % k ≠ (posF k r i d t + 5 - 2 * t) % k
        apply mod_ne
        · omega
        · omega
      · intro hin
        obtain ⟨t', ht', heq⟩ := List.mem_map.mp hin
        exact hsep t' ht' y (by omega) hy2 heq.symm

def isRec (cut : ℕ) (d : ℕ → ℕ) (time : ℕ) : Bool :=
  decide (cut < time) && (List.range time).all (fun prior =>
    decide (prior < cut ∨ prior + d prior < time + d time))

theorem isRec_iff (cut : ℕ) (d : ℕ → ℕ) (t : ℕ) : isRec cut d t = true ↔
    cut < t ∧ ∀ prior, prior < t → prior < cut ∨ prior + d prior < t + d t := by
  simp [isRec, List.all_eq_true]

theorem count_ge (cut N : ℕ) (d : ℕ → ℕ) (hd : ∀ t, cut < t → t ≤ N → d t ≤ d (t - 1)) :
    ∀ T, cut ≤ T → T ≤ N → ∀ t, cut ≤ t → t ≤ T →
      t + d t ≤ cut + d cut + ((List.range (T + 1)).filter (isRec cut d)).length := by
  intro T hT
  induction T, hT using Nat.le_induction with
  | base =>
    intro _ t h1 h2
    have : t = cut := by omega
    subst this; omega
  | succ T hT ih =>
    intro hN t h1 h2
    rw [List.range_succ, List.filter_append, List.length_append]
    by_cases htT : t ≤ T
    · have := ih (by omega) t h1 htT
      omega
    · have ht : t = T + 1 := by omega
      subst ht
      by_cases hrec : isRec cut d (T + 1) = true
      · have h3 := hd (T + 1) (by omega) hN
        have h4 := ih (by omega) T hT (le_refl _)
        rw [Nat.add_sub_cancel] at h3
        have hl : (List.filter (isRec cut d) [T + 1]).length = 1 := by simp [hrec]
        rw [hl]; omega
      · have hnot := (isRec_iff cut d (T + 1)).not.mp hrec
        rw [not_and] at hnot
        have hnot2 := hnot (by omega)
        push Not at hnot2
        obtain ⟨prior, hp1, hp2, hp3⟩ := hnot2
        have := ih (by omega) prior (by omega) (by omega)
        omega

def recs (r e q : ℕ) (d : ℕ → ℕ) : List ℕ :=
  ((List.range (r - e + 1)).filter (isRec (e + q + 3) d)).take (r - (3 * e + 2 * q + 2))

theorem main (k r e q i : ℕ) (row : Fin (2 ^ k)) (constant : ℕ → Fin (2 ^ k)) (d : ℕ → ℕ)
    (hq : 0 < q) (hr : 3 * e + 2 * q + 3 ≤ r) (hk : k + e + 3 = 5 * r)
    (h1 : ∀ t, e + q + 3 ≤ t → t ≤ r → d t < e + q ∧ d t ≤ 4 * (r - t))
    (h2 : ∀ t, e + q + 3 < t → t ≤ r → d t ≤ d (t - 1)) :
    (recs r e q d).length = r - (3 * e + 2 * q + 2) ∧ ((recs r e q d).map (pivotF k r i d)).Nodup ∧
    ∀ seed target : ℕ, seed < 2 ^ k →
      ((recs r e q d).foldl (tog (pivotF k r i d) (guardF k r i row constant d))
          (seed ^^^ (seed &&& (recs r e q d).foldl
            (fun mask entry => mask ||| (1 <<< pivotF k r i d entry)) 0)) = target ↔
        target < 2 ^ k ∧
        (∀ j : Fin k, j.val ∉ (recs r e q d).map (pivotF k r i d) →
          seed.testBit j.val = target.testBit j.val) ∧
        ∀ t ∈ recs r e q d, guardF k r i row constant d t target = false) := by
  have hmem : ∀ t ∈ recs r e q d, e + q + 3 < t ∧ t ≤ r - e := by
    intro t ht
    have h := List.mem_filter.mp (List.mem_of_mem_take ht)
    have h3 := List.mem_range.mp h.1
    have h4 := ((isRec_iff _ _ _).mp h.2).1
    omega
  have hpw : (recs r e q d).Pairwise (fun a b => a < b ∧ a + d a < b + d b) := by
    have h0 : (recs r e q d).Pairwise (· < ·) :=
      List.Pairwise.sublist ((List.take_sublist _ _).trans List.filter_sublist) List.pairwise_lt_range
    refine h0.imp_of_mem ?_
    intro a b ha hb hab
    have h := List.mem_filter.mp (List.mem_of_mem_take hb)
    have h4 := ((isRec_iff _ _ _).mp h.2).2 a hab
    have h5 := (hmem a ha).1
    exact ⟨hab, by omega⟩
  have hgood := good_recs (i := i) row constant d hq hr hk h1 (recs r e q d) hmem hpw
  refine ⟨?_, good_nodup _ hgood, ?_⟩
  · unfold recs
    rw [List.length_take]
    have h3 := count_ge (e + q + 3) r d h2 (r - e) (by omega) (by omega) (r - e) (by omega) (le_refl _)
    have h4 := (h1 (e + q + 3) (le_refl _) (by omega)).1
    omega
  · intro seed target hseed
    have hx0 : seed ^^^ (seed &&& (recs r e q d).foldl
        (fun mask entry => mask ||| (1 <<< pivotF k r i d entry)) 0) < 2 ^ k :=
      Nat.xor_lt_two_pow hseed (lt_of_le_of_lt Nat.and_le_left hseed)
    obtain ⟨hlt, hoff, hgz, huniq⟩ := dec_spec k _ _ (recs r e q d) hgood _ hx0
    have hbit : ∀ j, j < k → j ∉ (recs r e q d).map (pivotF k r i d) →
        (seed ^^^ (seed &&& (recs r e q d).foldl
          (fun mask entry => mask ||| (1 <<< pivotF k r i d entry)) 0)).testBit j = seed.testBit j := by
      intro j hj hnin
      rw [Nat.testBit_xor, Nat.testBit_and, hidden_tb _ _ _ _ hnin]
      simp
    constructor
    · rintro rfl
      exact ⟨hlt, fun j hj => by rw [hoff j.val j.isLt hj, hbit j.val j.isLt hj], hgz⟩
    · rintro ⟨ht1, ht2, ht3⟩
      exact (huniq target ht1 (fun j hj hnin => by
        rw [hbit j hj hnin]; exact (ht2 ⟨j, hj⟩ hnin).symm) ht3).symm

end PEqualNP.Outside.L_meta_25532_aux

theorem PEqualNP.Outside.L_meta_25532 : (∀ (k r e q i : Nat) (row : Fin (2 ^ k))
    (constant : Nat → Fin (2 ^ k)) (d : Nat → Nat),
  0 < q → 3 * e + 2 * q + 3 ≤ r → k + e + 3 = 5 * r → i < k →
  let cut := e + q + 3
  (∀ t, cut ≤ t → t ≤ r → d t < e + q ∧ d t ≤ 4 * (r - t)) →
  (∀ t, cut < t → t ≤ r → d t ≤ d (t - 1)) →
  let m := r - (3 * e + 2 * q + 2)
  let records := ((List.range (r - e + 1)).filter (fun time =>
    decide (cut < time) && (List.range time).all (fun prior =>
      decide (prior < cut ∨ prior + d prior < time + d time)))).take m
  let pos := fun roundIdx => k + i + 3 * (r - roundIdx) - d roundIdx
  let pivot := fun recordTime => (pos recordTime + 5 - 2 * recordTime) % k
  let rot := fun (s bits : Nat) =>
    ((bits <<< (s % k)) ||| (bits >>> (k - s % k))) % 2 ^ k
  let step := fun (mixed : Nat) =>
    (List.range k).foldl (fun acc place =>
      acc ||| ((xor (mixed.testBit place)
        (!(mixed.testBit ((place + 1) % k)) && mixed.testBit ((place + 2) % k))).toNat <<< place)) 0
  let guard := fun (guardTime start : Nat) =>
    let key := rot (k - 1) (start ^^^ row.val)
    let z := (List.range (guardTime - 1)).foldl (fun prev roundNo =>
      step (prev ^^^ rot 1 prev ^^^ rot (k - 1) prev) ^^^ rot (2 * roundNo) key ^^^
        (constant (roundNo + 1)).val) start
    let b := pos guardTime
    xor (xor (z.testBit (b % k)) (z.testBit ((b + 1) % k)))
      (z.testBit ((b + 2) % k))
  let hidden := records.foldl (fun mask entry => mask ||| (1 <<< pivot entry)) 0
  let decode := fun input => records.foldl (fun trial visit =>
    if guard visit trial then trial ^^^ (1 <<< pivot visit) else trial)
    (input ^^^ (input &&& hidden))
  records.length = m ∧ (records.map pivot).Nodup ∧
  ∀ seed target : Nat, seed < 2 ^ k →
    (decode seed = target ↔ target < 2 ^ k ∧
      (∀ j : Fin k, j.val ∉ records.map pivot →
        seed.testBit j.val = target.testBit j.val) ∧
      ∀ t ∈ records, guard t target = false)) := by
  intro k r e q i row constant d hq hr hk hi cut h1 h2 m records pos pivot rot step guard hidden decode
  exact PEqualNP.Outside.L_meta_25532_aux.main k r e q i row constant d hq hr hk h1 h2
