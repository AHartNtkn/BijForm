import BijForm.Coding
import BijForm.Pairing

namespace BijForm
namespace CodeAlgebra

universe u

/-- Split `Nat` into a finite prefix of size `k` and the remaining tail. -/
def finPlusNat (k : Nat) : (Fin k ⊕ Nat) ≃ᵢ Nat where
  toFun
    | Sum.inl i => i.val
    | Sum.inr n => k + n
  invFun n :=
    if h : n < k then
      Sum.inl ⟨n, h⟩
    else
      Sum.inr (n - k)
  left_inv := by
    intro x
    cases x with
    | inl i =>
        simp [i.isLt]
    | inr n =>
        have hnot : ¬k + n < k := by omega
        simp [hnot]
  right_inv := by
    intro n
    by_cases h : n < k
    · simp [h]
    · have hk : k ≤ n := Nat.le_of_not_gt h
      simp [h, Nat.add_sub_of_le hk]

theorem finPlusNat_inr_lt {k n tail : Nat} (hk : 0 < k)
    (h : (finPlusNat k).invFun n = Sum.inr tail) : tail < n := by
  have hright := (finPlusNat k).right_inv n
  rw [h] at hright
  simp [finPlusNat] at hright
  omega

/-- Coding for a nonempty finite choice paired with a natural-number payload. -/
def finProdNat (k : Nat) (hk : 0 < k) : (Fin k × Nat) ≃ᵢ Nat where
  toFun := fun p => p.1.val + k * p.2
  invFun := fun n => (⟨n % k, Nat.mod_lt n hk⟩, n / k)
  left_inv := by
    intro p
    cases p with
    | mk i n =>
      apply Prod.ext
      · apply Fin.ext
        calc
          (i.val + k * n) % k = i.val % k := Nat.add_mul_mod_self_left i.val k n
          _ = i.val := Nat.mod_eq_of_lt i.isLt
      · calc
          (i.val + k * n) / k = (i.val + n * k) / k := by rw [Nat.mul_comm k n]
          _ = i.val / k + n := Nat.add_mul_div_right i.val n hk
          _ = n := by
            rw [Nat.div_eq_of_lt i.isLt]
            exact Nat.zero_add n
  right_inv := by
    intro n
    dsimp
    calc
      n % k + k * (n / k) = k * (n / k) + n % k := by
        rw [Nat.add_comm]
      _ = n := Nat.div_add_mod n k

theorem finProdNat_snd_le (k : Nat) (hk : 0 < k) (n : Nat) :
    ((finProdNat k hk).invFun n).2 ≤ n := by
  simp [finProdNat]
  exact Nat.div_le_self n k

theorem finProdNat_toFun_snd_le (k : Nat) (hk : 0 < k) (p : Fin k × Nat) :
    p.2 ≤ (finProdNat k hk).toFun p := by
  dsimp [finProdNat]
  have hmul : p.2 ≤ k * p.2 := by
    calc
      p.2 = 1 * p.2 := by rw [Nat.one_mul]
      _ ≤ k * p.2 := Nat.mul_le_mul_right p.2 hk
  omega

/-- Finite sums are finite. -/
def finSum (a b : Nat) : (Fin a ⊕ Fin b) ≃ᵢ Fin (a + b) where
  toFun
    | Sum.inl i => ⟨i.val, by omega⟩
    | Sum.inr j => ⟨a + j.val, by omega⟩
  invFun k :=
    if h : k.val < a then
      Sum.inl ⟨k.val, h⟩
    else
      Sum.inr ⟨k.val - a, by omega⟩
  left_inv := by
    intro x
    cases x with
    | inl i => simp [i.isLt]
    | inr j =>
        have hnot : ¬a + j.val < a := by omega
        simp [hnot, Nat.add_sub_cancel_left]
  right_inv := by
    intro k
    by_cases h : k.val < a
    · simp [h]
    · have hle : a ≤ k.val := Nat.le_of_not_gt h
      simp [h]
      apply Fin.ext
      exact Nat.add_sub_of_le hle

/-- Finite products are finite when the right factor is nonempty. -/
def finProdPos (a b : Nat) (hb : 0 < b) : (Fin a × Fin b) ≃ᵢ Fin (a * b) where
  toFun p := ⟨p.1.val * b + p.2.val, by
    have hlt_add : p.1.val * b + p.2.val < p.1.val * b + b :=
      Nat.add_lt_add_left p.2.isLt (p.1.val * b)
    have hsucc : p.1.val * b + b = (p.1.val + 1) * b := by
      rw [Nat.succ_mul]
    have hlt_succ : p.1.val * b + p.2.val < (p.1.val + 1) * b := by
      simpa [hsucc] using hlt_add
    have hle : (p.1.val + 1) * b ≤ a * b :=
      Nat.mul_le_mul_right b (Nat.succ_le_of_lt p.1.isLt)
    exact Nat.lt_of_lt_of_le hlt_succ hle⟩
  invFun k :=
    (⟨k.val / b, by
      have hk : k.val < b * a := Nat.lt_of_lt_of_eq k.isLt (Nat.mul_comm a b)
      exact Nat.div_lt_of_lt_mul hk⟩,
     ⟨k.val % b, Nat.mod_lt k.val hb⟩)
  left_inv := by
    intro p
    cases p with
    | mk i j =>
      apply Prod.ext
      · apply Fin.ext
        calc
          (i.val * b + j.val) / b = (b * i.val + j.val) / b := by
            rw [Nat.mul_comm i.val b]
          _ = i.val + j.val / b := Nat.mul_add_div hb i.val j.val
          _ = i.val := by rw [Nat.div_eq_of_lt j.isLt, Nat.add_zero]
      · apply Fin.ext
        calc
          (i.val * b + j.val) % b = j.val % b := Nat.mul_add_mod_self_right i.val b j.val
          _ = j.val := Nat.mod_eq_of_lt j.isLt
  right_inv := by
    intro k
    apply Fin.ext
    calc
      (k.val / b) * b + k.val % b = b * (k.val / b) + k.val % b := by
        rw [Nat.mul_comm]
      _ = k.val := Nat.div_add_mod k.val b

/-- Binary sum coding via parity. -/
def sumNat : (Nat ⊕ Nat) ≃ᵢ Nat where
  toFun
    | Sum.inl n => 2 * n
    | Sum.inr n => 2 * n + 1
  invFun n :=
    if n % 2 = 0 then
      Sum.inl (n / 2)
    else
      Sum.inr (n / 2)
  left_inv := by
    intro x
    cases x with
    | inl n =>
      have hmod : (2 * n) % 2 = 0 := by
          exact Nat.mul_mod_right 2 n
      have hdiv : (2 * n) / 2 = n := by
          exact Nat.mul_div_right n (by decide : 0 < 2)
      simp [hmod, hdiv]
    | inr n =>
        have hmod : (2 * n + 1) % 2 ≠ 0 := by
          have hlt : 1 < 2 := by decide
          have hcalc : (2 * n + 1) % 2 = 1 := by
            calc
              (2 * n + 1) % 2 = (1 + 2 * n) % 2 := by rw [Nat.add_comm]
              _ = 1 % 2 := Nat.add_mul_mod_self_left 1 2 n
              _ = 1 := Nat.mod_eq_of_lt hlt
          omega
        have hdiv : (2 * n + 1) / 2 = n := by
          calc
            (2 * n + 1) / 2 = (1 + 2 * n) / 2 := by rw [Nat.add_comm]
            _ = (1 + n * 2) / 2 := by rw [Nat.mul_comm 2 n]
            _ = 1 / 2 + n := Nat.add_mul_div_right 1 n (by decide : 0 < 2)
            _ = n := by
              rw [Nat.div_eq_of_lt (by decide : 1 < 2)]
              exact Nat.zero_add n
        simp [hdiv]
  right_inv := by
    intro n
    have hsplit := Nat.div_add_mod n 2
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · simp [h]
      omega
    · have hne : n % 2 ≠ 0 := by omega
      simp [hne]
      omega

theorem sumNat_inl_le {n a : Nat}
    (h : sumNat.invFun n = Sum.inl a) : a ≤ n := by
  have hright := sumNat.right_inv n
  rw [h] at hright
  simp [sumNat] at hright
  omega

theorem sumNat_inr_le {n a : Nat}
    (h : sumNat.invFun n = Sum.inr a) : a ≤ n := by
  have hright := sumNat.right_inv n
  rw [h] at hright
  simp [sumNat] at hright
  omega

def sum3Nat : (Nat ⊕ (Nat ⊕ Nat)) ≃ᵢ Nat :=
  Iso.trans (Iso.sum (Iso.refl Nat) sumNat) sumNat

def sum4Nat : (Nat ⊕ (Nat ⊕ (Nat ⊕ Nat))) ≃ᵢ Nat :=
  Iso.trans (Iso.sum (Iso.refl Nat) sum3Nat) sumNat

/-- Product coding delegates to the proved simplified pairing function. -/
def prodNat : (Nat × Nat) ≃ᵢ Nat :=
  Pairing.iso

theorem prodNat_fst_le (n : Nat) : (prodNat.invFun n).1 ≤ n :=
  Pairing.decode_fst_le n

theorem prodNat_snd_le (n : Nat) : (prodNat.invFun n).2 ≤ n :=
  Pairing.decode_snd_le n

theorem prodNat_toFun_fst_le (p : Nat × Nat) : p.1 ≤ prodNat.toFun p := by
  simpa using prodNat_fst_le (prodNat.toFun p)

theorem prodNat_toFun_snd_le (p : Nat × Nat) : p.2 ≤ prodNat.toFun p := by
  simpa using prodNat_snd_le (prodNat.toFun p)

def sumProdNat : (Nat ⊕ (Nat × Nat)) ≃ᵢ Nat :=
  Iso.trans (Iso.sum (Iso.refl Nat) prodNat) sumNat

theorem sumProdNat_toFun_inr_fst_lt (p : Nat × Nat) :
    p.1 < sumProdNat.toFun (Sum.inr p) := by
  dsimp [sumProdNat, Iso.trans, Iso.sum, sumNat]
  have hle := prodNat_toFun_fst_le p
  omega

theorem sumProdNat_toFun_inr_snd_lt (p : Nat × Nat) :
    p.2 < sumProdNat.toFun (Sum.inr p) := by
  dsimp [sumProdNat, Iso.trans, Iso.sum, sumNat]
  have hle := prodNat_toFun_snd_le p
  omega

theorem sumProdNat_invFun_inr_fst_lt {n a b : Nat}
    (h : sumProdNat.invFun n = Sum.inr (a, b)) : a < n := by
  have hright := sumProdNat.right_inv n
  rw [h] at hright
  have hlt := sumProdNat_toFun_inr_fst_lt (a, b)
  rw [hright] at hlt
  exact hlt

theorem sumProdNat_invFun_inr_snd_lt {n a b : Nat}
    (h : sumProdNat.invFun n = Sum.inr (a, b)) : b < n := by
  have hright := sumProdNat.right_inv n
  rw [h] at hright
  have hlt := sumProdNat_toFun_inr_snd_lt (a, b)
  rw [hright] at hlt
  exact hlt

def natOrProdOrProdNat :
    (Nat ⊕ ((Nat × Nat) ⊕ (Nat × Nat))) ≃ᵢ Nat :=
  Iso.trans (Iso.sum (Iso.refl Nat) (Iso.sum prodNat prodNat)) sum3Nat

theorem natOrProdOrProdNat_toFun_inl_le (n : Nat) :
    n ≤ natOrProdOrProdNat.toFun (Sum.inl n) := by
  simp [natOrProdOrProdNat, sum3Nat, Iso.trans, Iso.sum, sumNat, Iso.refl]
  omega

theorem natOrProdOrProdNat_toFun_inr_inl_fst_le (p : Nat × Nat) :
    p.1 ≤ natOrProdOrProdNat.toFun (Sum.inr (Sum.inl p)) := by
  simp [natOrProdOrProdNat, sum3Nat, Iso.trans, Iso.sum, sumNat, Iso.refl]
  have hle := prodNat_toFun_fst_le p
  omega

theorem natOrProdOrProdNat_toFun_inr_inl_snd_le (p : Nat × Nat) :
    p.2 ≤ natOrProdOrProdNat.toFun (Sum.inr (Sum.inl p)) := by
  simp [natOrProdOrProdNat, sum3Nat, Iso.trans, Iso.sum, sumNat, Iso.refl]
  have hle := prodNat_toFun_snd_le p
  omega

theorem natOrProdOrProdNat_toFun_inr_inr_fst_le (p : Nat × Nat) :
    p.1 ≤ natOrProdOrProdNat.toFun (Sum.inr (Sum.inr p)) := by
  simp [natOrProdOrProdNat, sum3Nat, Iso.trans, Iso.sum, sumNat, Iso.refl]
  have hle := prodNat_toFun_fst_le p
  omega

theorem natOrProdOrProdNat_toFun_inr_inr_snd_le (p : Nat × Nat) :
    p.2 ≤ natOrProdOrProdNat.toFun (Sum.inr (Sum.inr p)) := by
  simp [natOrProdOrProdNat, sum3Nat, Iso.trans, Iso.sum, sumNat, Iso.refl]
  have hle := prodNat_toFun_snd_le p
  omega

def prodOrNatOrProdOrNat :
    ((Nat × Nat) ⊕ (Nat ⊕ ((Nat × Nat) ⊕ Nat))) ≃ᵢ Nat :=
  Iso.trans
    (Iso.sum prodNat (Iso.sum (Iso.refl Nat) (Iso.sum prodNat (Iso.refl Nat))))
    sum4Nat

theorem prodOrNatOrProdOrNat_toFun_inr_inl_lt (n : Nat) :
    n < prodOrNatOrProdOrNat.toFun (Sum.inr (Sum.inl n)) := by
  simp [prodOrNatOrProdOrNat, sum4Nat, sum3Nat, Iso.trans, Iso.sum, sumNat, Iso.refl]
  omega

theorem prodOrNatOrProdOrNat_toFun_inr_inr_inl_fst_lt (p : Nat × Nat) :
    p.1 < prodOrNatOrProdOrNat.toFun (Sum.inr (Sum.inr (Sum.inl p))) := by
  simp [prodOrNatOrProdOrNat, sum4Nat, sum3Nat, Iso.trans, Iso.sum, sumNat, Iso.refl]
  have hle := prodNat_toFun_fst_le p
  omega

theorem prodOrNatOrProdOrNat_toFun_inr_inr_inl_snd_lt (p : Nat × Nat) :
    p.2 < prodOrNatOrProdOrNat.toFun (Sum.inr (Sum.inr (Sum.inl p))) := by
  simp [prodOrNatOrProdOrNat, sum4Nat, sum3Nat, Iso.trans, Iso.sum, sumNat, Iso.refl]
  have hle := prodNat_toFun_snd_le p
  omega

theorem prodOrNatOrProdOrNat_toFun_inr_inr_inr_lt (n : Nat) :
    n < prodOrNatOrProdOrNat.toFun (Sum.inr (Sum.inr (Sum.inr n))) := by
  simp [prodOrNatOrProdOrNat, sum4Nat, sum3Nat, Iso.trans, Iso.sum, sumNat, Iso.refl]
  omega

def finPrefixNat {α : Type u} (k : Nat) (tail : α ≃ᵢ Nat) :
    (Fin k ⊕ α) ≃ᵢ Nat :=
  Iso.trans (Iso.sum (Iso.refl (Fin k)) tail) (finPlusNat k)

/-- Finite constructor branches plus finitely tagged recursive `Nat` branches. -/
def finiteRecursiveNat (finite recursive : Nat) (hrec : 0 < recursive) :
    (Fin finite ⊕ (Fin recursive × Nat)) ≃ᵢ Nat :=
  finPrefixNat finite (finProdNat recursive hrec)

theorem finPrefixNat_toFun_inr_lt_of_lt {α : Type u}
    (k : Nat) (tail : α ≃ᵢ Nat) {a : α} {m : Nat}
    (h : m < tail.toFun a) :
    m < (finPrefixNat k tail).toFun (Sum.inr a) := by
  dsimp [finPrefixNat, Iso.trans, Iso.sum, finPlusNat]
  omega

theorem finPrefixNat_toFun_inr_lt_of_le {α : Type u}
    (k : Nat) (hk : 0 < k) (tail : α ≃ᵢ Nat) {a : α} {m : Nat}
    (h : m ≤ tail.toFun a) :
    m < (finPrefixNat k tail).toFun (Sum.inr a) := by
  dsimp [finPrefixNat, Iso.trans, Iso.sum, finPlusNat]
  omega

/-- Recursive payloads are bounded by their finite-recursive branch code. -/
theorem finiteRecursiveNat_payload_le
    (finite recursive : Nat) (hrec : 0 < recursive)
    (p : Fin recursive × Nat) :
    p.2 ≤ (finiteRecursiveNat finite recursive hrec).toFun (Sum.inr p) := by
  dsimp [finiteRecursiveNat]
  exact Nat.le_trans
    (finProdNat_toFun_snd_le recursive hrec p)
    (by
      dsimp [finPrefixNat, Iso.trans, Iso.sum, finPlusNat]
      omega)

/--
If either the finite prefix is nonempty or the recursive tag is nonzero, the
recursive payload is strictly below its finite-recursive branch code.
-/
theorem finiteRecursiveNat_payload_lt_of_prefix_or_tag
    (finite recursive : Nat) (hrec : 0 < recursive)
    (p : Fin recursive × Nat)
    (hslack : 0 < finite ∨ 0 < p.1.val) :
    p.2 < (finiteRecursiveNat finite recursive hrec).toFun (Sum.inr p) := by
  dsimp [finiteRecursiveNat, finPrefixNat, Iso.trans, Iso.sum, finPlusNat, finProdNat]
  cases hslack with
  | inl hfinite =>
      have hmul : p.2 ≤ recursive * p.2 := by
        calc
          p.2 = 1 * p.2 := by rw [Nat.one_mul]
          _ ≤ recursive * p.2 := Nat.mul_le_mul_right p.2 hrec
      omega
  | inr htag =>
      have hmul : p.2 ≤ recursive * p.2 := by
        calc
          p.2 = 1 * p.2 := by rw [Nat.one_mul]
          _ ≤ recursive * p.2 := Nat.mul_le_mul_right p.2 hrec
      omega

/-- Two finite recursive branch families encoded as one natural-number family. -/
def finSumProdNat (left right : Nat) (hleft : 0 < left) (hright : 0 < right) :
    ((Fin left × Nat) ⊕ (Fin right × Nat)) ≃ᵢ Nat :=
  Iso.trans
    (Iso.sum (finProdNat left hleft) (finProdNat right hright))
    sumNat

theorem finSumProdNat_toFun_inl_snd_le
    (left right : Nat) (hleft : 0 < left) (hright : 0 < right)
    (p : Fin left × Nat) :
    p.2 ≤ (finSumProdNat left right hleft hright).toFun (Sum.inl p) := by
  have hpayload := finProdNat_toFun_snd_le left hleft p
  dsimp [finSumProdNat, Iso.trans, Iso.sum, sumNat]
  omega

theorem finSumProdNat_toFun_inr_snd_lt
    (left right : Nat) (hleft : 0 < left) (hright : 0 < right)
    (p : Fin right × Nat) :
    p.2 < (finSumProdNat left right hleft hright).toFun (Sum.inr p) := by
  have hpayload := finProdNat_toFun_snd_le right hright p
  dsimp [finSumProdNat, Iso.trans, Iso.sum, sumNat]
  omega

def finProdProdNat (k : Nat) (hk : 0 < k) :
    (Fin k × (Nat × Nat)) ≃ᵢ Nat :=
  Iso.trans (Iso.prod (Iso.refl (Fin k)) prodNat) (finProdNat k hk)

theorem finProdProdNat_toFun_snd_fst_le (k : Nat) (hk : 0 < k)
    (p : Fin k × (Nat × Nat)) :
    p.2.1 ≤ (finProdProdNat k hk).toFun p := by
  dsimp [finProdProdNat, Iso.trans, Iso.prod]
  exact Nat.le_trans (prodNat_toFun_fst_le p.2)
    (finProdNat_toFun_snd_le k hk (p.1, prodNat.toFun p.2))

theorem finProdProdNat_toFun_snd_snd_le (k : Nat) (hk : 0 < k)
    (p : Fin k × (Nat × Nat)) :
    p.2.2 ≤ (finProdProdNat k hk).toFun p := by
  dsimp [finProdProdNat, Iso.trans, Iso.prod]
  exact Nat.le_trans (prodNat_toFun_snd_le p.2)
    (finProdNat_toFun_snd_le k hk (p.1, prodNat.toFun p.2))

def natProdProdNat : (Nat × (Nat × Nat)) ≃ᵢ Nat :=
  Iso.trans (Iso.prod (Iso.refl Nat) prodNat) prodNat

theorem natProdProdNat_toFun_snd_fst_le (p : Nat × (Nat × Nat)) :
    p.2.1 ≤ natProdProdNat.toFun p := by
  dsimp [natProdProdNat, Iso.trans, Iso.prod]
  exact Nat.le_trans (prodNat_toFun_fst_le p.2)
    (prodNat_toFun_snd_le (p.1, prodNat.toFun p.2))

theorem natProdProdNat_toFun_snd_snd_le (p : Nat × (Nat × Nat)) :
    p.2.2 ≤ natProdProdNat.toFun p := by
  dsimp [natProdProdNat, Iso.trans, Iso.prod]
  exact Nat.le_trans (prodNat_toFun_snd_le p.2)
    (prodNat_toFun_snd_le (p.1, prodNat.toFun p.2))

/--
Code a possibly empty finite-tagged product together with a plain `Nat` tail.
When the finite side is empty, the tail is coded by the identity; otherwise the
finite product occupies the even numbers and the tail occupies the odd numbers.
-/
def finProdNatOrNat (k : Nat) : ((Fin k × Nat) ⊕ Nat) ≃ᵢ Nat where
  toFun
    | Sum.inl p =>
        if h : 0 < k then
          2 * (finProdNat k h).toFun p
        else
          False.elim (Nat.not_lt_zero p.1.val (by
            have hzero : k = 0 := Nat.eq_zero_of_not_pos h
            simpa [hzero] using p.1.isLt))
    | Sum.inr n =>
        if k = 0 then n else 2 * n + 1
  invFun n :=
    if h : 0 < k then
      if hp : n % 2 = 0 then
        Sum.inl ((finProdNat k h).invFun (n / 2))
      else
        Sum.inr (n / 2)
    else
      Sum.inr n
  left_inv := by
    intro x
    cases x with
    | inl p =>
        dsimp
        by_cases h : 0 < k
        · let code := (finProdNat k h).toFun p
          have hmod : (2 * code) % 2 = 0 := Nat.mul_mod_right 2 code
          have hdiv : (2 * code) / 2 = code :=
            Nat.mul_div_right code (by decide : 0 < 2)
          simp [h, hmod, hdiv, code]
        · exact False.elim (Nat.not_lt_zero p.1.val (by
            have hzero : k = 0 := Nat.eq_zero_of_not_pos h
            simpa [hzero] using p.1.isLt))
    | inr n =>
        dsimp
        by_cases hk0 : k = 0
        · simp [hk0, Nat.lt_irrefl]
        · have hpos : 0 < k := Nat.pos_of_ne_zero hk0
          have hmod : (2 * n + 1) % 2 ≠ 0 := by
            have hcalc : (2 * n + 1) % 2 = 1 := by
              calc
                (2 * n + 1) % 2 = (1 + 2 * n) % 2 := by rw [Nat.add_comm]
                _ = 1 % 2 := Nat.add_mul_mod_self_left 1 2 n
                _ = 1 := Nat.mod_eq_of_lt (by decide : 1 < 2)
            omega
          have hdiv : (2 * n + 1) / 2 = n := by
            calc
              (2 * n + 1) / 2 = (1 + n * 2) / 2 := by
                rw [Nat.add_comm, Nat.mul_comm 2 n]
              _ = 1 / 2 + n := Nat.add_mul_div_right 1 n (by decide : 0 < 2)
              _ = n := by
                rw [Nat.div_eq_of_lt (by decide : 1 < 2)]
                exact Nat.zero_add n
          simp [hpos, hk0, hdiv]
  right_inv := by
    intro n
    dsimp
    by_cases h : 0 < k
    · by_cases hp : n % 2 = 0
      · simp [h, hp]
        have hsplit := Nat.div_add_mod n 2
        omega
      · simp [h, hp]
        have hne : ¬k = 0 := Nat.ne_of_gt h
        have hsplit := Nat.div_add_mod n 2
        rcases Nat.mod_two_eq_zero_or_one n with h0 | h1
        · exact False.elim (hp h0)
        · simp [hne]
          omega
    · have hzero : k = 0 := Nat.eq_zero_of_not_pos h
      simp [hzero]

theorem finProdNatOrNat_inl_snd_le (k : Nat) (p : Fin k × Nat) :
    p.2 ≤ (finProdNatOrNat k).toFun (Sum.inl p) := by
  dsimp [finProdNatOrNat]
  by_cases h : 0 < k
  · have hpayload : p.2 ≤ (finProdNat k h).toFun p :=
      finProdNat_toFun_snd_le k h p
    simp [h]
    omega
  · exact False.elim (Nat.not_lt_zero p.1.val (by
      have hzero : k = 0 := Nat.eq_zero_of_not_pos h
      simpa [hzero] using p.1.isLt))

theorem finProdNatOrNat_inr_le (k n : Nat) :
    n ≤ (finProdNatOrNat k).toFun (Sum.inr n) := by
  dsimp [finProdNatOrNat]
  by_cases h : k = 0
  · simp [h]
  · simp [h]
    omega

theorem finProdNatOrNat_inr_lt_of_pos {k n : Nat} (hk : 0 < k) :
    n < (finProdNatOrNat k).toFun (Sum.inr n) := by
  have hk0 : ¬k = 0 := Nat.ne_of_gt hk
  dsimp [finProdNatOrNat]
  simp [hk0]
  omega

/--
Code either a bare finite tag or a recursive product with the same tag into a
finite tag paired with a natural payload. Payload zero is reserved for the bare
tag; positive payloads decode through `prodNat`.
-/
def finTaggedProdNat (k : Nat) :
    (Fin k ⊕ ((Fin k × Nat) × Nat)) ≃ᵢ (Fin k × Nat) where
  toFun
    | Sum.inl tag => (tag, 0)
    | Sum.inr p => (p.1.1, prodNat.toFun (p.1.2, p.2) + 1)
  invFun
    | (tag, 0) => Sum.inl tag
    | (tag, n + 1) =>
        let p := prodNat.invFun n
        Sum.inr ((tag, p.1), p.2)
  left_inv := by
    intro x
    cases x with
    | inl tag => rfl
    | inr p =>
        cases p with
        | mk fn arg =>
          cases fn with
          | mk tag payload =>
            dsimp
            rw [prodNat.left_inv (payload, arg)]
  right_inv := by
    intro code
    cases code with
    | mk tag n =>
      cases n with
      | zero => rfl
      | succ n =>
          dsimp
          rw [prodNat.right_inv n]

theorem finTaggedProdNat_inr_fst_payload_le (k : Nat)
    (p : (Fin k × Nat) × Nat) :
    p.1.2 ≤ ((finTaggedProdNat k).toFun (Sum.inr p)).2 := by
  dsimp [finTaggedProdNat]
  exact Nat.le_trans (prodNat_toFun_fst_le (p.1.2, p.2)) (Nat.le_succ _)

theorem finTaggedProdNat_inr_fst_payload_lt (k : Nat)
    (p : (Fin k × Nat) × Nat) :
    p.1.2 < ((finTaggedProdNat k).toFun (Sum.inr p)).2 := by
  dsimp [finTaggedProdNat]
  exact Nat.lt_succ_of_le (prodNat_toFun_fst_le (p.1.2, p.2))

theorem finTaggedProdNat_inr_snd_le (k : Nat)
    (p : (Fin k × Nat) × Nat) :
    p.2 ≤ ((finTaggedProdNat k).toFun (Sum.inr p)).2 := by
  dsimp [finTaggedProdNat]
  exact Nat.le_trans (prodNat_toFun_snd_le (p.1.2, p.2)) (Nat.le_succ _)

theorem finTaggedProdNat_inr_snd_lt (k : Nat)
    (p : (Fin k × Nat) × Nat) :
    p.2 < ((finTaggedProdNat k).toFun (Sum.inr p)).2 := by
  dsimp [finTaggedProdNat]
  exact Nat.lt_succ_of_le (prodNat_toFun_snd_le (p.1.2, p.2))

/-- Put two natural numbers into nondecreasing order. -/
def sortNatPair (a b : Nat) : {p : Nat × Nat // p.1 ≤ p.2} :=
  if h : a ≤ b then
    ⟨(a, b), h⟩
  else
    ⟨(b, a), Nat.le_of_not_ge h⟩

theorem sortNatPair_of_le {a b : Nat} (h : a ≤ b) :
    sortNatPair a b = ⟨(a, b), h⟩ := by
  simp [sortNatPair, h]

theorem sortNatPair_comm (a b : Nat) :
    sortNatPair a b = sortNatPair b a := by
  by_cases hab : a ≤ b
  · by_cases hba : b ≤ a
    · have h : a = b := Nat.le_antisymm hab hba
      cases h
      apply Subtype.ext
      rfl
    · rw [sortNatPair_of_le hab]
      simp [sortNatPair, hba]
  · have hba : b ≤ a := Nat.le_of_not_ge hab
    rw [sortNatPair_of_le hba]
    simp [sortNatPair, hab]

/-- Unordered pairs of natural numbers are coded by the smaller element and
the distance to the larger element. -/
def unorderedPairNat : {p : Nat × Nat // p.1 ≤ p.2} ≃ᵢ Nat where
  toFun p := prodNat.toFun (p.val.1, p.val.2 - p.val.1)
  invFun n :=
    let p := prodNat.invFun n
    ⟨(p.1, p.1 + p.2), by omega⟩
  left_inv := by
    intro p
    apply Subtype.ext
    cases p with
    | mk p hp =>
      cases p with
      | mk a b =>
        dsimp
        rw [prodNat.left_inv]
        simp
        omega
  right_inv := by
    intro n
    dsimp
    rw [Nat.add_sub_cancel_left]
    exact prodNat.right_inv n

def unorderedPairCode (a b : Nat) : Nat :=
  unorderedPairNat.toFun (sortNatPair a b)

theorem unorderedPairCode_comm (a b : Nat) :
    unorderedPairCode a b = unorderedPairCode b a := by
  simp [unorderedPairCode, sortNatPair_comm a b]

theorem unorderedPairCode_invFun (n : Nat) :
    unorderedPairCode (unorderedPairNat.invFun n).val.1
      (unorderedPairNat.invFun n).val.2 = n := by
  unfold unorderedPairCode
  have hsort :
      sortNatPair (unorderedPairNat.invFun n).val.1
          (unorderedPairNat.invFun n).val.2 =
        unorderedPairNat.invFun n := by
    exact sortNatPair_of_le (unorderedPairNat.invFun n).property
  rw [hsort]
  exact unorderedPairNat.right_inv n

theorem unorderedPairNat_inv_unorderedPairCode_of_le {a b : Nat}
    (h : a ≤ b) :
    unorderedPairNat.invFun (unorderedPairCode a b) = ⟨(a, b), h⟩ := by
  unfold unorderedPairCode
  rw [sortNatPair_of_le h]
  exact unorderedPairNat.left_inv ⟨(a, b), h⟩

theorem unorderedPairNat_inv_unorderedPairCode_of_not_le {a b : Nat}
    (h : ¬a ≤ b) :
    unorderedPairNat.invFun (unorderedPairCode a b) =
      ⟨(b, a), Nat.le_of_not_ge h⟩ := by
  rw [unorderedPairCode_comm]
  exact unorderedPairNat_inv_unorderedPairCode_of_le (Nat.le_of_not_ge h)

end CodeAlgebra
end BijForm
