import BijForm.Coding
import BijForm.Pairing

namespace BijForm
namespace CodeAlgebra

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

end CodeAlgebra
end BijForm
