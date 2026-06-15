import BijForm.Coding
import BijForm.Pairing

namespace BijForm
namespace NatCoding

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

end NatCoding
end BijForm
