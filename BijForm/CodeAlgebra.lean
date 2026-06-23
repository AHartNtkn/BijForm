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
  have hright := Iso.toFun_eq_of_invFun_eq (finPlusNat k) h
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
      · exact fin_eq_of_val_eq (by
          calc
          (i.val + k * n) % k = i.val % k := Nat.add_mul_mod_self_left i.val k n
          _ = i.val := Nat.mod_eq_of_lt i.isLt)
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

/-- Encode a finite tag paired with a payload by first coding the payload as
`Nat`, then using the finite-product Nat codec. -/
def toNatFinProd {α : Type u} (k : Nat) (hk : 0 < k)
    (payload : α ≃ᵢ Nat) : (Fin k × α) ≃ᵢ Nat :=
  Iso.trans (Iso.prod (Iso.refl (Fin k)) payload) (finProdNat k hk)

theorem toNatFinProd_payloadCode_le {α : Type u}
    (k : Nat) (hk : 0 < k) (payload : α ≃ᵢ Nat) (p : Fin k × α) :
    payload.toFun p.2 ≤ (toNatFinProd k hk payload).toFun p := by
  dsimp [toNatFinProd, Iso.trans, Iso.prod]
  exact finProdNat_toFun_snd_le k hk (p.1, payload.toFun p.2)

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
      exact fin_eq_of_val_eq (Nat.add_sub_of_le hle)

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
      · exact fin_eq_of_val_eq (by
          calc
          (i.val * b + j.val) / b = (b * i.val + j.val) / b := by
            rw [Nat.mul_comm i.val b]
          _ = i.val + j.val / b := Nat.mul_add_div hb i.val j.val
          _ = i.val := by rw [Nat.div_eq_of_lt j.isLt, Nat.add_zero])
      · exact fin_eq_of_val_eq (by
          calc
          (i.val * b + j.val) % b = j.val % b := Nat.mul_add_mod_self_right i.val b j.val
          _ = j.val := Nat.mod_eq_of_lt j.isLt)
  right_inv := by
    intro k
    exact fin_eq_of_val_eq (by
      calc
      (k.val / b) * b + k.val % b = b * (k.val / b) + k.val % b := by
        rw [Nat.mul_comm]
      _ = k.val := Nat.div_add_mod k.val b)

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
  have hright := Iso.toFun_eq_of_invFun_eq sumNat h
  simp [sumNat] at hright
  omega

theorem sumNat_inr_le {n a : Nat}
    (h : sumNat.invFun n = Sum.inr a) : a ≤ n := by
  have hright := Iso.toFun_eq_of_invFun_eq sumNat h
  simp [sumNat] at hright
  omega

/-- Encode a sum into `Nat` by first coding each side as `Nat`, then using
the standard binary Nat sum codec. -/
def toNatSum {α : Type u} {β : Type v}
    (left : α ≃ᵢ Nat) (right : β ≃ᵢ Nat) : (α ⊕ β) ≃ᵢ Nat :=
  Iso.trans (Iso.sum left right) sumNat

theorem toNatSum_inl_le_of_le {α : Type u} {β : Type v}
    (left : α ≃ᵢ Nat) (right : β ≃ᵢ Nat) {a : α} {m : Nat}
    (h : m ≤ left.toFun a) :
    m ≤ (toNatSum left right).toFun (Sum.inl a) := by
  dsimp [toNatSum, Iso.trans, Iso.sum, sumNat]
  omega

theorem toNatSum_inr_lt_of_le {α : Type u} {β : Type v}
    (left : α ≃ᵢ Nat) (right : β ≃ᵢ Nat) {b : β} {m : Nat}
    (h : m ≤ right.toFun b) :
    m < (toNatSum left right).toFun (Sum.inr b) := by
  dsimp [toNatSum, Iso.trans, Iso.sum, sumNat]
  omega

theorem toNatSum_inr_lt_of_lt {α : Type u} {β : Type v}
    (left : α ≃ᵢ Nat) (right : β ≃ᵢ Nat) {b : β} {m : Nat}
    (h : m < right.toFun b) :
    m < (toNatSum left right).toFun (Sum.inr b) :=
  toNatSum_inr_lt_of_le left right (Nat.le_of_lt h)

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

/-- Encode a product into `Nat` by first coding each component as `Nat`, then
using the standard pairing codec. -/
def toNatProd {α : Type u} {β : Type v}
    (left : α ≃ᵢ Nat) (right : β ≃ᵢ Nat) : (α × β) ≃ᵢ Nat :=
  Iso.trans (Iso.prod left right) prodNat

theorem toNatProd_leftCode_le {α : Type u} {β : Type v}
    (left : α ≃ᵢ Nat) (right : β ≃ᵢ Nat) (p : α × β) :
    left.toFun p.1 ≤ (toNatProd left right).toFun p := by
  dsimp [toNatProd, Iso.trans, Iso.prod]
  exact prodNat_toFun_fst_le (left.toFun p.1, right.toFun p.2)

theorem toNatProd_rightCode_le {α : Type u} {β : Type v}
    (left : α ≃ᵢ Nat) (right : β ≃ᵢ Nat) (p : α × β) :
    right.toFun p.2 ≤ (toNatProd left right).toFun p := by
  dsimp [toNatProd, Iso.trans, Iso.prod]
  exact prodNat_toFun_snd_le (left.toFun p.1, right.toFun p.2)

/-- A rank/projection is bounded by a codec after embedding into its carrier. -/
def SubcodeLe {α : Type u} {β : Type v}
    (codec : α ≃ᵢ Nat) (embed : β → α) (rank : β → Nat) : Prop :=
  ∀ b, rank b ≤ codec.toFun (embed b)

/-- A rank/projection is strictly bounded by a codec after embedding. -/
def SubcodeLt {α : Type u} {β : Type v}
    (codec : α ≃ᵢ Nat) (embed : β → α) (rank : β → Nat) : Prop :=
  ∀ b, rank b < codec.toFun (embed b)

theorem subcode_nat_id : SubcodeLe (Iso.refl Nat) id id :=
  fun _ => Nat.le_refl _

theorem subcode_prodNat_fst : SubcodeLe prodNat id Prod.fst :=
  prodNat_toFun_fst_le

theorem subcode_prodNat_snd : SubcodeLe prodNat id Prod.snd :=
  prodNat_toFun_snd_le

theorem subcode_finProdNat_snd (k : Nat) (hk : 0 < k) :
    SubcodeLe (finProdNat k hk) id Prod.snd :=
  finProdNat_toFun_snd_le k hk

theorem SubcodeLe.isoTrans {α : Type u} {β : Type v} {γ : Type w}
    {front : α ≃ᵢ β} {codec : β ≃ᵢ Nat}
    {embed : γ → α} {rank : γ → Nat}
    (h : SubcodeLe codec (fun x => front.toFun (embed x)) rank) :
    SubcodeLe (Iso.trans front codec) embed rank :=
  fun x => h x

theorem SubcodeLt.isoTrans {α : Type u} {β : Type v} {γ : Type w}
    {front : α ≃ᵢ β} {codec : β ≃ᵢ Nat}
    {embed : γ → α} {rank : γ → Nat}
    (h : SubcodeLt codec (fun x => front.toFun (embed x)) rank) :
    SubcodeLt (Iso.trans front codec) embed rank :=
  fun x => h x

theorem SubcodeLe.toNatSum_inl {α : Type u} {β : Type v} {γ : Type w}
    {left : α ≃ᵢ Nat} {right : β ≃ᵢ Nat}
    {embed : γ → α} {rank : γ → Nat}
    (h : SubcodeLe left embed rank) :
    SubcodeLe (toNatSum left right) (fun x => Sum.inl (embed x)) rank :=
  fun x => toNatSum_inl_le_of_le left right (h x)

theorem SubcodeLe.toNatSum_inr_lt {α : Type u} {β : Type v} {γ : Type w}
    {left : α ≃ᵢ Nat} {right : β ≃ᵢ Nat}
    {embed : γ → β} {rank : γ → Nat}
    (h : SubcodeLe right embed rank) :
    SubcodeLt (toNatSum left right) (fun x => Sum.inr (embed x)) rank :=
  fun x => toNatSum_inr_lt_of_le left right (h x)

theorem SubcodeLt.toNatSum_inr {α : Type u} {β : Type v} {γ : Type w}
    {left : α ≃ᵢ Nat} {right : β ≃ᵢ Nat}
    {embed : γ → β} {rank : γ → Nat}
    (h : SubcodeLt right embed rank) :
    SubcodeLt (toNatSum left right) (fun x => Sum.inr (embed x)) rank :=
  fun x => toNatSum_inr_lt_of_lt left right (h x)

theorem SubcodeLe.toNatProd_left {α : Type u} {β : Type v} {γ : Type w}
    {left : α ≃ᵢ Nat} {right : β ≃ᵢ Nat}
    {embed : γ → α} {fill : γ → β} {rank : γ → Nat}
    (h : SubcodeLe left embed rank) :
    SubcodeLe (toNatProd left right) (fun x => (embed x, fill x)) rank :=
  fun x => Nat.le_trans (h x) (toNatProd_leftCode_le left right (embed x, fill x))

theorem SubcodeLe.toNatProd_right {α : Type u} {β : Type v} {γ : Type w}
    {left : α ≃ᵢ Nat} {right : β ≃ᵢ Nat}
    {fill : γ → α} {embed : γ → β} {rank : γ → Nat}
    (h : SubcodeLe right embed rank) :
    SubcodeLe (toNatProd left right) (fun x => (fill x, embed x)) rank :=
  fun x => Nat.le_trans (h x) (toNatProd_rightCode_le left right (fill x, embed x))

theorem SubcodeLe.toNatFinProd_payload {α : Type u} {β : Type v}
    (k : Nat) (hk : 0 < k) {payload : α ≃ᵢ Nat}
    {fill : β → Fin k} {embed : β → α} {rank : β → Nat}
    (h : SubcodeLe payload embed rank) :
    SubcodeLe (toNatFinProd k hk payload) (fun x => (fill x, embed x)) rank :=
  fun x => Nat.le_trans (h x)
    (toNatFinProd_payloadCode_le k hk payload (fill x, embed x))

def sumProdNat : (Nat ⊕ (Nat × Nat)) ≃ᵢ Nat :=
  toNatSum (Iso.refl Nat) prodNat

@[simp]
theorem sumProdNat_toFun_inl_le (n : Nat) :
    n ≤ sumProdNat.toFun (Sum.inl n) :=
  toNatSum_inl_le_of_le (Iso.refl Nat) prodNat (Nat.le_refl n)

@[simp]
theorem sumProdNat_toFun_inr_fst_lt (p : Nat × Nat) :
    p.1 < sumProdNat.toFun (Sum.inr p) :=
  toNatSum_inr_lt_of_le (Iso.refl Nat) prodNat
    (prodNat_toFun_fst_le p)

@[simp]
theorem sumProdNat_toFun_inr_snd_lt (p : Nat × Nat) :
    p.2 < sumProdNat.toFun (Sum.inr p) :=
  toNatSum_inr_lt_of_le (Iso.refl Nat) prodNat
    (prodNat_toFun_snd_le p)

@[simp]
theorem sumProdNat_toFun_inr_fst_pair_lt (a b : Nat) :
    a < sumProdNat.toFun (Sum.inr (a, b)) :=
  sumProdNat_toFun_inr_fst_lt (a, b)

@[simp]
theorem sumProdNat_toFun_inr_snd_pair_lt (a b : Nat) :
    b < sumProdNat.toFun (Sum.inr (a, b)) :=
  sumProdNat_toFun_inr_snd_lt (a, b)

theorem sumProdNat_invFun_inr_fst_lt {n a b : Nat}
    (h : sumProdNat.invFun n = Sum.inr (a, b)) : a < n := by
  have hright := Iso.toFun_eq_of_invFun_eq sumProdNat h
  have hlt :
      a < sumProdNat.toFun (Sum.inr (a, b)) :=
    sumProdNat_toFun_inr_fst_lt (a, b)
  rw [hright] at hlt
  exact hlt

theorem sumProdNat_invFun_inr_snd_lt {n a b : Nat}
    (h : sumProdNat.invFun n = Sum.inr (a, b)) : b < n := by
  have hright := Iso.toFun_eq_of_invFun_eq sumProdNat h
  have hlt :
      b < sumProdNat.toFun (Sum.inr (a, b)) :=
    sumProdNat_toFun_inr_snd_lt (a, b)
  rw [hright] at hlt
  exact hlt

def natOrProdOrProdNat :
    (Nat ⊕ ((Nat × Nat) ⊕ (Nat × Nat))) ≃ᵢ Nat :=
  toNatSum (Iso.refl Nat) (toNatSum prodNat prodNat)

def prodOrNatOrProdOrNat :
    ((Nat × Nat) ⊕ (Nat ⊕ ((Nat × Nat) ⊕ Nat))) ≃ᵢ Nat :=
  toNatSum prodNat (toNatSum (Iso.refl Nat) (toNatSum prodNat (Iso.refl Nat)))

def finPrefixNat {α : Type u} (k : Nat) (tail : α ≃ᵢ Nat) :
    (Fin k ⊕ α) ≃ᵢ Nat :=
  Iso.trans (Iso.sum (Iso.refl (Fin k)) tail) (finPlusNat k)

/-- Finite constructor branches plus finitely tagged recursive `Nat` branches. -/
def finiteRecursiveNat (finite recursive : Nat) (hrec : 0 < recursive) :
    (Fin finite ⊕ (Fin recursive × Nat)) ≃ᵢ Nat :=
  finPrefixNat finite (finProdNat recursive hrec)

theorem prefixTail_lt_of_lt {α : Type u}
    (k : Nat) (tail : α ≃ᵢ Nat) {a : α} {m : Nat}
    (h : m < tail.toFun a) :
    m < (finPrefixNat k tail).toFun (Sum.inr a) := by
  dsimp [finPrefixNat, Iso.trans, Iso.sum, finPlusNat]
  omega

theorem prefixTail_lt_of_le {α : Type u}
    (k : Nat) (hk : 0 < k) (tail : α ≃ᵢ Nat) {a : α} {m : Nat}
    (h : m ≤ tail.toFun a) :
    m < (finPrefixNat k tail).toFun (Sum.inr a) := by
  dsimp [finPrefixNat, Iso.trans, Iso.sum, finPlusNat]
  omega

theorem SubcodeLt.prefixTail {α : Type u} {β : Type v}
    {tail : α ≃ᵢ Nat} {embed : β → α} {rank : β → Nat}
    (k : Nat) (h : SubcodeLt tail embed rank) :
    SubcodeLt (finPrefixNat k tail) (fun x => Sum.inr (embed x)) rank :=
  fun x => prefixTail_lt_of_lt k tail (h x)

theorem SubcodeLe.prefixTailOfPos {α : Type u} {β : Type v}
    {tail : α ≃ᵢ Nat} {embed : β → α} {rank : β → Nat}
    (k : Nat) (hk : 0 < k) (h : SubcodeLe tail embed rank) :
    SubcodeLt (finPrefixNat k tail) (fun x => Sum.inr (embed x)) rank :=
  fun x => prefixTail_lt_of_le k hk tail (h x)

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
  have hmul : p.2 ≤ recursive * p.2 := by
    calc
      p.2 = 1 * p.2 := by rw [Nat.one_mul]
      _ ≤ recursive * p.2 := Nat.mul_le_mul_right p.2 hrec
  cases hslack with
  | inl hfinite =>
      omega
  | inr htag =>
      omega

/-- Two finite recursive branch families encoded as one natural-number family. -/
def finSumProdNat (left right : Nat) (hleft : 0 < left) (hright : 0 < right) :
    ((Fin left × Nat) ⊕ (Fin right × Nat)) ≃ᵢ Nat :=
  toNatSum (finProdNat left hleft) (finProdNat right hright)

theorem finSumProdNat_toFun_inl_snd_le
    (left right : Nat) (hleft : 0 < left) (hright : 0 < right)
    (p : Fin left × Nat) :
    p.2 ≤ (finSumProdNat left right hleft hright).toFun (Sum.inl p) := by
  exact toNatSum_inl_le_of_le (finProdNat left hleft) (finProdNat right hright)
    (finProdNat_toFun_snd_le left hleft p)

theorem finSumProdNat_toFun_inr_snd_lt
    (left right : Nat) (hleft : 0 < left) (hright : 0 < right)
    (p : Fin right × Nat) :
    p.2 < (finSumProdNat left right hleft hright).toFun (Sum.inr p) := by
  exact toNatSum_inr_lt_of_le (finProdNat left hleft) (finProdNat right hright)
    (finProdNat_toFun_snd_le right hright p)

def finProdProdNat (k : Nat) (hk : 0 < k) :
    (Fin k × (Nat × Nat)) ≃ᵢ Nat :=
  toNatFinProd k hk prodNat

theorem subcode_finProdProdNat_snd_fst (k : Nat) (hk : 0 < k) :
    SubcodeLe (finProdProdNat k hk) id (fun p : Fin k × (Nat × Nat) => p.2.1) :=
  fun p => Nat.le_trans (prodNat_toFun_fst_le p.2)
    (toNatFinProd_payloadCode_le k hk prodNat p)

theorem subcode_finProdProdNat_snd_snd (k : Nat) (hk : 0 < k) :
    SubcodeLe (finProdProdNat k hk) id (fun p : Fin k × (Nat × Nat) => p.2.2) :=
  fun p => Nat.le_trans (prodNat_toFun_snd_le p.2)
    (toNatFinProd_payloadCode_le k hk prodNat p)

theorem finProdProdNat_toFun_snd_fst_le (k : Nat) (hk : 0 < k)
    (p : Fin k × (Nat × Nat)) :
    p.2.1 ≤ (finProdProdNat k hk).toFun p := by
  exact subcode_finProdProdNat_snd_fst k hk p

theorem finProdProdNat_toFun_snd_snd_le (k : Nat) (hk : 0 < k)
    (p : Fin k × (Nat × Nat)) :
    p.2.2 ≤ (finProdProdNat k hk).toFun p := by
  exact subcode_finProdProdNat_snd_snd k hk p

def natProdProdNat : (Nat × (Nat × Nat)) ≃ᵢ Nat :=
  toNatProd (Iso.refl Nat) prodNat

theorem subcode_natProdProdNat_snd_fst :
    SubcodeLe natProdProdNat id (fun p : Nat × (Nat × Nat) => p.2.1) :=
  fun p => Nat.le_trans (prodNat_toFun_fst_le p.2)
    (toNatProd_rightCode_le (Iso.refl Nat) prodNat p)

theorem subcode_natProdProdNat_snd_snd :
    SubcodeLe natProdProdNat id (fun p : Nat × (Nat × Nat) => p.2.2) :=
  fun p => Nat.le_trans (prodNat_toFun_snd_le p.2)
    (toNatProd_rightCode_le (Iso.refl Nat) prodNat p)

theorem natProdProdNat_toFun_snd_fst_le (p : Nat × (Nat × Nat)) :
    p.2.1 ≤ natProdProdNat.toFun p := by
  exact subcode_natProdProdNat_snd_fst p

theorem natProdProdNat_toFun_snd_snd_le (p : Nat × (Nat × Nat)) :
    p.2.2 ≤ natProdProdNat.toFun p := by
  exact subcode_natProdProdNat_snd_snd p

/--
Code a possibly empty finite-tagged product together with a plain `Nat` tail.
When the finite side is empty, the tail is coded by the identity; otherwise the
finite product occupies the even numbers and the tail occupies the odd numbers.
-/
def finProdNatOrNat (k : Nat) : ((Fin k × Nat) ⊕ Nat) ≃ᵢ Nat := by
  if h : 0 < k then
    exact toNatSum (finProdNat k h) (Iso.refl Nat)
  else
    exact
      { toFun
          | Sum.inl p =>
              have hzero : k = 0 := Nat.eq_zero_of_not_pos h
              fin_zero_elim (hzero ▸ p.1)
          | Sum.inr n => n
        invFun := Sum.inr
        left_inv := by
          intro x
          cases x with
          | inl p =>
              have hzero : k = 0 := Nat.eq_zero_of_not_pos h
              exact fin_zero_elim (hzero ▸ p.1)
          | inr n => rfl
        right_inv := by
          intro n
          rfl }

theorem finProdNatOrNat_eq_toNatSum_of_pos {k : Nat} (h : 0 < k) :
    finProdNatOrNat k = toNatSum (finProdNat k h) (Iso.refl Nat) := by
  simp [finProdNatOrNat, h]

theorem finProdNatOrNat_inl_snd_le (k : Nat) (p : Fin k × Nat) :
    p.2 ≤ (finProdNatOrNat k).toFun (Sum.inl p) := by
  by_cases h : 0 < k
  · rw [finProdNatOrNat_eq_toNatSum_of_pos h]
    exact toNatSum_inl_le_of_le (finProdNat k h) (Iso.refl Nat)
      (finProdNat_toFun_snd_le k h p)
  · have hzero : k = 0 := Nat.eq_zero_of_not_pos h
    exact fin_zero_elim (hzero ▸ p.1)

theorem finProdNatOrNat_inr_le (k n : Nat) :
    n ≤ (finProdNatOrNat k).toFun (Sum.inr n) := by
  by_cases h : 0 < k
  · rw [finProdNatOrNat_eq_toNatSum_of_pos h]
    exact Nat.le_of_lt
      (toNatSum_inr_lt_of_le (finProdNat k h) (Iso.refl Nat) (Nat.le_refl n))
  · simp [finProdNatOrNat, h]

theorem finProdNatOrNat_inr_lt_of_pos {k n : Nat} (hk : 0 < k) :
    n < (finProdNatOrNat k).toFun (Sum.inr n) := by
  rw [finProdNatOrNat_eq_toNatSum_of_pos hk]
  exact toNatSum_inr_lt_of_le (finProdNat k hk) (Iso.refl Nat) (Nat.le_refl n)

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

theorem sumNat_unorderedPairCode_swap (a b : Nat) :
    sumNat.toFun (Sum.inr (unorderedPairCode a b)) =
      sumNat.toFun (Sum.inr (unorderedPairCode b a)) := by
  rw [unorderedPairCode_comm]

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

theorem unorderedPairNat_invFun_fst_le (n : Nat) :
    (unorderedPairNat.invFun n).val.1 ≤ n := by
  dsimp [unorderedPairNat]
  exact prodNat_fst_le n

theorem unorderedPairNat_invFun_snd_le_twice (n : Nat) :
    (unorderedPairNat.invFun n).val.2 ≤ 2 * n := by
  dsimp [unorderedPairNat]
  have hfst := prodNat_fst_le n
  have hsnd := prodNat_snd_le n
  omega

theorem unorderedPairNat_invFun_fst_lt_sumNat_inr (n : Nat) :
    (unorderedPairNat.invFun n).val.1 < sumNat.toFun (Sum.inr n) := by
  have hfst := unorderedPairNat_invFun_fst_le n
  dsimp [sumNat]
  omega

theorem unorderedPairNat_invFun_snd_lt_sumNat_inr (n : Nat) :
    (unorderedPairNat.invFun n).val.2 < sumNat.toFun (Sum.inr n) := by
  have hsnd := unorderedPairNat_invFun_snd_le_twice n
  dsimp [sumNat]
  omega

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
