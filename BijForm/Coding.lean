import Std

namespace BijForm

/-- A concrete bijection, kept local so the project does not need mathlib's
`Equiv` while the formalization is still dependency-free. -/
structure Iso (α : Sort u) (β : Sort v) where
  toFun : α → β
  invFun : β → α
  left_inv : Function.LeftInverse invFun toFun
  right_inv : Function.RightInverse invFun toFun

namespace Iso

infix:25 " ≃ᵢ " => Iso

@[simp]
theorem left {α : Sort u} {β : Sort v} (e : α ≃ᵢ β) (a : α) :
    e.invFun (e.toFun a) = a :=
  e.left_inv a

@[simp]
theorem right {α : Sort u} {β : Sort v} (e : α ≃ᵢ β) (b : β) :
    e.toFun (e.invFun b) = b :=
  e.right_inv b

theorem toFun_eq_of_invFun_eq {α : Sort u} {β : Sort v}
    (e : α ≃ᵢ β) {b : β} {a : α} (h : e.invFun b = a) :
    e.toFun a = b := by
  rw [← h]
  exact e.right b

def refl (α : Sort u) : α ≃ᵢ α where
  toFun := id
  invFun := id
  left_inv := by intro a; rfl
  right_inv := by intro a; rfl

def symm {α : Sort u} {β : Sort v} (e : α ≃ᵢ β) : β ≃ᵢ α where
  toFun := e.invFun
  invFun := e.toFun
  left_inv := e.right_inv
  right_inv := e.left_inv

def trans {α : Sort u} {β : Sort v} {γ : Sort w}
    (e₁ : α ≃ᵢ β) (e₂ : β ≃ᵢ γ) : α ≃ᵢ γ where
  toFun := e₂.toFun ∘ e₁.toFun
  invFun := e₁.invFun ∘ e₂.invFun
  left_inv := by
    intro a
    simp [Function.comp]
  right_inv := by
    intro c
    simp [Function.comp]

def prod {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
    (e₁ : α ≃ᵢ β) (e₂ : γ ≃ᵢ δ) : (α × γ) ≃ᵢ (β × δ) where
  toFun p := (e₁.toFun p.1, e₂.toFun p.2)
  invFun p := (e₁.invFun p.1, e₂.invFun p.2)
  left_inv := by
    intro p
    cases p
    simp
  right_inv := by
    intro p
    cases p
    simp

def sum {α : Type u} {β : Type v} {γ : Type w} {δ : Type x}
    (e₁ : α ≃ᵢ β) (e₂ : γ ≃ᵢ δ) : (α ⊕ γ) ≃ᵢ (β ⊕ δ) where
  toFun
    | Sum.inl a => Sum.inl (e₁.toFun a)
    | Sum.inr c => Sum.inr (e₂.toFun c)
  invFun
    | Sum.inl b => Sum.inl (e₁.invFun b)
    | Sum.inr d => Sum.inr (e₂.invFun d)
  left_inv := by
    intro x
    cases x <;> simp
  right_inv := by
    intro x
    cases x <;> simp

/--
Split a type by a decidable predicate, then encode each subtype branch.
-/
def subtypePartition {α : Type u} {β : Type v} {γ : Type w}
    (p : α → Prop) [DecidablePred p]
    (left : {a : α // p a} ≃ᵢ β)
    (right : {a : α // ¬ p a} ≃ᵢ γ) :
    α ≃ᵢ (β ⊕ γ) where
  toFun a :=
    if h : p a then
      Sum.inl (left.toFun ⟨a, h⟩)
    else
      Sum.inr (right.toFun ⟨a, h⟩)
  invFun
    | Sum.inl b => (left.invFun b).val
    | Sum.inr c => (right.invFun c).val
  left_inv := by
    intro a
    by_cases h : p a <;> simp [h]
  right_inv := by
    intro tag
    cases tag with
    | inl b =>
        have hp : p (left.invFun b).val :=
          (left.invFun b).property
        have hleft :
            (⟨(left.invFun b).val, hp⟩ : {a : α // p a}) =
              left.invFun b := by
          apply Subtype.ext
          rfl
        simp [hp, hleft]
    | inr c =>
        have hn : ¬ p (right.invFun c).val :=
          (right.invFun c).property
        have hright :
            (⟨(right.invFun c).val, hn⟩ : {a : α // ¬ p a}) =
              right.invFun c := by
          apply Subtype.ext
          rfl
        simp [hn, hright]

/-- Transport quotients across an isomorphism when both directions preserve
the chosen setoid relations. -/
def quotient {α : Type u} {β : Type v} (e : α ≃ᵢ β)
    (Sα : Setoid α) (Sβ : Setoid β)
    (map_rel : ∀ {a b : α}, Sα.r a b → Sβ.r (e.toFun a) (e.toFun b))
    (inv_rel : ∀ {a b : β}, Sβ.r a b → Sα.r (e.invFun a) (e.invFun b)) :
    Quotient Sα ≃ᵢ Quotient Sβ where
  toFun :=
    Quotient.lift (fun a => Quotient.mk Sβ (e.toFun a))
      (by
        intro a b hab
        exact Quotient.sound (map_rel hab))
  invFun :=
    Quotient.lift (fun b => Quotient.mk Sα (e.invFun b))
      (by
        intro a b hab
        exact Quotient.sound (inv_rel hab))
  left_inv := by
    intro q
    exact Quotient.inductionOn q (fun a => by
      change Quotient.mk Sα (e.invFun (e.toFun a)) = Quotient.mk Sα a
      rw [e.left_inv a])
  right_inv := by
    intro q
    exact Quotient.inductionOn q (fun b => by
      change Quotient.mk Sβ (e.toFun (e.invFun b)) = Quotient.mk Sβ b
      rw [e.right_inv b])

theorem noNatIsoOfSubsingleton {α : Type u} [Subsingleton α] :
    (α ≃ᵢ Nat) → False := by
  intro e
  have hpre : e.invFun 0 = e.invFun 1 := Subsingleton.elim _ _
  have h01 : (0 : Nat) = 1 := by
    calc
      (0 : Nat) = e.toFun (e.invFun 0) := (e.right_inv 0).symm
      _ = e.toFun (e.invFun 1) := by rw [hpre]
      _ = 1 := e.right_inv 1
  exact Nat.zero_ne_one h01

theorem subsingletonLeft {α : Type u} {β : Type v}
    (e : α ≃ᵢ β) [Subsingleton β] : Subsingleton α := by
  constructor
  intro a b
  have h : e.toFun a = e.toFun b := Subsingleton.elim _ _
  calc
    a = e.invFun (e.toFun a) := (e.left_inv a).symm
    _ = e.invFun (e.toFun b) := by rw [h]
    _ = b := e.left_inv b

end Iso

/--
Finite table for a subtype.  A table owns the explicit values plus the evidence
that the list is duplicate-free, sound for the predicate, and complete.
-/
structure FiniteSubtypeTable (α : Type u) (p : α → Prop) where
  values : List α
  nodup : values.Nodup
  sound : ∀ i : Fin values.length, p (values.get i)
  complete : ∀ a, p a → {i : Fin values.length // values.get i = a}

namespace FiniteSubtypeTable

variable {α : Type u} {p : α → Prop}

private theorem get_injective_of_nodup {α : Type u} :
    ∀ (xs : List α), xs.Nodup →
      Function.Injective fun i : Fin xs.length => xs.get i
  | [], _hnodup, i, _j, _h => by
      cases i with
      | mk val isLt => exact False.elim (Nat.not_lt_zero val isLt)
  | x :: xs, hnodup, i, j, h => by
      have hsplit : x ∉ xs ∧ xs.Nodup := by
        simpa using hnodup
      cases i with
      | mk iVal iLt =>
          cases j with
          | mk jVal jLt =>
              cases iVal with
              | zero =>
                  cases jVal with
                  | zero => rfl
                  | succ jVal =>
                      have hmem :
                          xs.get ⟨jVal, Nat.lt_of_succ_lt_succ jLt⟩ ∈ xs :=
                        List.get_mem xs ⟨jVal, Nat.lt_of_succ_lt_succ jLt⟩
                      have hx :
                          x = xs.get
                            ⟨jVal, Nat.lt_of_succ_lt_succ jLt⟩ := by
                        simpa using h
                      exact False.elim (hsplit.1 (hx ▸ hmem))
              | succ iVal =>
                  cases jVal with
                  | zero =>
                      have hmem :
                          xs.get ⟨iVal, Nat.lt_of_succ_lt_succ iLt⟩ ∈ xs :=
                        List.get_mem xs ⟨iVal, Nat.lt_of_succ_lt_succ iLt⟩
                      have hx :
                          xs.get
                            ⟨iVal, Nat.lt_of_succ_lt_succ iLt⟩ = x := by
                        simpa using h
                      exact False.elim (hsplit.1 (hx.symm ▸ hmem))
                  | succ jVal =>
                      have htail :
                          (⟨iVal, Nat.lt_of_succ_lt_succ iLt⟩ :
                              Fin xs.length) =
                            ⟨jVal, Nat.lt_of_succ_lt_succ jLt⟩ := by
                        apply get_injective_of_nodup xs hsplit.2
                        simpa using h
                      apply Fin.ext
                      have hval : iVal = jVal := congrArg Fin.val htail
                      exact congrArg Nat.succ hval

def toFin (table : FiniteSubtypeTable α p)
    (x : {a : α // p a}) : Fin table.values.length :=
  (table.complete x.val x.property).1

def ofFin (table : FiniteSubtypeTable α p)
    (i : Fin table.values.length) : {a : α // p a} :=
  ⟨table.values.get i, table.sound i⟩

theorem ofFin_toFin (table : FiniteSubtypeTable α p)
    (x : {a : α // p a}) :
    table.ofFin (table.toFin x) = x := by
  cases hcomplete : table.complete x.val x.property with
  | mk i hi =>
      apply Subtype.ext
      change table.values.get (table.toFin x) = x.val
      unfold toFin
      rw [hcomplete]
      exact hi

theorem toFin_ofFin (table : FiniteSubtypeTable α p)
    (i : Fin table.values.length) :
    table.toFin (table.ofFin i) = i := by
  cases hcomplete :
      table.complete (table.ofFin i).val (table.ofFin i).property with
  | mk j hj =>
      apply get_injective_of_nodup table.values table.nodup
      change table.values.get (table.toFin (table.ofFin i)) = table.values.get i
      unfold toFin
      rw [hcomplete]
      simpa [ofFin] using hj

/-- Derive a finite subtype equivalence from a complete duplicate-free table. -/
def iso (table : FiniteSubtypeTable α p) :
    {a : α // p a} ≃ᵢ Fin table.values.length where
  toFun := table.toFin
  invFun := table.ofFin
  left_inv := table.ofFin_toFin
  right_inv := table.toFin_ofFin

end FiniteSubtypeTable

end BijForm
