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

end Iso

end BijForm
