import BijForm.Coding

namespace BijForm

universe u v

/--
Finite dependent product over a concrete list.  This is the product-shaped
counterpart to a `Fin xs.length` indexed child function.
-/
def ListPiTuple {α : Type u} (F : α → Type v) : List α → Type (max u v)
  | [] => PUnit
  | x :: xs => F x × ListPiTuple F xs

namespace ListPiTuple

variable {α : Type u} {F : α → Type v}

def ofPi :
    {xs : List α} →
      ((q : Fin xs.length) → F (xs.get q)) →
      ListPiTuple F xs
  | [], _child => PUnit.unit
  | _x :: xs, child =>
      (child ⟨0, by simp⟩,
        ofPi (xs := xs) (fun q => child q.succ))

def toPi :
    {xs : List α} →
      ListPiTuple F xs →
        (q : Fin xs.length) → F (xs.get q)
  | [], _tuple, q => fin_zero_elim q
  | _x :: _xs, tuple, q => by
      cases q using Fin.cases with
      | zero =>
          exact tuple.1
      | succ q =>
          exact toPi tuple.2 q

@[simp]
theorem ofPi_cons {x : α} {xs : List α}
    (child : (q : Fin (x :: xs).length) → F ((x :: xs).get q)) :
    ofPi child =
      (child ⟨0, by simp⟩,
        ofPi (xs := xs) (fun q => child q.succ)) :=
  rfl

@[simp]
theorem ofPi_cons_fst {x : α} {xs : List α}
    (child : (q : Fin (x :: xs).length) → F ((x :: xs).get q)) :
    (ofPi child).1 = child ⟨0, by simp⟩ :=
  rfl

@[simp]
theorem ofPi_cons_snd {x : α} {xs : List α}
    (child : (q : Fin (x :: xs).length) → F ((x :: xs).get q)) :
    (ofPi child).2 = ofPi (xs := xs) (fun q => child q.succ) :=
  rfl

@[simp]
theorem toPi_cons_zero {x : α} {xs : List α} (tuple : ListPiTuple F (x :: xs)) :
    toPi tuple ⟨0, by simp⟩ = tuple.1 :=
  rfl

@[simp]
theorem toPi_cons_succ {x : α} {xs : List α} (tuple : ListPiTuple F (x :: xs))
    (q : Fin xs.length) :
    toPi tuple q.succ = toPi tuple.2 q :=
  rfl

theorem toPi_ofPi :
    {xs : List α} →
      (child : (q : Fin xs.length) → F (xs.get q)) →
      toPi (ofPi child) = child
  | [], child => by
      funext q
      exact fin_zero_elim q
  | _x :: xs, child => by
      funext q
      cases q using Fin.cases with
      | zero => rfl
      | succ q =>
          exact congrFun
            (toPi_ofPi (xs := xs) (fun q => child q.succ)) q

theorem ofPi_toPi :
    {xs : List α} →
      (tuple : ListPiTuple F xs) →
      ofPi (toPi tuple) = tuple
  | [], tuple => by
      cases tuple
      rfl
  | _x :: xs, tuple => by
      cases tuple with
      | mk head tail =>
          change (head, ofPi (toPi tail)) = (head, tail)
          rw [ofPi_toPi (xs := xs) tail]

def iso (xs : List α) :
    ((q : Fin xs.length) → F (xs.get q)) ≃ᵢ ListPiTuple F xs where
  toFun := ofPi
  invFun := toPi
  left_inv := toPi_ofPi
  right_inv := ofPi_toPi

end ListPiTuple

end BijForm
