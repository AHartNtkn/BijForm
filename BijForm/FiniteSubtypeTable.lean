import BijForm.Coding

namespace BijForm

universe u

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
      exact fin_zero_elim i
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
                      have hval : iVal = jVal := congrArg Fin.val htail
                      exact fin_eq_of_val_eq (congrArg Nat.succ hval)

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
