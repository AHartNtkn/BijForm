import BijForm.InitialAlgebra
import BijForm.CodeAlgebra

namespace BijForm

/--
Close generated child-rank descent goals after the local presentation and
carrier maps are supplied as simplification definitions.
-/
macro "finish_rank_descent" : tactic =>
  `(tactic|
    rintro idx z q <;>
    cases z <;>
      simp_all! [BijForm.DepPoly.OutputIndexInversion.canonical] <;>
      try cases q <;>
      simp_all! [BijForm.DepPoly.OutputIndexInversion.canonical] <;>
      omega)

macro "finish_rank_descent " "[" defs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic|
    first
    | (rintro idx z q <;>
       cases idx <;>
         dsimp [$defs,*, BijForm.DepPoly.OutputIndexInversion.canonical] at z q ⊢ <;>
         (first | cases q | skip) <;>
         (first | cases z | skip) <;>
         dsimp [$defs,*, BijForm.DepPoly.OutputIndexInversion.canonical] at q ⊢ <;>
         (first | cases q | skip) <;>
         simp_all! [$defs,*, BijForm.DepPoly.OutputIndexInversion.canonical] <;>
         first
         | (apply Nat.add_lt_add_right; simp_all!)
         | omega
       done)
    | (rintro idx layer q <;>
       rcases layer with ⟨code, child⟩
       rcases code with ⟨ctor, param, out_eq⟩
       cases ctor <;>
         (first | cases out_eq | cases out_eq.symm | skip) <;>
         dsimp [$defs,*, BijForm.DepPoly.OutputIndexInversion.canonical] at q <;>
         (first | cases q | skip) <;>
         simp_all! [$defs,*, BijForm.DepPoly.OutputIndexInversion.canonical] <;>
         first
         | (apply Nat.add_lt_add_right; simp_all!)
         | omega
       done))

end BijForm
