import BijForm.InitialAlgebra
import BijForm.CodeAlgebra
import BijForm.TypedBinding

namespace BijForm

/--
Close generated rank-descent goals after the local presentation and carrier
maps are supplied as simplification definitions.
-/
macro "rank_descent" : tactic =>
  `(tactic|
    rintro idx z q <;>
    cases z <;>
      simp_all! [BijForm.DepPoly.OutputIndexInversion.canonical] <;>
      try cases q <;>
      simp_all! [BijForm.DepPoly.OutputIndexInversion.canonical] <;>
      omega)

macro "rank_descent " "[" defs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
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

macro "typed_binding_rank_descent " "[" defs:Lean.Parser.Tactic.simpLemma,* "]"
    " using " "[" h0:term "," h1:term "," h2:term "," h3:term "]" : tactic =>
  `(tactic|
    (apply BijForm.TypedBinding.LayerShapeRankProof.of_op <;>
      rintro ctx ctor child q <;>
      cases ctor <;>
        first
        | (cases q <;> omega)
        | (cases q using Fin.cases with
            | zero =>
                first
                | (simpa [$defs,*] using $h0 _ _)
                | (simpa [$defs,*] using $h1 _ _)
                | (simpa [$defs,*] using $h2 _ _)
                | (simpa [$defs,*] using $h3 _ _)
            | succ q =>
                first
                | (exact fin_zero_elim q)
                | (cases q using Fin.cases with
                    | zero =>
                        first
                        | (simpa [$defs,*] using $h0 _ _)
                        | (simpa [$defs,*] using $h1 _ _)
                        | (simpa [$defs,*] using $h2 _ _)
                        | (simpa [$defs,*] using $h3 _ _)
                    | succ q => exact fin_zero_elim q))))

macro "quotient_rank_descent" " using " hfact:term : tactic =>
  `(tactic|
    (rintro idx z ctor param out_eq child hdecode q;
     exact $hfact hdecode q))

end BijForm
