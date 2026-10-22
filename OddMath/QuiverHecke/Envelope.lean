/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Grading
import StringDiagrams.Super.MonoidalTwo

/-!
# The envelope `Ḣ_{q,π}` of the quiver Hecke supercategory and its `K₀`

Brundan–Ellis, arXiv:1701.04133v2, §11, before Lemma 11.1: `H_{q,π}` is the `(Q, Π)`-envelope of
the monoidal supercategory `H`, viewed as a 2-supercategory with one object; `Ḣ_{q,π}` is the
idempotent completion of the additive envelope of its underlying category; and (11.2)
identifies `K₀(Ḣ_{q,π})` with `⨁_{n ≥ 0} K₀(H_n)`, an `ℒ`-algebra with the induction product.

Here `HGr` is `H` with its grading (`OddMath.QuiverHecke.Grading`), `HDot := GSKAR k
(MonoidalTwo HGr)` (string-diagrams-lean's graded super Karoubi envelope of a one-object
2-supercategory), and its 1-morphism category `HCat = GSKar k HGr` is the graded super Karoubi
envelope of `H` (`hCat_eq`, definitionally). Its split Grothendieck group, the single summand of
`K₀Ring HDot`, is the `K₀` of (11.2), with product from the tensor product.

We take the left side of (11.2) as the definition. The equivalence of a graded super Karoubi
envelope with finitely generated graded projective (right) supermodules, which BE2 uses to
identify the two sides, is `OddMath.FiniteHomMatrix.gsKarEquivEssImage`
(`OddMath.QuiverHecke.ProjectiveModules`).
-/

noncomputable section

namespace OddMath.QuiverHecke

open CategoryTheory StringDiagrams

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k) (sy : SKM.Symmetrizer D)
  (hc : Sc.Homogeneous)

/-- `H` with its integer grading (a type synonym of `H D Sc` carrying the graded instances). -/
@[nolint unusedArguments]
def HGr (_sy : SKM.Symmetrizer D) (_hc : Sc.Homogeneous) : Type _ := H D Sc

namespace HGr

instance : Category (HGr D Sc sy hc) := inferInstanceAs (Category (H D Sc))

instance : Preadditive (HGr D Sc sy hc) := inferInstanceAs (Preadditive (H D Sc))

instance : Linear k (HGr D Sc sy hc) := inferInstanceAs (Linear k (H D Sc))

instance : Supercategory k (HGr D Sc sy hc) := inferInstanceAs (Supercategory k (H D Sc))

instance : GradedSupercategory k (HGr D Sc sy hc) := gradedSupercategory D sy Sc hc

instance : MonoidalCategoryStruct (HGr D Sc sy hc) :=
  inferInstanceAs (MonoidalCategoryStruct (H D Sc))

instance : MonoidalSupercategory k (HGr D Sc sy hc) :=
  inferInstanceAs (MonoidalSupercategory k (H D Sc))

/-- **BE2 §11**: `H` is a graded monoidal supercategory. -/
instance : GradedMonoidalSupercategory k (HGr D Sc sy hc) :=
  gradedMonoidalSupercategory D sy Sc hc

end HGr

/-- The object of `H` attached to a word. -/
abbrev hObj (t : List I) : HGr D Sc sy hc := (pres D Sc).obj (ob D t)


/-- **BE2 §11.** `Ḣ_{q,π}`: the idempotent completion of the additive envelope of the
underlying category of the `(Q, Π)`-envelope of `H`, as a 2-category with one object. -/
abbrev HDot := GSKAR k (MonoidalTwo (HGr D Sc sy hc))

/-- The unique object of `Ḣ_{q,π}`. -/
abbrev HDot.star : HDot D Sc sy hc := GSKAR.mkObj k _ (MonoidalTwo.star _)

/-- The 1-morphisms of `Ḣ_{q,π}`: the graded super Karoubi envelope of `H`. -/
abbrev HCat := HDot.star D Sc sy hc ⟶ HDot.star D Sc sy hc

theorem hCat_eq : HCat D Sc sy hc = GSKar k (HGr D Sc sy hc) := rfl

example : QPiTwoCategory k (HDot D Sc sy hc) := inferInstance

example : IsIdempotentComplete (HCat D Sc sy hc) := inferInstance

/-- **(11.2).** `K₀(Ḣ_{q,π})`, a ring with the product from the tensor product. -/
abbrev KH := K₀Ring (HDot D Sc sy hc)

example : NonUnitalRing (KH D Sc sy hc) := inferInstance

end OddMath.QuiverHecke
