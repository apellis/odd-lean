/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.Grading
import StringDiagrams.Super.PresentedGraded
import StringDiagrams.Super.KarBicategory

/-!
# The graded 2-supercategory `𝔘(𝔤)` and its `(Q, Π)`-envelope

J. Brundan, A. P. Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §1, paragraph
"Gradings" and Definition 1.6 (TeX label `ernie`).

Under a symmetrization `dᵢ` and the homogeneity condition (1.31), the relations of `𝔘(𝔤)` are
homogeneous for the degrees `gdeg` (`OddMath.SKM.Grading`), so `𝔘(𝔤)` is a graded
2-supercategory (`UGr`, with the instances `UGr.instGradedTwoSupercategory` etc.; from
string-diagrams-lean's `Presentation.gradedTwoSupercategory`). Then:

* `Uqπ := 𝔘_{q,π}(𝔤)`, the `(Q, Π)`-envelope of Definition 1.6 (string-diagrams-lean's
  `QPiTwoEnvelope`, Brundan–Ellis, *Monoidal supercategories*, Definition 6.10), a graded
  `(Q, Π)`-2-supercategory;
* `UUnderline := 𝔘̲_{q,π}(𝔤)`, its underlying 2-category (same objects and 1-morphisms, even
  2-morphisms of degree zero; `GUnderlying2`), a `(Q, Π)`-2-category;
* `UDot := 𝔘̇_{q,π}(𝔤)`, the idempotent completion of the additive envelope of
  `𝔘̲_{q,π}(𝔤)` (`GSKAR`), an additive, idempotent complete `(Q, Π)`-2-category.

The paper also assumes that `k` is a field here; none of these constructions needs it.
-/

noncomputable section

namespace OddMath.SKM

open CategoryTheory StringDiagrams

universe u v w

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X) {k : Type w} [CommRing k]
  (Sc : Scalars D k) (sy : Symmetrizer D) (hc : Sc.Homogeneous)

/-- `𝔘(𝔤)` with its grading (a type synonym of `U D Sc` carrying the graded instances). -/
@[nolint unusedArguments]
def UGr (_sy : Symmetrizer D) (_hc : Sc.Homogeneous) : Type _ := U D Sc

namespace UGr

instance : BicategoryStruct (UGr D Sc sy hc) := inferInstanceAs (BicategoryStruct (U D Sc))

instance (a b : UGr D Sc sy hc) : Preadditive (a ⟶ b) :=
  inferInstanceAs (Preadditive ((show U D Sc from a) ⟶ (show U D Sc from b)))

instance (a b : UGr D Sc sy hc) : Linear k (a ⟶ b) :=
  inferInstanceAs (Linear k ((show U D Sc from a) ⟶ (show U D Sc from b)))

instance instSupercategory (a b : UGr D Sc sy hc) : Supercategory k (a ⟶ b) :=
  homSupercategory D Sc a b

instance instGradedSupercategory (a b : UGr D Sc sy hc) : GradedSupercategory k (a ⟶ b) :=
  Presentation.Bicat.gradedSupercategory (gdeg D sy) (isParityHomogeneous D Sc)
    (isHomogeneous_gdeg D sy Sc hc) a b

instance instTwoSupercategory : TwoSupercategory k (UGr D Sc sy hc) :=
  twoSupercategory D Sc

/-- **`𝔘(𝔤)` is a graded 2-supercategory** (Brundan–Ellis, §1, "Gradings"), under (1.31). -/
instance instGradedTwoSupercategory : GradedTwoSupercategory k (UGr D Sc sy hc) :=
  Presentation.gradedTwoSupercategory (gdeg D sy) (isParityHomogeneous D Sc)
    (isHomogeneous_gdeg D sy Sc hc)

end UGr

/-- **Definition 1.6 applied to `𝔘(𝔤)`**: the `(Q, Π)`-envelope `𝔘_{q,π}(𝔤)`. -/
abbrev Uqπ : Type _ := QPiTwoEnvelope k (UGr D Sc sy hc)

/-- `𝔘_{q,π}(𝔤)` is a graded `(Q, Π)`-2-supercategory (Brundan–Ellis, Definition 1.6 and
*Monoidal supercategories*, Definition 6.5). -/
example : QPiTwoSupercategory k (Uqπ D Sc sy hc) := inferInstance

/-- The underlying 2-category `𝔘̲_{q,π}(𝔤)`: even 2-morphisms of degree zero. -/
abbrev UUnderline : Type _ := GUnderlying2 k (Uqπ D Sc sy hc)

/-- `𝔘̲_{q,π}(𝔤)` is a `(Q, Π)`-2-category (*Monoidal supercategories*, Definition 6.14). -/
example : QPiTwoCategory k (UUnderline D Sc sy hc) := inferInstance

/-- `𝔘̇_{q,π}(𝔤)`: the idempotent completion of the additive envelope of `𝔘̲_{q,π}(𝔤)`. -/
abbrev UDot : Type _ := GSKAR k (UGr D Sc sy hc)

/-- `𝔘̇_{q,π}(𝔤)` is an additive, idempotent complete `(Q, Π)`-2-category. -/
example : QPiTwoCategory k (UDot D Sc sy hc) := inferInstance

example (a b : UDot D Sc sy hc) : IsIdempotentComplete (a ⟶ b) := inferInstance

end OddMath.SKM
