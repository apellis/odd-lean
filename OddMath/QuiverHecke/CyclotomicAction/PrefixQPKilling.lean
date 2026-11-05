/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.PrefixQPInduction

/-!
# The relation-killing step (K) with a right context

`DeformedGlobalQP.md`, §2: after the strand of colour `i` has crossed the prefix
`μ ++ [i]` and the last old `i` has been brought back to the front, the first-position
relation `f_i(x₁)` lies in the old cyclotomic ideal. This file proves the version with an
arbitrary right context `σ`, which the all-prefix induction needs:

* `killE_whiskerLeft_comp`: precomposition by `1_i ⊗ g` kills when `g` lies in the old
  cyclotomic kernel;
* `killE_relation_context`: the identity (K) on the word `i :: (μ ++ [i] ++ σ)`.

Supporting whiskering identities: `twist_whiskerRight_obj` (the parity twist commutes with
right whiskering), `whiskerLeft_whiskerRight_cons`, `whiskerRight_whiskerRight_word`
(associativity of whiskering by words) and `whiskerLeft_dotE_cons`.
-/

noncomputable section
open CategoryTheory StringDiagrams Categorification MulOpposite MonoidalCategory
namespace OddMath.QuiverHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  [CommRing k] (Sc : SKM.Scalars D k)

section Whisker

/-- Right whiskering of a left whiskering by a letter, on words. -/
theorem whiskerLeft_whiskerRight_cons (i : I) {t t' : List I}
    (g : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')) (σ : List I) :
    ((pres D Sc).obj (ob D [i]) ◁ g) ▷ (pres D Sc).obj (ob D σ) =
      ((pres D Sc).obj (ob D [i]) ◁ (g ▷ (pres D Sc).obj (ob D σ)) :
        (pres D Sc).obj (ob D (i :: (t ++ σ))) ⟶ (pres D Sc).obj (ob D (i :: (t' ++ σ)))) := by
  have h := MonoidalSupercategory.associator_naturality (R := k)
    (𝟙 ((pres D Sc).obj (ob D [i]))) g (𝟙 ((pres D Sc).obj (ob D σ)))
  simp only [MonoidalSupercategory.tensorHom_def (R := k),
    MonoidalSupercategory.id_whiskerRight (R := k),
    MonoidalSupercategory.whiskerLeft_id (R := k), Category.id_comp, Category.comp_id,
    Presentation.associator_eq, eqToIso.hom] at h
  simpa using h

/-- Right whiskering by a word, as a homomorphism of `k`-algebras. -/
def whiskerWordAlgHom (w s : List I) :
    End ((pres D Sc).obj (ob D w)) →ₐ[k] End ((pres D Sc).obj (ob D (w ++ s))) where
  __ := whiskerWordRingHom D Sc w s
  commutes' c := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    change (c • 𝟙 _) ▷ _ = c • 𝟙 _
    rw [MonoidalSupercategory.smul_whiskerRight (R := k),
      MonoidalSupercategory.id_whiskerRight (R := k)]
    rfl

end Whisker

variable [Fintype I] (i : I) (β : Multiset I) (a : I → _root_.Polynomial k)
  (ha : CyclotomicPolynomialParity D a) (n : ℕ)

section Killing

end Killing

end OddMath.QuiverHecke
