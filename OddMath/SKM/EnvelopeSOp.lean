import StringDiagrams.Super.TwoSOpGraded
import StringDiagrams.Super.GradedTwoEnvelopeUniversal

/-!
# The general extension into a super-opposite

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Lemma 9.1.
Unlike the Chevalley specialization, the input may already take values in the
shifted target. This is the extension needed in the proof of Proposition 9.4.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams StringDiagrams.Supercategory
  StringDiagrams.GradedSupercategory StringDiagrams.BicategoryStruct

universe r u v w u' v' w'

section Opposite
variable {R : Type r} [CommRing R] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear R C] [Supercategory R C]

/-- An odd isomorphism reverses with a minus sign on its inverse in the super-opposite. -/
def oddSOpIso {X Y : C} (e : X ≅ Y) (he : e.hom ∈ parity (R := R) X Y 1) :
    (⟨X⟩ : SOp R C) ≅ ⟨Y⟩ where
  hom := SOp.sop e.inv
  inv := -SOp.sop e.hom
  hom_inv_id := by
    apply SOp.hom_ext
    rw [Preadditive.comp_neg, SOp.unsop_neg,
      SOp.comp_of_mem (inv_mem e he) he]
    simp
  inv_hom_id := by
    apply SOp.hom_ext
    rw [Preadditive.neg_comp, SOp.unsop_neg,
      SOp.comp_of_mem he (inv_mem e he)]
    simp
end Opposite

section Structure
variable {R : Type r} [CommRing R] {B : Type u} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
  [∀ a b : B, GradedSupercategory R (a ⟶ b)] [GradedTwoSupercategory R B]
  [QPiTwoSupercategory R B]

/-- The structure used in Lemma 9.1: exchange the two integer shift objects,
reverse the three structure maps, and correct the inverse of the odd one. -/
instance qpiTwoSOp : QPiTwoSupercategory R (TwoSOp R B) where
  pi a := ⟨PiTwoSupercategory.pi (R := R) a.unop⟩
  ζ a := oddSOpIso (PiTwoSupercategory.ζ (R := R) a.unop)
    (PiTwoSupercategory.ζ_hom_mem a.unop)
  ζ_hom_mem a := PiTwoSupercategory.ζ_inv_mem a.unop
  ζ_hom_mem_degree a := QPiTwoSupercategory.ζ_inv_mem_degree' a.unop
  q a := ⟨QPiTwoSupercategory.qinv (R := R) a.unop⟩
  qinv a := ⟨QPiTwoSupercategory.q (R := R) a.unop⟩
  σ a := SOp.evenIso (QPiTwoSupercategory.σbar (R := R) a.unop)
    (QPiTwoSupercategory.σbar_hom_mem a.unop)
  σbar a := SOp.evenIso (QPiTwoSupercategory.σ (R := R) a.unop)
    (QPiTwoSupercategory.σ_hom_mem a.unop)
  σ_hom_mem a := QPiTwoSupercategory.σbar_inv_mem a.unop
  σ_hom_mem_degree a := QPiTwoSupercategory.σbar_inv_mem_degree a.unop
  σbar_hom_mem a := QPiTwoSupercategory.σ_inv_mem a.unop
  σbar_hom_mem_degree a := QPiTwoSupercategory.σ_inv_mem_degree a.unop
end Structure

section Extension
variable {R : Type r} [CommRing R]
  {A : Type u} [BicategoryStruct.{w, v} A]
  [∀ a b : A, Preadditive (a ⟶ b)] [∀ a b : A, Linear R (a ⟶ b)]
  [∀ a b : A, Supercategory R (a ⟶ b)] [TwoSupercategory R A]
  [∀ a b : A, GradedSupercategory R (a ⟶ b)]
  {B : Type u'} [BicategoryStruct.{w', v'} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear R (a ⟶ b)]
  [∀ a b : B, Supercategory R (a ⟶ b)] [TwoSupercategory R B]
  [∀ a b : B, GradedSupercategory R (a ⟶ b)] [GradedTwoSupercategory R B]

/-- **Lemma 9.1.** Extend an arbitrary map into the already-shifted super-opposite.
No factorization through the unshifted super-opposite is assumed. -/
def extendEnvelopeSOp (F : TwoSuperfunctor R A (TwoSOp R (QPiTwoEnvelope R B))) :
    TwoSuperfunctor R (QPiTwoEnvelope R A) (TwoSOp R (QPiTwoEnvelope R B)) :=
  QPiTwoEnvelope.extendQPi F

omit [∀ a b : A, GradedSupercategory R (a ⟶ b)] in
/-- The extension agrees with the original map, including its comparison data. -/
theorem twoJ_comp_extendEnvelopeSOp
    (F : TwoSuperfunctor R A (TwoSOp R (QPiTwoEnvelope R B))) :
    (QPiTwoEnvelope.twoJ R A).comp (extendEnvelopeSOp F) = F :=
  QPiTwoEnvelope.twoJ_comp_extendQPi F

/-- The general extension in Lemma 9.1 preserves the integer grading. -/
theorem extendEnvelopeSOp_isGraded
    (F : TwoSuperfunctor R A (TwoSOp R (QPiTwoEnvelope R B))) (hF : F.IsGraded) :
    (extendEnvelopeSOp F).IsGraded :=
  QPiTwoEnvelope.extendQPi_isGraded F hF

/-- **Lemma 9.1**, with its grading and restriction conclusions together. -/
theorem exists_graded_envelopeSOp_extension
    (F : TwoSuperfunctor R A (TwoSOp R (QPiTwoEnvelope R B))) (hF : F.IsGraded) :
    ∃ G : TwoSuperfunctor R (QPiTwoEnvelope R A) (TwoSOp R (QPiTwoEnvelope R B)),
      G.IsGraded ∧ (QPiTwoEnvelope.twoJ R A).comp G = F :=
  ⟨extendEnvelopeSOp F, extendEnvelopeSOp_isGraded F hF,
    twoJ_comp_extendEnvelopeSOp F⟩
end Extension
end OddMath.SKM
