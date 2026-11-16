import OddMath.SKM.BubbleCoefficientParity
import OddMath.SKM.MatchingTargetExpansion

/-! Exact source/target coefficient-placement comparison. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k}

/-- Apply the exact full-SYM parity involution separately at each label. -/
def labelParityTwist {A : Type*} (q : A → ZMod 2) :
    (A →₀ SYM D k) →ₗ[k] (A →₀ SYM D k) :=
  Finsupp.lsum k (fun i => (Finsupp.lsingle i).comp (SYM.parityTwist D k (q i)))

@[simp] theorem labelParityTwist_single {A : Type*} (q : A → ZMod 2) (i : A) (p : SYM D k) :
    labelParityTwist (D := D) (k := k) q (Finsupp.single i p) =
      Finsupp.single i (SYM.parityTwist D k (q i) p) := Finsupp.lsum_single k _ i p

@[simp] theorem labelParityTwist_involutive {A : Type*} (q : A → ZMod 2) (f : A →₀ SYM D k) :
    labelParityTwist (D := D) (k := k) q (labelParityTwist q f) = f := by
  classical
  induction f using Finsupp.induction with
  | zero => simp only [map_zero]
  | @single_add i p f _ _ ih =>
    simp only [map_add, labelParityTwist_single, SYM.parityTwist_involutive, ih]

/-- A labelwise involutive coefficient change preserves injectivity. -/
theorem injective_iff_labelParityTwist {A M : Type*} [AddCommGroup M] [Module k M]
    (q : A → ZMod 2) (source target : (A →₀ SYM D k) →ₗ[k] M)
    (h : ∀ i p, source (Finsupp.single i (SYM.parityTwist D k (q i) p)) =
      target (Finsupp.single i p)) :
    Function.Injective source ↔ Function.Injective target := by
  have he : ∀ f, source (labelParityTwist q f) = target f := by
    intro f
    classical
    induction f using Finsupp.induction with
    | zero => simp only [map_zero]
    | @single_add i p f _ _ ih => simp only [map_add, labelParityTwist_single, h, ih]
  constructor
  · intro hi f g hfg
    have H := hi ((he f).trans (hfg.trans (he g).symm))
    have H' := congrArg (labelParityTwist (D := D) (k := k) q) H
    simpa only [labelParityTwist_involutive] using H'
  · intro hi f g hfg
    have ht (f) : target (labelParityTwist q f) = source f := by
      rw [← he, labelParityTwist_involutive]
    have H := hi ((ht f).trans (hfg.trans (ht g).symm))
    have H' := congrArg (labelParityTwist (D := D) (k := k) q) H
    simpa only [labelParityTwist_involutive] using H'

/-- Source and target placement give equivalent independence for any family
of actual homogeneous morphisms, with arbitrary inhomogeneous coefficients. -/
theorem source_target_expansion_injective_iff (cs : CScalars Sc) (μ : X)
    {A : Type*} {s t : List (Letter I)}
    (f : A → ((pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)))
    (q : A → ZMod 2) (hf : ∀ i, f i ∈ homPar D Sc μ s t (q i))
    (source target : (A →₀ SYM D k) →ₗ[k]
      ((pres D Sc).obj (ob D μ s) ⟶ (pres D Sc).obj (ob D μ t)))
    (hsource : ∀ i p, source (Finsupp.single i p) = bubAt D Sc μ s (betaSYM cs μ p) ≫ f i)
    (htarget : ∀ i p, target (Finsupp.single i p) = f i ≫ bubAt D Sc μ t (betaSYM cs μ p)) :
    Function.Injective source ↔ Function.Injective target := by
  apply injective_iff_labelParityTwist q source target
  intro i p
  rw [hsource, htarget]
  exact source_target_twist cs μ (hf i) p

namespace MatchingBasisChoice
variable (cs : CScalars Sc) (μ : X) {a b : List (Letter I)}

theorem expansion_injective_iff_target (F : MatchingBasisChoice a b) :
    Function.Injective (F.expansion cs μ) ↔ Function.Injective (F.targetExpansion cs μ) := by
  apply source_target_expansion_injective_iff cs μ
    (fun t => xev cs μ a b (F.layers t)) (fun t => xpar D μ (F.layers t))
    (fun t => xev_mem_homPar cs μ a b (F.layers t))
    (F.expansion cs μ) (F.targetExpansion cs μ)
  · exact F.expansion_single cs μ
  · exact F.targetExpansion_single cs μ

end MatchingBasisChoice
end OddMath.SKM
