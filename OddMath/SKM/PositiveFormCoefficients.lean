import OddMath.SKM.PositiveDecoratedFamilyCoefficients
import OddMath.CoveringQuantum.UDot.PositiveWordCoefficients

/-!
# Canonical positive decorated families and the modified form

Brundan–Ellis, arXiv:1701.04133v2, Theorem 10.3, Claim 1: the finite
integer-degree fibers of the existing canonical decorated family compute the
Laurent coefficients of the existing positive modified form. The witnesses for
top placement and ordinary realization are taken from the canonical-family
coefficient theorem, without changing their quantifier order or identifying
independently chosen families at different signs.

This result retains representative coverage and uniqueness, finite colours,
and bar consistency. It does not identify arbitrary geometric selectors or
address unequal-length words and the other claims of Theorem 10.3.
-/

noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {I X : Type*} [AddCommGroup X] [DecidableEq I] [DecidableEq X] [Finite I]
variable (Q : CoveringQuantum.RootDatum I X) (hQ : Q.toSuperCartanDatum.BarConsistent)
variable (μ : X) (σ : ℚ) (hσ : σ ^ 2 = 1) {n : ℕ} (a b : Fin n → I)
local notation "A" => (List.ofFn fun r => (true, a r))
local notation "B" => (List.ofFn fun r => (true, b r))

/-- The canonical family's finite parity-weighted degree fibers equal the Laurent
coefficients of the constructed form, with its finite/bar-consistent restrictions. -/
theorem positive_decorated_family_form_coeff
    (M : Set (List (TMove (Letter I))))
    (hM : ∀ R ∈ M, IsMatching₂ A B R ∧ StrictReduced₂ A R)
    (hrep : ∀ R', IsMatching₂ A B R' → StrictReduced₂ A R' →
      ∃ R ∈ M, Iso (pairing₂ A R) (pairing₂ A R'))
    (huniq : ∀ R ∈ M, ∀ S ∈ M,
      Iso (pairing₂ A R) (pairing₂ A S) → R = S) :
  ∃ p : ∀ R : {R // R ∈ M}, MatchingStrand A R.val ≃ Fin n,
    (∀ R (j : MatchingStrand A R.val),
      OnStrand₂ A R.val j.val (R.val.length, (p R j).val)) ∧
    (let family := decoratedFamily₂ A M
       (fun R c => topDotMoves A R (topPositionExtension M p R) (fun j => c j))
     let G := {D // D ∈ family}
     ∃ (L : G → List (LayerData I)) (hL : ∀ D, SChain A (L D) B),
       (∀ D, (L D).map ofL = D.val) ∧
       ∀ z : ℤ, ∃ hf : Set.Finite {D : G |
         Diagram.degree (gdeg Q.toSKM Q.skmSymmetrizer)
           (mkD Q.toSKM μ (L D) (hL D)) = z},
         (∑ D ∈ hf.toFinset, σ ^ (xpar Q.toSKM μ D.val).val) =
           (CoveringQuantum.signLaurent σ hσ
             (CoveringQuantum.UDot.GenericTensor.sesquilinearForm Q hQ
               (CoveringQuantum.UDot.positiveHalf Q CoveringQuantum.Coefficients.q
                 CoveringQuantum.Coefficients.pi μ
                 (Q.toSerreF CoveringQuantum.Coefficients.q CoveringQuantum.Coefficients.pi
                   (CoveringQuantum.PreF.monomial CoveringQuantum.Coefficients.Ring
                     (List.ofFn a).reverse)))
               (CoveringQuantum.UDot.positiveHalf Q CoveringQuantum.Coefficients.q
                 CoveringQuantum.Coefficients.pi μ
                 (Q.toSerreF CoveringQuantum.Coefficients.q CoveringQuantum.Coefficients.pi
                   (CoveringQuantum.PreF.monomial CoveringQuantum.Coefficients.Ring
                     (List.ofFn b).reverse))))).coeff z) := by
  obtain ⟨p, hp, L, hL, hmap, hc⟩ := positive_decorated_family_coeff
    Q μ σ hσ a b M hM hrep huniq
  refine ⟨p, hp, L, hL, hmap, ?_⟩
  intro z
  obtain ⟨hf, hfcoeff⟩ := hc z
  refine ⟨hf, hfcoeff.trans ?_⟩
  simpa only using (CoveringQuantum.UDot.GenericTensor.sesquilinearForm_positive_words_coeff
    Q hQ σ hσ μ n a b z).symm

end OddMath.SKM
