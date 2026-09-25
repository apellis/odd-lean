import OddMath.Frontier.EKSchurOrthonormal
import OddMath.Frontier.EKKostkaValues
import OddMath.Frontier.EKProp310
import OddMath.Frontier.EKOddRSKII

/-!
# EK closure composition: proved bridges between the existing modules

The four existing modules consumed by `EKClosureComposition` were written independently and
each carries its own copy of the source objects.  Every textual mismatch is bridged here by a
PROVED lemma; nothing is restated or redefined.

* `schur` : `EKSchurOrthonormal.schur`, `EKProp310.schur`, `EKOddRSKII.schur` are all
  `KostkaModuleInversion.recover d (degreeHBasis d)` (the unique solution of EK (3.6)); proved
  equal (`schur_prop310_eq`, `schur_oddRSKII_eq`).
* `C(λᵀ,2)` : the three `transposeChoose` copies (`EKSchurOrthonormalControls`,
  `EKProp310Controls`, `EKOddRSKIIControls`) are the same function (`transposeChoose_*_eq`);
  likewise the printed-sign statistic `evenParts` (`evenParts_oddRSKII_eq`).
* the (3.9) sign : `EKKostkaValues.Mh_eq_sum_kostka` uses `TableauStripSigns.directNorth λ`
  while `EKSchurOrthonormal.Identity39` uses `(-1)^{λ₂+λ₄+⋯} = (-1)^{evenParts λ}`.
  `sign_directNorth_eq_evenParts` proves the signs agree for EVERY Young diagram, via
  `directNorth = Σ_j C(λᵀ_j,2)` (`EKKostkaValues.directNorth_eq_choose`) and the existing
  `EKSchurOrthonormal.sign_bridge`.  This is an equality of SIGNS, not of the statistics:
  `sign_bridge_is_parity_only` exhibits λ = (1,1,1) with statistics 3 ≠ 1.
* index/carrier : all modules index by `DegreeShapes.DegreeShape d`, use
  `TableauDominance.signedKostka` (EK (3.7)), `EKDualBases.Mh` (EK M′ = (h,h)), the pairing
  `EKRadicalQuotient.quotientPairing` on `Q`, and the Fintype instance
  `DegreeShapes.degreeFintype`; no further bridge is needed (checked by elaboration of the
  composed statements in `EKClosureComposition`).
-/
noncomputable section
open scoped BigOperators
namespace OddMath.Frontier.EKClosureCompositionControls
open EKRadicalQuotient EKIntegralBases DegreeShapes EKDualBases TableauDominance

/-! ## Identity of the independently written copies -/

theorem schur_prop310_eq (d : ℕ) : EKProp310.schur d = EKSchurOrthonormal.schur d := rfl

theorem schur_oddRSKII_eq (d : ℕ) : EKOddRSKII.schur d = EKSchurOrthonormal.schur d := rfl

theorem transposeChoose_prop310_eq (lam : YoungDiagram) :
    EKProp310Controls.transposeChoose lam = EKSchurOrthonormalControls.transposeChoose lam := rfl

theorem transposeChoose_oddRSKII_eq (lam : YoungDiagram) :
    EKOddRSKIIControls.transposeChoose lam = EKSchurOrthonormalControls.transposeChoose lam := rfl

theorem evenParts_oddRSKII_eq (L : List ℕ) :
    EKOddRSKIIControls.evenParts L = EKSchurOrthonormalControls.evenParts L := rfl

/-! ## The (3.9) sign: `directNorth` form vs printed `λ₂+λ₄+⋯` form, every diagram -/

/-- `(-1)^{directNorth λ} = (-1)^{C(λᵀ,2)}` for every Young diagram. -/
theorem sign_directNorth_eq_transposeChoose (lam : YoungDiagram) :
    (-1 : ℤ) ^ TableauStripSigns.directNorth lam =
      (-1 : ℤ) ^ EKSchurOrthonormalControls.transposeChoose lam := by
  rw [EKKostkaValues.directNorth_eq_choose, EKSchurOrthonormal.transposeChoose_eq]

/-- `(-1)^{directNorth λ} = (-1)^{λ₂+λ₄+⋯}` for every Young diagram. -/
theorem sign_directNorth_eq_evenParts (lam : YoungDiagram) :
    (-1 : ℤ) ^ TableauStripSigns.directNorth lam =
      (-1 : ℤ) ^ EKSchurOrthonormalControls.evenParts lam.rowLens := by
  rw [sign_directNorth_eq_transposeChoose, EKSchurOrthonormal.sign_bridge]

/-- Control: the bridge is genuinely parity-level.  For λ = (1,1,1) the statistics differ
(`C(λᵀ,2) = 3`, `λ₂ = 1`) while the signs agree. -/
theorem sign_bridge_is_parity_only :
    EKSchurOrthonormalControls.transposeChoose EKSchurOrthonormalControls.sh111.val ≠
        EKSchurOrthonormalControls.evenParts EKSchurOrthonormalControls.sh111.val.rowLens ∧
      (-1 : ℤ) ^ TableauStripSigns.directNorth EKSchurOrthonormalControls.sh111.val = -1 := by
  obtain ⟨h1, h2⟩ := EKSchurOrthonormalControls.sh111_signs
  refine ⟨by rw [h1, h2]; decide, ?_⟩
  rw [sign_directNorth_eq_evenParts, h2]
  norm_num

end OddMath.Frontier.EKClosureCompositionControls
