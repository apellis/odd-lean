import OddMath.QuiverHecke.ReservoirFusedDetection
import OddMath.QuiverHecke.ReservoirFusedSectors
import OddMath.QuiverHecke.ReservoirVacuumExamples

/-! Two-odd-colour consumers of the fused-vacuum detection reduction.
The fused action, fusion inversion and the mate projection formula remain
hypotheses; these checks instantiate the datum-dependent parts. -/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke OddMath.QuiverHecke.ReservoirVacuumExamples

def cs : OddMath.SKM.CScalars params where
  c := fun _ _ => 1
  shift := by intros; simp [params]

/-- The headline at the two-odd-colour datum, for any ambient 2-supercategory. -/
example {B : Type} [BicategoryStruct.{0,0} B]
    [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear ℚ (a ⟶ b)]
    [∀ a b : B, Supercategory ℚ (a ⟶ b)] [TwoSupercategory ℚ B]
    (A : ∀ μ, FusedVacuumAction datum params cs μ B)
    (hM : ∀ μ, (A μ).MateProjections) :
    OddMath.SKM.WeakMate.UpwardIndependence cs :=
  upward_independence_of_fused_vacuum_actions A hM

/-- With sector summands the mate projection hypothesis is discharged. -/
example {B : Type} [BicategoryStruct.{0,0} B]
    [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear ℚ (a ⟶ b)]
    [∀ a b : B, Supercategory ℚ (a ⟶ b)] [TwoSupercategory ℚ B]
    (A : ∀ μ, FusedSectorAction datum params cs μ B) :
    OddMath.SKM.WeakMate.UpwardIndependence cs :=
  upward_independence_of_fused_sector_actions A

/-- The sector normalization is satisfiable with a nontrivial probe series at an
odd colour (`q = -1`), with reservoir coefficients carrying the product of the
two exterior generators. -/
example (n : ℕ) :
    ∑ r ∈ Finset.range (n + 1), (koszulSign 1 1) ^ r •
      ((((koszulSign 1 1 ^ r : ℤ) : ℚ) * (if r = 0 then 1 else 3)) •
        OddMath.SKM.reservoirDeconvolution
          (fun m => OddMath.SKM.SYM.e datum ℚ false m +
            OddMath.SKM.SYM.delta datum ℚ i * OddMath.SKM.SYM.delta datum ℚ j)
          (fun s => algebraMap ℚ _ (if s = 0 then 1 else 3)) (n - r)) =
      OddMath.SKM.SYM.e datum ℚ false n +
        OddMath.SKM.SYM.delta datum ℚ i * OddMath.SKM.SYM.delta datum ℚ j :=
  sector_normalize_deconvolution (D := datum) 1 (fun r => if r = 0 then 1 else 3) (by simp)
    (fun m => OddMath.SKM.SYM.e datum ℚ false m +
      OddMath.SKM.SYM.delta datum ℚ i * OddMath.SKM.SYM.delta datum ℚ j) n

/-- With a probe series of constant term one, the normalization is not the
identity: the degree-one reservoir coefficient differs from the fused one. -/
example : OddMath.SKM.reservoirDeconvolution
    (fun m => OddMath.SKM.SYM.e datum ℚ false m)
    (fun s => algebraMap ℚ (OddMath.SKM.SYM datum ℚ) (if s = 0 then 1 else 3)) 1 =
      OddMath.SKM.SYM.e datum ℚ false 1 -
        OddMath.SKM.SYM.e datum ℚ false 0 * algebraMap ℚ _ 3 := by
  have h0 : ∀ C P : ℕ → OddMath.SKM.SYM datum ℚ,
      OddMath.SKM.reservoirDeconvolution C P 0 = C 0 := by
    intro C P
    rw [OddMath.SKM.reservoirDeconvolution]
    simp
  rw [OddMath.SKM.reservoirDeconvolution, Fin.sum_univ_one]
  simp [h0]

#print axioms mate_projection_sector_bubble
#print axioms sector_normalize_deconvolution
#print axioms VacuumBubbleSector.bubbles_eq
#print axioms VacuumBubbleSectors.fused_bubbles_eq_reservoir
#print axioms VacuumBubbleSectors.fused_odd_bubble
#print axioms FusedVacuumWords.evaluation
#print axioms FusedVacuumWords.evaluation_normalizedBubbleFormula
#print axioms FusedRegularVacuumFamily.toFamily
#print axioms FusedVacuumAction.toFamily
#print axioms upward_independence_of_fused_vacuum_actions
#print axioms VacuumSectorBubble.toSector_mateProjection
#print axioms VacuumSectorBubble.bubbles_eq
#print axioms upward_independence_of_fused_sector_actions
