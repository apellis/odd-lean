import OddMath.SKM.RouquierCoupledMate
import OddMath.SKM.RouquierCoupledSectors
import OddMath.QuiverHecke.ReservoirVacuumExamples

/-!
Consumers of the coupled separated-sector assembly.

* The rational cross-sector entries at an odd colour (`q = koszulSign 1 1 = -1`)
  in `2 × 2` rational matrices, with a nilpotent dot that does not commute with
  the invertible one: both separated slides hold, and the left entry is not the
  naive inverse `Z`.
* The coupled slide, coupled adjunction triangles and coupled mate projection
  formula for any coupled separated factors.
* Detection at the two-odd-colour datum from coupled separated factors.

The factor data of `CoupledFactors`, the vacuum values and the fused bubble
identification remain hypotheses.
-/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
open OddMath.SKM OddMath.QuiverHecke OddMath.QuiverHecke.ReservoirVacuumExamples

namespace CoupledConsumer

/-- A nilpotent dot. -/
def X : Matrix (Fin 2) (Fin 2) ℚ := !![0, 0; 1, 0]
/-- An invertible dot that does not commute with `X`. -/
def Y : Matrix (Fin 2) (Fin 2) ℚ := !![1, 1; 0, 1]
/-- The inverse of `Y`. -/
def Z : Matrix (Fin 2) (Fin 2) ℚ := !![1, -1; 0, 1]

theorem X_sq : X ^ 2 = 0 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [X, pow_two, Matrix.mul_apply, Fin.sum_univ_two]

theorem Y_Z : Y * Z = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Y, Z, Matrix.mul_apply, Fin.sum_univ_two]

theorem Z_Y : Z * Y = 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Y, Z, Matrix.mul_apply, Fin.sum_univ_two]

/-- The two dots do not commute. -/
example : X * Y ≠ Y * X := by
  intro h
  have := congrFun (congrFun h 1) 1
  simp [X, Y, Matrix.mul_apply, Fin.sum_univ_two] at this

/-- The left rational entry at an odd colour solves its separated slide. -/
example : Y * coupledRationalLeft (koszulSign 1 1) X Z 2 -
    koszulSign 1 1 • (coupledRationalLeft (koszulSign 1 1) X Z 2 * X) = 1 :=
  coupledRationalLeft_spec _ 2 Y_Z X_sq

/-- The right rational entry at an odd colour solves its separated slide. -/
example : X * coupledRationalRight (koszulSign 1 1) X Z 2 -
    koszulSign 1 1 • (coupledRationalRight (koszulSign 1 1) X Z 2 * Y) = 1 :=
  coupledRationalRight_spec (koszulSign_mul_self 1 1) 2 Z_Y X_sq

/-- The left rational entry is the series `Z - Z² X`, not the inverse `Z` of the
probe dot alone. -/
example : coupledRationalLeft (koszulSign 1 1) X Z 2 = Z - Z ^ 2 * X := by
  simp [coupledRationalLeft, Finset.sum_range_succ, sub_eq_add_neg]

example : coupledRationalLeft (koszulSign 1 1) X Z 2 ≠ Z := by
  intro h
  have := congrFun (congrFun h 0) 0
  simp [coupledRationalLeft, Finset.sum_range_succ, X, Z, pow_two] at this

end CoupledConsumer

section
variable {k : Type*} [CommRing k] {B : Type*} [BicategoryStruct B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

/-- The coupled slide at an odd colour. -/
example {a b c : B} (C : CoupledFactors (k := k) a b c) (hp : C.p = 1) :
    C.coupledCross ≫ C.E₁ ◁ C.x₂ + C.x₁ ▷ C.E₂ ≫ C.coupledCross = 𝟙 _ := by
  have := C.slide
  rw [hp, koszulSign_one_one, neg_one_zsmul, sub_neg_eq_add] at this
  exact this

/-- The coupled counit restricts to the sector counits. -/
example {a b c : B} (C : CoupledFactors (k := k) a b c) (s : CoupledSector) :
    sectorIn (C.DE₁.inc s) (C.DF₁.inc s) ≫ C.A₁.counit = (C.adj₁ s).counit :=
  (C.sourceSector s).counit_comm

/-- The probe-to-reservoir projection of the coupled mate at an odd colour is the
sector mate of the rational block. -/
example {a b c : B} (C : CoupledFactors (k := k) a b c) :
    sectorIn (C.DE₁.inc CoupledSector.probe) (C.DF₁.inc CoupledSector.probe) ≫
        rouquierMate C.A₁ C.A₂ C.coupledCross ≫
          sectorOut (C.DE₂.proj CoupledSector.reservoir) (C.DF₂.proj CoupledSector.reservoir) =
      rouquierMate (C.adj₁ CoupledSector.probe) (C.adj₂ CoupledSector.reservoir)
        C.rationalPR :=
  C.probe_mate_reservoir

end

/-- Detection at the two-odd-colour datum from coupled separated factors. -/
example {B : Type} [BicategoryStruct.{0,0} B]
    [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear ℚ (a ⟶ b)]
    [∀ a b : B, Supercategory ℚ (a ⟶ b)] [TwoSupercategory ℚ B]
    (cs : CScalars params)
    (A : ∀ μ, FusedCoupledAction datum params cs μ B) :
    WeakMate.UpwardIndependence cs :=
  upward_independence_of_fused_coupled_actions A

#print axioms coupledRationalLeft_spec
#print axioms coupledRationalRight_spec
#print axioms SectorDecomp.comp
#print axioms coupledAdjunction
#print axioms CoupledFactors.slide
#print axioms CoupledFactors.sourceSector
#print axioms CoupledFactors.targetSector
#print axioms CoupledFactors.mateProjectionFormula
#print axioms sectorIn_rouquierMate
#print axioms rouquierMate_sectorOut
#print axioms CoupledFactors.sector_mate_block
#print axioms CoupledFactors.probe_mate_reservoir
#print axioms CoupledSectorBubble.fused
#print axioms CoupledSectorBubble.toVacuumSectorBubble
#print axioms CoupledSectorBubble.bubbles_eq
#print axioms FusedCoupledAction.toSectorAction
#print axioms upward_independence_of_fused_coupled_actions
