import OddMath.QuiverHecke.CyclotomicAction.ELVShiftedMatrixFamilies
import OddMath.QuiverHecke.CyclotomicAction.ELVUnitPositiveInverse
import OddMath.Algebra.LowPolynomialCoordinates

/-! # Finite shifted coordinates for the unscaled unit columns

DeformedMatrixComparison (6) uses the explicit diagonal source units d_r.
They convert the literal polynomial columns to the ordinary, unscaled
adjunction-unit/induction-dot columns in the shifted finite source family.
The first coordinate remains the specified signed balanced crossing until
the ordered-mate comparison is proved. No column equality is assumed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
open OddMath.LowPolynomialCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
local instance unitFamilyPi : PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory

/-- The prescribed dot-power scalar as a unit, including either moving parity. -/
def inductionUnitDotUnit (p : ZMod 2) (n : ℕ) : kˣ where
  val := inductionUnitDotSign (k := k) p n
  inv := inductionUnitDotSign (k := k) p n
  val_inv := Supercategory.sign_mul_self _
  inv_val := Supercategory.sign_mul_self _

/-- The finite coordinate sign change is invertible without a field premise. -/
def unitCoefficientDiagonal (p : ZMod 2) (v t : List I) (m : ℕ) :
    (Fin m → Old D Sc cutoff v t) ≃ₗ[k] (Fin m → Old D Sc cutoff v t) :=
  LinearEquiv.piCongrRight fun r => LinearEquiv.smulOfUnit (inductionUnitDotUnit (k := k) p r.val)

@[simp] theorem unitCoefficientDiagonal_apply (p : ZMod 2) (v t : List I) (m : ℕ)
    (b : Fin m → Old D Sc cutoff v t) (r : Fin m) :
    unitCoefficientDiagonal D Sc cutoff p v t m b r = inductionUnitDotSign (k := k) p r.val • b r := by
  change ((inductionUnitDotUnit (k := k) p r.val : kˣ) : k) • b r = _
  rfl

/-- The source diagonal produces the unscaled ordinary unit/dot columns. -/
theorem unitDotPolynomialMap_diagonal (i : I) (v t : List I) (m : ℕ)
    (b : Fin m → Old D Sc cutoff v t) :
    unitDotPolynomialMap D Sc cutoff i v t
      ((lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m
        (unitCoefficientDiagonal D Sc cutoff (D.parity i) v t m b)).val) =
      ∑ r : Fin m, inductionUnitDotColumn D Sc cutoff i v t r.val (b r) := by
  classical
  let L : (Fin m → Old D Sc cutoff v t) →ₗ[k] Old D Sc cutoff (v ++ [i]) (t ++ [i]) :=
    (unitDotPolynomialMap D Sc cutoff i v t).comp
      ((Finsupp.supported (Old D Sc cutoff v t) k (Set.Iio m)).subtype.comp
        (lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m).toLinearMap)
  have hsum : unitCoefficientDiagonal D Sc cutoff (D.parity i) v t m b =
      ∑ r : Fin m, Pi.single r (inductionUnitDotSign (k := k) (D.parity i) r.val • b r) := by
    ext r
    simp only [unitCoefficientDiagonal_apply, Finset.sum_apply, Pi.single_apply]
    simp
  change L (unitCoefficientDiagonal D Sc cutoff (D.parity i) v t m b) = _
  rw [hsum, map_sum]
  apply Finset.sum_congr rfl
  intro r _
  change unitDotPolynomialMap D Sc cutoff i v t
    ((lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m
      (Pi.single r (inductionUnitDotSign (k := k) (D.parity i) r.val • b r))).val) = _
  rw [lowVectorEquiv_single, ← Finsupp.smul_single, map_smul, unitDotPolynomialMap_single]
  exact (inductionUnitDotColumn_apply D Sc cutoff i v t r.val (b r)).symm

/-- Finite vectors identify the literal positive polynomial window. -/
def unitWindowVectorEquiv (j : {j : I // D.parity j = 1}) (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff j.1 v = outputSDegree D j.1 v + m) :
    (Fin m → Old D Sc cutoff v t) ≃ₗ[k] offDiagonalBoundaryRowWindow D Sc cutoff j v t :=
  (lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m).trans
    (LinearEquiv.ofEq _ _ (offDiagonalBoundaryRowWindow_eq_height D Sc cutoff j v t m hm).symm)

private def parityComponentEquiv (p : ZMod 2)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k)) (t : OldCategory D Sc cutoff) :
    ((SKM.homParityShift (k := k) p).obj M).obj t ≃ₗ[k] M.obj t :=
  moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) p).iso M) t

/-- Canonical parity isomorphisms remove the finite source shifts on components. -/
def unitFamilyPlainCoordinates (i : I) (v t : List I) (m : ℕ) :
    ((a : Option (Fin m)) →
      (unitMatrixFamily D Sc cutoff i
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m a).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) ≃ₗ[k]
    ((((BalancedInduction.induction (append D Sc cutoff i)).obj
      ((BalancedInduction.restriction (append D Sc cutoff i)).obj
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) × (Fin m → Old D Sc cutoff v t)) :=
  (LinearEquiv.piOptionEquivProd k).trans
    ((parityComponentEquiv D Sc cutoff (D.parity i)
      ((BalancedInduction.induction (append D Sc cutoff i)).obj
        ((BalancedInduction.restriction (append D Sc cutoff i)).obj
          (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))) ⟨t⟩).prodCongr
      (LinearEquiv.piCongrRight fun r : Fin m => parityComponentEquiv D Sc cutoff
        (r.val • D.parity i) (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) ⟨t⟩))

/-- The explicit diagonal source units followed by the literal polynomial window. -/
def unitFamilyComponentCoordinates (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff j.1 v = outputSDegree D j.1 v + m) :
    ((a : Option (Fin m)) →
      (unitMatrixFamily D Sc cutoff j.1
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m a).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) ≃ₗ[k]
    ((((BalancedInduction.induction (append D Sc cutoff j.1)).obj
      ((BalancedInduction.restriction (append D Sc cutoff j.1)).obj
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)))).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) × offDiagonalBoundaryRowWindow D Sc cutoff j v t) :=
  (unitFamilyPlainCoordinates D Sc cutoff j.1 v t m).trans
    ((LinearEquiv.refl k _).prodCongr
      ((unitCoefficientDiagonal D Sc cutoff (D.parity j.1) v t m).trans
        (unitWindowVectorEquiv D Sc cutoff j v t m hm)))

/-- Component inverse with the prescribed unscaled unit columns on the shifted source family. -/
def unitFamilyComponentEquiv (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff j.1 v = outputSDegree D j.1 v + m) :
    ((a : Option (Fin m)) →
      (unitMatrixFamily D Sc cutoff j.1
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m a).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) ≃ₗ[k]
      Old D Sc cutoff (v ++ [j.1]) (t ++ [j.1]) :=
  (unitFamilyComponentCoordinates D Sc cutoff j v t m hm).trans
    (unitPositiveMatrixEquiv D Sc cutoff p j v t (by omega))

/-- Every unit slot is the ordinary, unscaled adjunction-unit/dot column.
The first slot remains the specified signed balanced crossing until the mate comparison. -/
theorem unitFamilyComponentEquiv_apply (p : ZMod 2) (j : {j : I // D.parity j = 1})
    (v t : List I) (m : ℕ)
    (hm : endpointQPDegree D cutoff j.1 v = outputSDegree D j.1 v + m)
    (x : (a : Option (Fin m)) →
      (unitMatrixFamily D Sc cutoff j.1
        (oldRepresentable D Sc cutoff (⟨v⟩ : OldCategory D Sc cutoff)) m a).obj
          (⟨t⟩ : OldCategory D Sc cutoff)) :
    unitFamilyComponentEquiv D Sc cutoff p j v t m hm x =
      -toCyclotomic D Sc cutoff j.1 v t
        (shiftedSourceCanonicalEquiv D Sc cutoff j v t
          (unitFamilyPlainCoordinates D Sc cutoff j.1 v t m x).1) +
      ∑ r : Fin m, inductionUnitDotColumn D Sc cutoff j.1 v t r.val
        ((unitFamilyPlainCoordinates D Sc cutoff j.1 v t m x).2 r) := by
  rw [unitFamilyComponentEquiv, LinearEquiv.trans_apply]
  rw [show (unitFamilyComponentCoordinates D Sc cutoff j v t m hm x) =
      ((unitFamilyPlainCoordinates D Sc cutoff j.1 v t m x).1,
        unitWindowVectorEquiv D Sc cutoff j v t m hm
          (unitCoefficientDiagonal D Sc cutoff (D.parity j.1) v t m
            (unitFamilyPlainCoordinates D Sc cutoff j.1 v t m x).2)) from rfl,
    unitPositiveMatrixEquiv_apply]
  congr 1
  change unitDotPolynomialMap D Sc cutoff j.1 v t
    ((lowVectorEquiv (k := k) (M := Old D Sc cutoff v t) m
      (unitCoefficientDiagonal D Sc cutoff (D.parity j.1) v t m
        (unitFamilyPlainCoordinates D Sc cutoff j.1 v t m x).2)).val) = _
  exact unitDotPolynomialMap_diagonal D Sc cutoff j.1 v t m _

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
