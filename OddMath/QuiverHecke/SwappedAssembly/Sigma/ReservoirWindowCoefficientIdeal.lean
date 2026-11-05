import OddMath.QuiverHecke.SwappedAssembly.Sigma.ReservoirWindowInverseData
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.ProductCoefficients
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.ResidualComparison
import OddMath.QuiverHecke.CyclotomicAction.ELVContentHomZero
import OddMath.QuiverHecke.CyclotomicAction.ELVReservoirClosureIdeal
import OddMath.QuiverHecke.CyclotomicAction.ELVReservoirBoundaryIdeal

/-! # Padded chosen reservoir contractions in the fixed-output coefficient ideal

SwappedHomInversion §4 (7)–(9): the named principal and finite inverse
entries of ReservoirWindowInverseData retain their source coefficient
ideal membership after the actual whole-output evaluation. Padding charts
cancel before the native closure and boundary ideal theorems are applied.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM BicategoryStruct
open scoped Classical
namespace OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir
universe u uB v w
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type uB} [BicategoryStruct.{w, v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k} (P : ProbeReservoir k B D Sc)
  {C : Type*} [Category C] [Preadditive C] [Limits.HasZeroObject C]
  (c : P.CrossCoeff) (i : I) (t : Sector I) (Z : P.H t)
  (E : P.H t ⥤ C) [E.Additive]
/-- The occupied padded cap principal closes to the same native chosen principal. -/
theorem reservoirCapInverseData_closure_eq (hh : 0 ≤ D.h i (P.muM t))
    (ha : StepValid (up i) false t) (r s : ℕ) :
    P.centralPaddedUnit i t Z E false r ≫
      (P.centralPaddedReservoir_capInverseData c i t Z E ha hh).principal ≫
        P.centralPaddedCap i t Z E false s =
    E.map (homContentPostCup P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t) r Z ≫
      (homContentPostInvPos P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i ha) (P.muM_postF i t) hh Z).f' ≫
        homContentPostCap P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i ha) s Z) := by
  have hp : (P.centralPaddedReservoir_capInverseData c i t Z E ha hh).principal =
      (P.centralTargetCornerIso i t Z E ⟨false, by trivial⟩).hom ≫
        E.map (homContentPostInvPos P.T.obj P.W i t.1 (P.muP t)
          (P.muM_postE i ha) (P.muM_postF i t) hh Z).f' ≫
            (P.centralSourceCornerIso i t Z E ⟨false, ha⟩).inv := rfl
  rw [hp]
  simp only [ProbeReservoir.centralPaddedUnit, ProbeReservoir.centralPaddedCap,
    dite_eq_left ha, dite_eq_left (show StepValid (dn i) false t from by trivial),
    ProbeReservoir.centralFactorUnit, ProbeReservoir.centralFactorCap,
    Category.assoc, Iso.inv_hom_id_assoc, ← E.map_comp]

/-- The occupied padded unit principal closes to the same native chosen principal. -/
theorem reservoirCupInverseData_closure_eq (hh : D.h i (P.muM t) ≤ 0)
    (ha : StepValid (up i) false t) (r s : ℕ) :
    P.centralPaddedUnit i t Z E false r ≫
      (P.centralPaddedReservoir_cupInverseData c i t Z E ha hh).principal ≫
        P.centralPaddedCap i t Z E false s =
    E.map (homContentPostCup P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t) r Z ≫
      (homContentPostInvNeg P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i ha) (P.muM_postF i t) hh Z).f' ≫
        homContentPostCap P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i ha) s Z) := by
  have hp : (P.centralPaddedReservoir_cupInverseData c i t Z E ha hh).principal =
      (P.centralTargetCornerIso i t Z E ⟨false, by trivial⟩).hom ≫
        E.map (homContentPostInvNeg P.T.obj P.W i t.1 (P.muP t)
          (P.muM_postE i ha) (P.muM_postF i t) hh Z).f' ≫
            (P.centralSourceCornerIso i t Z E ⟨false, ha⟩).inv := rfl
  rw [hp]
  simp only [ProbeReservoir.centralPaddedUnit, ProbeReservoir.centralPaddedCap,
    dite_eq_left ha, dite_eq_left (show StepValid (dn i) false t from by trivial),
    ProbeReservoir.centralFactorUnit, ProbeReservoir.centralFactorCap,
    Category.assoc, Iso.inv_hom_id_assoc, ← E.map_comp]

/-- The occupied finite cap column contracts to the literal native boundary. -/
theorem reservoirCapInverseData_boundary_eq (hh : 0 ≤ D.h i (P.muM t))
    (ha : StepValid (up i) false t) (j : Fin (D.h i (P.muM t)).toNat) (r : ℕ) :
    (P.centralPaddedReservoir_capInverseData c i t Z E ha hh).window j ≫
      P.centralPaddedCap i t Z E false r =
    E.map ((homContentPostInvPos P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i ha) (P.muM_postF i t) hh Z).g' j ≫
      homContentPostCap P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i ha) r Z) := by
  have hp : (P.centralPaddedReservoir_capInverseData c i t Z E ha hh).window j =
      E.map ((homContentPostInvPos P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i ha) (P.muM_postF i t) hh Z).g' j) ≫ (P.centralSourceCornerIso i t Z E ⟨false, ha⟩).inv := rfl
  rw [hp]
  simp only [ProbeReservoir.centralPaddedCap, dite_eq_left ha, ProbeReservoir.centralFactorCap,
    Category.assoc, Iso.inv_hom_id_assoc, ← E.map_comp]

/-- The occupied finite unit row contracts to the literal native boundary. -/
theorem reservoirCupInverseData_boundary_eq (hh : D.h i (P.muM t) ≤ 0)
    (ha : StepValid (up i) false t) (j : Fin (-D.h i (P.muM t)).toNat) (r : ℕ) :
    P.centralPaddedUnit i t Z E false r ≫
      (P.centralPaddedReservoir_cupInverseData c i t Z E ha hh).window j =
    E.map (homContentPostCup P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t) r Z ≫
      (homContentPostInvNeg P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i ha) (P.muM_postF i t) hh Z).g' j) := by
  have hp : (P.centralPaddedReservoir_cupInverseData c i t Z E ha hh).window j =
      (P.centralTargetCornerIso i t Z E ⟨false, by trivial⟩).hom ≫ E.map ((homContentPostInvNeg P.T.obj P.W i t.1 (P.muP t) (P.muM_postE i ha) (P.muM_postF i t) hh Z).g' j) := rfl
  rw [hp]
  simp only [ProbeReservoir.centralPaddedUnit,
    dite_eq_left (show StepValid (dn i) false t from by trivial), ProbeReservoir.centralFactorUnit,
    Category.assoc, Iso.inv_hom_id_assoc, ← E.map_comp]

/-- An absent finite unit row retains its synthetic native predecessor and boundary. -/
theorem reservoirCupInverseData_boundary_eq_of_absent (hh : D.h i (P.muM t) ≤ 0)
    {μ : X} (h : μ + D.α i = P.muM t)
    (hzero : Limits.IsZero ((homContentPostE P.T.obj P.W i t.1 (P.muP t) h).obj
      ((homContentPostF P.T.obj P.W i t.1 (P.muP t) h).obj Z)))
    (ha : ¬StepValid (up i) false t) (j : Fin (-D.h i (P.muM t)).toNat) (r : ℕ) :
    P.centralPaddedUnit i t Z E false r ≫
      (P.centralPaddedReservoir_cupInverseData_of_source_isZero c i t Z E ha h hzero hh).window j =
    E.map (homContentPostCup P.T.obj P.W i t.1 (P.muP t) (P.muM_postF i t) r Z ≫
      (homContentPostInvNeg P.T.obj P.W i t.1 (P.muP t)
        h (P.muM_postF i t) hh Z).g' j) := by
  have hp : (P.centralPaddedReservoir_cupInverseData_of_source_isZero c i t Z E ha h hzero hh).window j =
      (P.centralTargetCornerIso i t Z E ⟨false, by trivial⟩).hom ≫
        E.map ((homContentPostInvNeg P.T.obj P.W i t.1 (P.muP t) h (P.muM_postF i t) hh Z).g' j) := rfl
  rw [hp]
  simp only [ProbeReservoir.centralPaddedUnit,
    dite_eq_left (show StepValid (dn i) false t from by trivial), ProbeReservoir.centralFactorUnit,
    Category.assoc, Iso.inv_hom_id_assoc, ← E.map_comp]
end OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir

namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : Datum I X) (Sc : Scalars D k) (m : I → ℕ) (cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "Sc'" => parameterTwist D Sc
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR
local instance reservoirIdealHomPi (A B : PiSCat.{u,u,u + 1} k) :
    PiSupercategory k (A ⟶ B) := PiTwoSupercategory.homPiLeft A B

/-- Actual whole-output projection, retaining the input probe superfunctor. -/
def reservoirOutputEval (t : Sector I) (β : WeightBlocks D ΛR ((P).muM t)) :
    (P).H t ⥤ ((P).T.obj (-((P).muP t)) ⟶ contentModuleTarget D Sc' cutoff bound β.1) :=
  RegularReservoir.evalHomFunctor (k := k)
    (fun γ : WeightBlocks D ΛR ((P).muM t) => ContentModules D Sc' cutoff bound γ.1)
    ((P).T.obj (-((P).muP t))) β

instance reservoirOutputEval_additive (t : Sector I) (β : WeightBlocks D ΛR ((P).muM t)) :
    (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β).Additive := by
  exact inferInstanceAs (RegularReservoir.evalHomFunctor (k := k)
    (fun γ : WeightBlocks D ΛR ((P).muM t) => ContentModules D Sc' cutoff bound γ.1)
    ((P).T.obj (-((P).muP t))) β).Additive

/-- Projection objects retain the entire input functor and select only the output content. -/
theorem reservoirOutputEval_obj (t : Sector I) (β : WeightBlocks D ΛR ((P).muM t)) (A : (P).H t) :
    (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β).obj A =
      A.comp (elvBlockEval D Sc' cutoff bound ΛR β) := rfl

/-- This projection is the native output whiskering used by the source ideal APIs. -/
theorem reservoirOutputEval_map (t : Sector I) (β : WeightBlocks D ΛR ((P).muM t))
    {A B : (P).H t} (f : A ⟶ B) :
    (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β).map f =
      Superfunctor.whiskerRight f (elvBlockEval D Sc' cutoff bound ΛR β) := rfl

variable [Finite I] (sy : Symmetrizer D) (hc : Sc.Homogeneous)
  (i : I) (t : Sector I) (Z : H D Sc' m cutoff bound ΛP ΛR t)
  (β : WeightBlocks D ΛR ((P).muM t)) (c : (P).CrossCoeff)

/-- The named padded cap principal closes in the positive coefficient ideal. -/
theorem reservoirCapInverseData_closure_mem (i : I) (t : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
    (β : WeightBlocks D ΛR ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).muM t))
    (c : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).CrossCoeff)
    (hh : 0 ≤ D.h i ((P).muM t)) (r s : ℕ) :
    (contentModuleCoefficientIdeal D Sc' cutoff bound β.1 sy (parameterTwist_homogeneous D Sc hc) ((P).T.obj (-((P).muP t)))).mem 1 ((P).centralPaddedUnit i t Z.obj (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) false r ≫
      (reservoirCapInverseData D Sc m cutoff bound ΛP ΛR hP hR i t Z (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) c hh).principal ≫
        (P).centralPaddedCap i t Z.obj (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) false s) := by
  by_cases ha : StepValid (up i) false t
  · simp only [reservoirCapInverseData, dite_eq_left ha]
    rw [ProbeReservoir.reservoirCapInverseData_closure_eq]
    simpa only [reservoirOutputEval_map, reservoirOutputEval_obj, elvProbeReservoir_W, Category.id_comp, Category.comp_id] using
      ReservoirClosures.positiveClosure_evaluate_mem D Sc' cutoff bound ΛR hR i
        ((P).muM_postE i ha) ((P).muM_postF i t) β sy
        (parameterTwist_homogeneous D Sc hc) (P).T.obj t.1 ((P).muP t) hh r s
        (𝟙 Z.obj) (𝟙 Z.obj)
  · rw [reservoirCapInverseData_principal_of_absent D Sc m cutoff bound ΛP ΛR hP hR i t Z (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) c hh ha]
    simpa only [Limits.comp_zero, Limits.zero_comp] using (contentModuleCoefficientIdeal D Sc' cutoff bound β.1 sy (parameterTwist_homogeneous D Sc hc) ((P).T.obj (-((P).muP t)))).zero_mem 1

/-- The named padded unit principal closes in the positive coefficient ideal. -/
theorem reservoirCupInverseData_closure_mem (i : I) (t : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
    (β : WeightBlocks D ΛR ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).muM t))
    (c : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).CrossCoeff)
    (hh : D.h i ((P).muM t) ≤ 0) (r s : ℕ) :
    (contentModuleCoefficientIdeal D Sc' cutoff bound β.1 sy (parameterTwist_homogeneous D Sc hc) ((P).T.obj (-((P).muP t)))).mem 1 ((P).centralPaddedUnit i t Z.obj (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) false r ≫
      (reservoirCupInverseData D Sc m cutoff bound ΛP ΛR hP hR i t Z (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) c hh).principal ≫
        (P).centralPaddedCap i t Z.obj (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) false s) := by
  by_cases ha : StepValid (up i) false t
  · simp only [reservoirCupInverseData, dite_eq_left ha]
    rw [ProbeReservoir.reservoirCupInverseData_closure_eq]
    simpa only [reservoirOutputEval_map, reservoirOutputEval_obj, elvProbeReservoir_W, Category.id_comp, Category.comp_id] using
      ReservoirClosures.negativeClosure_evaluate_mem D Sc' cutoff bound ΛR hR i
        ((P).muM_postE i ha) ((P).muM_postF i t) β sy
        (parameterTwist_homogeneous D Sc hc) (P).T.obj t.1 ((P).muP t) hh r s
        (𝟙 Z.obj) (𝟙 Z.obj)
  · rw [reservoirCupInverseData_principal_of_absent D Sc m cutoff bound ΛP ΛR hP hR i t Z (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) c hh ha]
    simpa only [Limits.comp_zero, Limits.zero_comp] using (contentModuleCoefficientIdeal D Sc' cutoff bound β.1 sy (parameterTwist_homogeneous D Sc hc) ((P).T.obj (-((P).muP t)))).zero_mem 1

/-- Every named cap inverse column contracts off its finite window into level one. -/
theorem reservoirCapInverseData_boundary_mem (i : I) (t : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
    (β : WeightBlocks D ΛR ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).muM t))
    (c : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).CrossCoeff)
    (hh : 0 ≤ D.h i ((P).muM t))
    (j : Fin (D.h i ((P).muM t)).toNat) (r : ℕ) (hjr : (j : ℕ) < r) :
    (contentModuleCoefficientIdeal D Sc' cutoff bound β.1 sy (parameterTwist_homogeneous D Sc hc) ((P).T.obj (-((P).muP t)))).mem 1 ((reservoirCapInverseData D Sc m cutoff bound ΛP ΛR hP hR i t Z (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) c hh).window j ≫
      (P).centralPaddedCap i t Z.obj (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) false r) := by
  by_cases ha : StepValid (up i) false t
  · simp only [reservoirCapInverseData, dite_eq_left ha]
    rw [ProbeReservoir.reservoirCapInverseData_boundary_eq]
    simpa only [reservoirOutputEval_map, reservoirOutputEval_obj, elvProbeReservoir_W, Category.id_comp, Category.comp_id] using
      ReservoirBoundaries.positiveBoundary_evaluate_mem D Sc' cutoff bound ΛR hR i
        ((P).muM_postE i ha) ((P).muM_postF i t) β sy
        (parameterTwist_homogeneous D Sc hc) (P).T.obj t.1 ((P).muP t) hh j r j.isLt hjr
        (𝟙 Z.obj) (𝟙 Z.obj)
  · rw [reservoirCapInverseData_window_of_absent D Sc m cutoff bound ΛP ΛR hP hR i t Z (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) c hh ha]
    simpa only [Limits.zero_comp] using (contentModuleCoefficientIdeal D Sc' cutoff bound β.1 sy (parameterTwist_homogeneous D Sc hc) ((P).T.obj (-((P).muP t)))).zero_mem 1

/-- The absent unit rows retain their native positive-degree off-window boundary. -/
theorem reservoirCupInverseData_boundary_mem (i : I) (t : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
    (β : WeightBlocks D ΛR ((elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).muM t))
    (c : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).CrossCoeff)
    (hh : D.h i ((P).muM t) ≤ 0)
    (j : Fin (-D.h i ((P).muM t)).toNat) (r : ℕ) (hjr : (j : ℕ) < r) :
    (contentModuleCoefficientIdeal D Sc' cutoff bound β.1 sy (parameterTwist_homogeneous D Sc hc) ((P).T.obj (-((P).muP t)))).mem 1 ((P).centralPaddedUnit i t Z.obj (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) false r ≫
      (reservoirCupInverseData D Sc m cutoff bound ΛP ΛR hP hR i t Z (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β) c hh).window j) := by
  by_cases ha : StepValid (up i) false t
  · simp only [reservoirCupInverseData, dite_eq_left ha]
    rw [ProbeReservoir.reservoirCupInverseData_boundary_eq]
    simpa only [reservoirOutputEval_map, reservoirOutputEval_obj, elvProbeReservoir_W, Category.id_comp, Category.comp_id] using
      ReservoirBoundaries.negativeBoundary_evaluate_mem D Sc' cutoff bound ΛR hR i
        ((P).muM_postE i ha) ((P).muM_postF i t) β sy
        (parameterTwist_homogeneous D Sc hc) (P).T.obj t.1 ((P).muP t) hh j r j.isLt hjr
        (𝟙 Z.obj) (𝟙 Z.obj)
  · simp only [reservoirCupInverseData, dite_eq_right ha]
    rw [ProbeReservoir.reservoirCupInverseData_boundary_eq_of_absent]
    simpa only [reservoirOutputEval_map, reservoirOutputEval_obj, elvProbeReservoir_W, Category.id_comp, Category.comp_id] using
      ReservoirBoundaries.negativeBoundary_evaluate_mem D Sc' cutoff bound ΛR hR i
        (show (P).muM t - D.α i + D.α i = (P).muM t from sub_add_cancel _ _)
        ((P).muM_postF i t) β sy
        (parameterTwist_homogeneous D Sc hc) (P).T.obj t.1 ((P).muP t) hh j r j.isLt hjr
        (𝟙 Z.obj) (𝟙 Z.obj)

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
