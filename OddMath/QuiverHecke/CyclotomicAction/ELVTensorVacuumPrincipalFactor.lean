import OddMath.QuiverHecke.CyclotomicAction.ELVTensorVacuumWholeInput
import OddMath.QuiverHecke.SwappedAssembly.Sigma.VacuumInverseWindow

/-! # The chosen principal inverse on the supported tensor vacuum

SwappedVacuumNonpositiveBubbles §4 (13): at equal levels the prescribed
negative augmented inverse is the inverse of the positive mixed bend.
Removing its two zero-padding charts retains the actual chosen inverse.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
open CyclotomicAction SwappedAssembly SKM
universe u
local instance principalFactorHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ)
  (L : I × ℕ → ℕ) (ΛP ΛR : X)
  (hcP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hcR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "bound" => PowerWordContent.powerBound D cutoff L
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hcP hcR
local notation "Z" => SupportedSectors.tensorVacuum D Sc m cutoff L ΛP ΛR

/-- Empty output content in the original weight presentation of the formal vacuum. -/
def tensorSectorEmpty : WeightBlocks D ΛR ((P).muM (0,0)) :=
  ⟨0, by simp [blockWeight, ProbeReservoir.muM, elvProbeReservoir]⟩
local notation "E" => SupportedSectors.reservoirOutputEval D Sc m cutoff bound ΛP ΛR hcP hcR
  (0,0) (tensorSectorEmpty D Sc m cutoff L ΛP ΛR hcP hcR)

variable (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous) (i : I)
local notation "c" => elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hcP hcR sy hc

/-- The unpadded principal is exactly the specified supported-vacuum inverse,
with no assumption on a bend, cap or moment comparison. -/
def tensorVacuumPrincipalFactorIso (hlevel : probeCutoff D m i = cutoff i) :
    (E).obj ((P).centralSourceFactor i (0,0) (Z).obj ⟨true, by trivial⟩) ≅
      (E).obj ((P).centralTargetFactor i (0,0) (Z).obj ⟨false, by trivial⟩) := by
  have hh : D.h i ((P).wt (0,0)) = 0 := by
    rw [SupportedSectors.vacuum_height_eq, hlevel, sub_self]
  exact ((P).centralSourceCornerIso i (0,0) (Z).obj E ⟨true, by trivial⟩).symm ≪≫
    SupportedSectors.vacuumPrincipalIso D Sc m cutoff bound ΛP ΛR hcP hcR sy hc i Z
      (tensorSectorEmpty D Sc m cutoff L ΛP ΛR hcP hcR) hh ≪≫
        (P).centralTargetCornerIso i (0,0) (Z).obj E ⟨false, by trivial⟩

/-- Its forward map is the prescribed positive mixed entry before zero padding. -/
theorem tensorVacuumPrincipalFactorIso_hom (hlevel : probeCutoff D m i = cutoff i) :
    (tensorVacuumPrincipalFactorIso D Sc m cutoff L ΛP ΛR hcP hcR sy hc i hlevel).hom =
      (E).map ((P).centralFactorSigma c i (0,0) (Z).obj ⟨true, by trivial⟩ ⟨false, by trivial⟩) := by
  simp only [tensorVacuumPrincipalFactorIso, Iso.trans_hom, Iso.symm_hom,
    SupportedSectors.vacuumPrincipalIso, ProbeReservoir.centralPaddedSigma,
    dite_eq_left (show StepValid (up i) true ((0,0) : Sector I) from by trivial),
    dite_eq_left (show StepValid (dn i) false ((0,0) : Sector I) from by trivial),
    Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- The inverse is the principal row of the same chosen negative matrix,
with exactly the two displayed corner transports. -/
theorem tensorVacuumPrincipalFactorIso_inv (hlevel : probeCutoff D m i = cutoff i) :
    let hh : D.h i ((P).wt (0,0)) = 0 := by
      rw [SupportedSectors.vacuum_height_eq, hlevel, sub_self]
    (tensorVacuumPrincipalFactorIso D Sc m cutoff L ΛP ΛR hcP hcR sy hc i hlevel).inv =
      ((P).centralTargetCornerIso i (0,0) (Z).obj E ⟨false, by trivial⟩).inv ≫
        (SupportedSectors.vacuumCupInverseData D Sc m cutoff bound ΛP ΛR hcP hcR sy hc i Z
          (tensorSectorEmpty D Sc m cutoff L ΛP ΛR hcP hcR) hh.le).principal ≫
        ((P).centralSourceCornerIso i (0,0) (Z).obj E ⟨true, by trivial⟩).hom := by
  simp only [tensorVacuumPrincipalFactorIso, Iso.trans_inv, Iso.symm_inv,
    SupportedSectors.vacuumPrincipalIso, Category.assoc]

end OddMath.QuiverHecke.ELVOld.WeightTensorVacuum
