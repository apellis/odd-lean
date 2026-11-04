import NonVacuity.ELVWeightedAppendFixture
import OddMath.QuiverHecke.CyclotomicAction.ELVReservoirBoundaryIdeal
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightCentreBlocks
import OddMath.QuiverHecke.CyclotomicAction.ELVReservoirBoundaries
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedDetection
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace NonVacuity.ELVReservoirBoundaryIdeal.Absent
private theorem identity_total {C E : Type*} [Category C] [Category E]
    [Preadditive C] [Linear ℚ C] [Supercategory ℚ C]
    [Preadditive E] [Linear ℚ E] [Supercategory ℚ E]
    (F : Superfunctor ℚ C E) (a : C) :
    (𝟙 F : F ⟶ F).total a = 𝟙 (F.obj a) :=
  SuperNatTrans.id_total F.toFunctor a
private def D : SKM.Datum Unit ℤ where
  cd := {
    root := fun _ => 2
    coroot := fun _ => LinearMap.id
    coroot_root_self := fun _ => rfl }
  isGCM := {
    diag := fun _ => rfl
    offDiag_nonpos := fun i j h => absurd (Subsingleton.elim i j) h
    zero_comm := fun _ _ => Iff.rfl }
  parity := fun _ => 1
  even_of_odd := fun _ _ _ => even_two
private def Sc : SKM.Scalars D ℚ where
  t := fun _ _ => 1
  t_self := fun _ => rfl
  t_symm_of_d_eq_zero := fun _ _ _ => rfl
  s := fun _ _ _ _ => 0
  s_symm := fun _ _ _ _ => rfl
  s_eq_zero := fun _ _ _ _ _ => rfl
  two_isUnit := fun _ => isUnit_iff_ne_zero.mpr (by norm_num)
private def cutoff (_ : Unit) : ℕ := 2
private def Λ : ℤ := 2
private theorem cutoff_match (i : Unit) : (cutoff i : ℤ) = D.h i Λ := rfl
private theorem h₁ : (-4 : ℤ) + D.α () = -2 := by decide
private theorem h₂ : (-2 : ℤ) + D.α () = 0 := by decide
private def δ : WeightBlocks D Λ (-2) := ⟨0,by decide⟩
private def v : ContentCategory D Sc cutoff 3 δ.1 := ⟨⟨[]⟩,rfl⟩
private def R := contentRepresentable D Sc cutoff 3 δ.1 v
private def M : ELVWeightProduct D Sc cutoff 3 Λ (-2) :=
  (WeightCentreBlocks.extension D Sc cutoff 3 Λ δ).obj R
private theorem absent : ¬ ∃ β, blockSucc D Λ () h₁ β = δ := by
  intro h
  have hi := (exists_blockSucc_iff D Λ () h₁ δ).mp h
  simp [δ] at hi

-- Both finite rows of the absent unit window are retained by the chosen inverse.
example (j : Fin (-D.h () (-2 : ℤ)).toNat) :=
  elvChosenAbsentUnitWindow_coordinates D Sc cutoff 3 Λ cutoff_match () h₁ h₂ M δ
    absent (by decide) j.val j.isLt
example (j : Fin (CyclotomicCrossingTensor.contentUnitCount D cutoff () δ.1)) :=
  contentAbsentUnitTargetInverse_window D Sc cutoff 3 δ.1
    (blockSucc D Λ () h₂ δ).1 () (elvBlockSucc_content_eq D () Λ h₂ δ) (M δ)
    (elvContentAbsentUnitInverseAtWeight D Sc cutoff 3 Λ () h₁ h₂ M δ absent)
    (by decide) j.val j.isLt
example : CyclotomicCrossingTensor.contentUnitCount D cutoff () δ.1 = 2 := by decide

private def strand : TruncatedCategory D Sc cutoff 3 := ⟨[()]⟩
private theorem strand_identity_ne_zero : (𝟙 strand : strand ⟶ strand) ≠ 0 := by
  have hz := truncatedSingle_delta_ne_zero D Sc rfl
  intro h
  apply hz
  calc
    _ = (𝟙 strand) ≫ truncatedSingle D Sc cutoff 3 () (SKM.SYM.delta D ℚ ⟨(),rfl⟩) 0 :=
      (Category.id_comp _).symm
    _ = 0 := by rw [h, Limits.zero_comp]
private theorem vacuum_identity_ne_zero : (𝟙 v : v ⟶ v) ≠ 0 := by
  intro h
  apply strand_identity_ne_zero
  have hv : (𝟙 v.obj : v.obj ⟶ v.obj) = 0 := h
  have he := congrArg (fun f : v.obj ⟶ v.obj => (truncatedAppend D Sc cutoff 3 [()]).map f) hv
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero] at he
  exact he
private def chart := moduleIsoLinearEquiv
  (eqToIso (WeightCentreBlocks.extension_obj D Sc cutoff 3 Λ δ R)) v
private def occupied : (M δ).obj v := chart.symm (𝟙 v)
private theorem occupied_ne_zero : occupied ≠ 0 := by
  intro h
  apply vacuum_identity_ne_zero
  have he := congrArg chart h
  simpa only [occupied, LinearEquiv.apply_symm_apply, map_zero] using he

-- The absent diagonal unit boundary is identity, so this branch cannot be discarded.
private theorem diagonal_boundary :
    ReservoirBoundaries.negative D Sc cutoff 3 Λ cutoff_match () h₁ h₂ (by decide) 0 0 =
      𝟙 (Superfunctor.id ℚ (ELVWeightProduct D Sc cutoff 3 Λ (-2))) :=
  ((elvRouquierFamily D Sc cutoff 3 Λ cutoff_match).loc () h₁ h₂).boundaryNeg_eq
    (by decide) 0 0 (by decide) (by decide)
example : occupied ≠ 0 := occupied_ne_zero
example :
    (((ReservoirBoundaries.negative D Sc cutoff 3 Λ cutoff_match () h₁ h₂ (by decide) 0 0).total M δ).total v)
      occupied ≠ 0 := by
  rw [diagonal_boundary]
  simpa only [identity_total, CategoryTheory.Pi.id_apply, SVec.id_apply] using occupied_ne_zero
private def sy : SKM.Symmetrizer D where
  d := fun _ => 1
  pos := fun _ => by decide
  symm := fun _ _ => rfl
private theorem hc : Sc.Homogeneous := fun _ _ _ _ _ _ _ _ h => absurd rfl h
-- Every absent finite unit slot and every ordinary row, including rows beyond the window.
example (j : Fin (-D.h () (-2 : ℤ)).toNat) (r : ℕ) :=
  ReservoirBoundaries.negativeCoefficient_mem_degree D Sc cutoff 3 Λ cutoff_match () h₁ h₂
    δ sy hc (by decide) r j.val j.isLt
example (j : Fin (-D.h () (-2 : ℤ)).toNat) (r : ℕ) :=
  ReservoirBoundaries.negative_represented_coordinates D Sc cutoff 3 Λ cutoff_match () h₁ h₂
    M δ (by decide) (2 + r) j.val j.isLt v occupied

private abbrev C := contentModuleTarget D Sc cutoff 3 δ.1
private abbrev W := elvWeightSpace D Sc cutoff 3 Λ (-2)
example (j : Fin 2) (r : ℕ) := ReservoirBoundaries.negativeContent_mem_coeffGrading
  D Sc cutoff 3 Λ cutoff_match () h₁ h₂ δ sy hc (by decide) j.val (2+r) j.isLt
example (j : Fin 2) (r : ℕ) (a b : (𝟙 C) ⟶ (𝟙 C)) :=
  ReservoirBoundaries.negativeContent_sandwich_mem D Sc cutoff 3 Λ cutoff_match () h₁ h₂
    δ sy hc C (by decide) j.val (2+r) j.isLt (by omega) a b
example (j : Fin 2) (r : ℕ) (a b : (𝟙 W) ⟶ (𝟙 W)) :=
  ReservoirBoundaries.negativeAction_evaluate_mem D Sc cutoff 3 Λ cutoff_match () h₁ h₂
    δ sy hc W (by decide) j.val (2+r) j.isLt (by omega) a b
example (j : Fin 2) (r : ℕ) (a b : (𝟙 W) ⟶ (𝟙 W)) :=
  ReservoirBoundaries.negativeNativeBoundary_evaluate_mem D Sc cutoff 3 Λ cutoff_match () h₁ h₂
    δ sy hc (fun _ => W) (Finsupp.single () 1) 0
    (by decide) j.val (2+r) j.isLt (by omega) a b

end NonVacuity.ELVReservoirBoundaryIdeal.Absent

namespace NonVacuity.ELVReservoirBoundaryIdeal.Supported
private def D : SKM.Datum Bool (Bool → ℤ) := WeightedAppendFixture.datum
private def Sc : SKM.Scalars D ℚ := WeightedAppendFixture.scalars
private abbrev cut : Bool → ℕ := fun _ => 4
private def Λ : Bool → ℤ := fun _ => 4
private def w (v : List Bool) : Bool → ℤ := (v.map D.α).sum - Λ
private def base (v : List Bool) : WeightBlocks D Λ (w v) := ⟨v, rfl⟩
private theorem cutoff (i : Bool) : (cut i : ℤ) = D.h i Λ := rfl
private def M (v : List Bool) (i : Bool) : ELVWeightProduct D Sc cut 8 Λ (w v + D.α i) := fun δ =>
  supermoduleParityObj ((BalancedInduction.restriction (contentInclusion D Sc cut 8 δ.1)).obj
    (WeightedAppendFixture.truncatedRepresentable D Sc cut 8
      ((oldTruncateFunctor D Sc cut 8).obj ⟨v ++ [i]⟩)))
private theorem negative (i : Bool) : D.h i (w [] + D.α i) ≤ 0 := by
  cases i <;> norm_num [w, Λ, D, WeightedAppendFixture.datum,
    AsymmetricParameters.datum, SKM.Datum.h, SKM.Datum.α]
private theorem positive (i : Bool) : 0 ≤ D.h i (w [i,i] + D.α i) := by
  cases i <;> norm_num [w, Λ, D, WeightedAppendFixture.datum,
    AsymmetricParameters.datum, SKM.Datum.h, SKM.Datum.α]
private def sy : SKM.Symmetrizer D where
  d := AsymmetricParameters.symmetrizer.d
  pos := AsymmetricParameters.symmetrizer.pos
  symm := AsymmetricParameters.symmetrizer.symm
private theorem hc : Sc.Homogeneous := fun _ _ _ _ _ _ _ _ h => absurd rfl h
private def t (v : List Bool) (i : Bool) :
    ContentCategory D Sc cut 8 (blockSucc D Λ i rfl (base v)).1 := ⟨⟨i :: v⟩, rfl⟩
example (i : Bool) (j : Fin (D.h i (w [i,i] + D.α i)).toNat) (r : ℕ) :=
  ReservoirBoundaries.positiveCoefficient_mem_degree D Sc cut 8 Λ cutoff i rfl rfl
    (blockSucc D Λ i rfl (base [i,i])) sy hc (positive i) j.val (2 + r) j.isLt
example (i : Bool) (j : Fin (-D.h i (w [] + D.α i)).toNat) (r : ℕ) :=
  ReservoirBoundaries.negativeCoefficient_mem_degree D Sc cut 8 Λ cutoff i rfl rfl
    (blockSucc D Λ i rfl (base [])) sy hc (negative i) (2 + r) j.val j.isLt
example (i : Bool) (j : Fin (D.h i (w [i,i] + D.α i)).toNat) (r : ℕ) :=
  ReservoirBoundaries.positive_represented_coordinates D Sc cut 8 Λ cutoff i rfl rfl
    (M [i,i] i) (base [i,i]) (positive i) j.val (2 + r) j.isLt (t [i,i] i)
example (i : Bool) (j : Fin (-D.h i (w [] + D.α i)).toNat) (r : ℕ) :=
  ReservoirBoundaries.negative_represented_coordinates D Sc cut 8 Λ cutoff i rfl rfl
    (M [] i) (blockSucc D Λ i rfl (base [])) (negative i) (2 + r) j.val j.isLt (t [] i)
example : D.parity true = 1 := by decide
example : D.parity false = 0 := by decide

private abbrev β (i : Bool) := blockSucc D Λ i rfl (base [i,i])
private abbrev C (i : Bool) := contentModuleTarget D Sc cut 8 (β i).1
private abbrev W (i : Bool) := elvWeightSpace D Sc cut 8 Λ (w [i,i] + D.α i)
example (i : Bool) (j : Fin (D.h i (w [i,i] + D.α i)).toNat) (r : ℕ) :=
  ReservoirBoundaries.positiveContent_mem_coeffGrading D Sc cut 8 Λ cutoff i rfl rfl
    (β i) sy hc (positive i) j.val (j.val+1+r) j.isLt
example (i : Bool) (j : Fin (D.h i (w [i,i] + D.α i)).toNat) (r : ℕ)
    (a b : (𝟙 (C i)) ⟶ (𝟙 (C i))) :=
  ReservoirBoundaries.positiveContent_sandwich_mem D Sc cut 8 Λ cutoff i rfl rfl
    (β i) sy hc (C i) (positive i) j.val (j.val+1+r) j.isLt (by omega) a b
example (i : Bool) (j : Fin (D.h i (w [i,i] + D.α i)).toNat) (r : ℕ)
    (a b : (𝟙 (W i)) ⟶ (𝟙 (W i))) :=
  ReservoirBoundaries.positiveAction_evaluate_mem D Sc cut 8 Λ cutoff i rfl rfl
    (β i) sy hc (W i) (positive i) j.val (j.val+1+r) j.isLt (by omega) a b
example (i : Bool) (j : Fin (D.h i (w [i,i] + D.α i)).toNat) (r : ℕ)
    (a b : (𝟙 (W i)) ⟶ (𝟙 (W i))) :=
  ReservoirBoundaries.positiveNativeBoundary_evaluate_mem D Sc cut 8 Λ cutoff i rfl rfl
    (β i) sy hc (fun _ => W i) (Finsupp.single i 1) 0
    (positive i) j.val (j.val+1+r) j.isLt (by omega) a b

end NonVacuity.ELVReservoirBoundaryIdeal.Supported

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVReservoirBoundaryIdeal
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms only"
