import NonVacuity.ELVWeightedAppendFixture
import OddMath.QuiverHecke.CyclotomicAction.ELVReservoirClosureDegree
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightCentreBlocks
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedDetection
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
open OddMath OddMath.QuiverHecke ELVOld
open OddMath.QuiverHecke.CyclotomicAction
namespace NonVacuity.ELVReservoirClosureDegree
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
private theorem h₁ : (-2 : ℤ) + D.α () = 0 := by decide
private theorem h₂ : (0 : ℤ) + D.α () = 2 := by decide
private def β : WeightBlocks D Λ 0 := ⟨[()],by decide⟩
private def v : ContentCategory D Sc cutoff 3 β.1 := ⟨⟨[()]⟩,rfl⟩
private def R := contentRepresentable D Sc cutoff 3 β.1 v
private def M : ELVWeightProduct D Sc cutoff 3 Λ 0 := (WeightCentreBlocks.extension D Sc cutoff 3 Λ β).obj R
private def z : R.obj v := truncatedSingle D Sc cutoff 3 () (SKM.SYM.delta D ℚ ⟨(),rfl⟩) 0
private theorem z_ne_zero : z ≠ 0 := truncatedSingle_delta_ne_zero D Sc rfl
private theorem identity_ne_zero : (𝟙 v : v ⟶ v) ≠ 0 := by
  intro h
  have hz := congrArg (fun f : v ⟶ v => f ≫ z) h
  rw [Category.id_comp, Limits.zero_comp] at hz
  exact z_ne_zero hz
private def chart := moduleIsoLinearEquiv (eqToIso (WeightCentreBlocks.extension_obj D Sc cutoff 3 Λ β R)) v
private def occupied : (M β).obj v := chart.symm z
private theorem occupied_ne_zero : occupied ≠ 0 := by
  intro h
  apply z_ne_zero
  have hh := congrArg chart h
  simpa only [occupied,LinearEquiv.apply_symm_apply,map_zero] using hh

private def β₀ : WeightBlocks D Λ (-2) := ⟨0,by decide⟩

-- Both literal chosen principal orientations at a supported, occupied odd block.
example (F : ELVWeightProduct D Sc cutoff 3 Λ 0) :=
  ReservoirClosures.positive_content_coordinates D Sc cutoff 3 Λ cutoff_match () h₁ h₂ F β₀ (by decide) 2 3
example (F : ELVWeightProduct D Sc cutoff 3 Λ 0) :=
  ReservoirClosures.negative_content_coordinates D Sc cutoff 3 Λ cutoff_match () h₁ h₂ F β₀ (by decide) 2 3
example := ReservoirClosures.positive_content_coordinates D Sc cutoff 3 Λ cutoff_match () h₁ h₂ M β₀ (by decide) 2 3
example := ReservoirClosures.negative_content_coordinates D Sc cutoff 3 Λ cutoff_match () h₁ h₂ M β₀ (by decide) 2 3
example : occupied ≠ 0 := occupied_ne_zero
example : (𝟙 v : v ⟶ v) ≠ 0 := identity_ne_zero

private def sy : SKM.Symmetrizer D where
  d := fun _ => 1
  pos := fun _ => by decide
  symm := fun _ _ => rfl
private theorem hc : Sc.Homogeneous := fun _ _ _ _ _ _ _ _ h => absurd rfl h
example (r s : ℕ) := ReservoirClosures.positive_weighted_coordinates D Sc cutoff 3 Λ cutoff_match
  () h₁ h₂ M β₀ (by decide) r s
example (r s : ℕ) := ReservoirClosures.negative_weighted_coordinates D Sc cutoff 3 Λ cutoff_match
  () h₁ h₂ M β₀ (by decide) r s
example (r s : ℕ) := ReservoirClosures.positiveRepresentedValue_degree D Sc cutoff 3 Λ cutoff_match
  () β sy hc (by decide) r s v
example (r s : ℕ) := ReservoirClosures.negativeRepresentedValue_degree D Sc cutoff 3 Λ cutoff_match
  () β sy hc (by decide) r s v

example (r s : ℕ) := ReservoirClosures.positiveContent_represented_coordinates
  D Sc cutoff 3 Λ cutoff_match () h₁ h₂ β₀ (by decide) r s R v z
example (r s : ℕ) := ReservoirClosures.negativeContent_represented_coordinates
  D Sc cutoff 3 Λ cutoff_match () h₁ h₂ β₀ (by decide) r s R v z
example (r s : ℕ) := ReservoirClosures.positiveCoefficient_mem_degree
  D Sc cutoff 3 Λ cutoff_match () h₁ h₂ β sy hc (by decide) r s
example (r s : ℕ) := ReservoirClosures.negativeCoefficient_mem_degree
  D Sc cutoff 3 Λ cutoff_match () h₁ h₂ β sy hc (by decide) r s

end NonVacuity.ELVReservoirClosureDegree

namespace NonVacuity.ELVReservoirClosureDegree.SignedHeights
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
private theorem middle (i : Bool) : D.h i (w [i] + D.α i) = 0 := by
  cases i <;> norm_num [w, Λ, D, WeightedAppendFixture.datum,
    AsymmetricParameters.datum, SKM.Datum.h, SKM.Datum.α]
example (i : Bool) := ReservoirClosures.positive_content_coordinates D Sc cut 8 Λ cutoff i rfl rfl
  (M [i,i] i) (base [i,i]) (positive i) 2 3
example (i : Bool) := ReservoirClosures.negative_content_coordinates D Sc cut 8 Λ cutoff i rfl rfl
  (M [] i) (base []) (negative i) 2 3
example (i : Bool) := ReservoirClosures.positive_content_coordinates D Sc cut 8 Λ cutoff i rfl rfl
  (M [i] i) (base [i]) (le_of_eq (middle i).symm) 2 3
example (i : Bool) := ReservoirClosures.negative_content_coordinates D Sc cut 8 Λ cutoff i rfl rfl
  (M [i] i) (base [i]) (le_of_eq (middle i)) 2 3
private def sy : SKM.Symmetrizer D where
  d := AsymmetricParameters.symmetrizer.d
  pos := AsymmetricParameters.symmetrizer.pos
  symm := AsymmetricParameters.symmetrizer.symm
private theorem hc : Sc.Homogeneous := fun _ _ _ _ _ _ _ _ h => absurd rfl h
private def t (v : List Bool) (i : Bool) :
    ContentCategory D Sc cut 8 (blockSucc D Λ i rfl (base v)).1 := ⟨⟨i :: v⟩, rfl⟩
example (i : Bool) (r s : ℕ) := ReservoirClosures.positiveRepresentedValue_degree D Sc cut 8 Λ cutoff
  i (blockSucc D Λ i rfl (base [i,i])) sy hc (positive i) r s (t [i,i] i)
example (i : Bool) (r s : ℕ) := ReservoirClosures.negativeRepresentedValue_degree D Sc cut 8 Λ cutoff
  i (blockSucc D Λ i rfl (base [])) sy hc (negative i) r s (t [] i)

example (i : Bool) (r s : ℕ) := ReservoirClosures.positiveCoefficient_mem_degree D Sc cut 8 Λ cutoff
  i rfl rfl (blockSucc D Λ i rfl (base [i,i])) sy hc (positive i) r s
example (i : Bool) (r s : ℕ) := ReservoirClosures.negativeCoefficient_mem_degree D Sc cut 8 Λ cutoff
  i rfl rfl (blockSucc D Λ i rfl (base [])) sy hc (negative i) r s

private def vacuum : WeightBlocks D (0 : Bool → ℤ) (0 : Bool → ℤ) := ⟨0, by decide⟩
example (i : Bool) (r s : ℕ) := ReservoirClosures.positiveCoefficient_mem_degree
  D Sc (fun _ => 0) 8 0 (fun _ => rfl) i (neg_add_cancel (D.α i)) (zero_add (D.α i))
  vacuum sy hc (by cases i <;> decide) r s
example (i : Bool) (r s : ℕ) := ReservoirClosures.negativeCoefficient_mem_degree
  D Sc (fun _ => 0) 8 0 (fun _ => rfl) i (neg_add_cancel (D.α i)) (zero_add (D.α i))
  vacuum sy hc (by cases i <;> decide) r s

end NonVacuity.ELVReservoirClosureDegree.SignedHeights

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.QuiverHecke.CyclotomicAction.ELVReservoirClosureDegree
  let some idx := env.header.moduleNames.idxOf? owner | throwError "Module not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  if names.isEmpty then throwError "No owned declarations: {owner}"
  for name in names do
    for axiomName in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains axiomName do
        throwError "Disallowed axiom {axiomName} in {name}"
  logInfo m!"Audited {names.size} owned declarations in {owner}: standard axioms only"
