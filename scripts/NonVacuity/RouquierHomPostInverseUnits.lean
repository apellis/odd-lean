import OddMath.SKM.RouquierHomPostInverseUnits
import OddMath.QuiverHecke.CyclotomicAction.ProbeWeightDotInverse
import OddMath.QuiverHecke.CyclotomicAction.ProbePolynomialParity
import OddMath.QuiverHecke.CyclotomicAction.PiWeightSpaces
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightSuperAdjunction
import StringDiagrams.Super.PiTwo
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct OddMath.SKM
open OddMath.QuiverHecke OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace NonVacuity.RouquierHomPostInverseUnits

private def D : SKM.Datum Unit ℤ where
  cd :=
    { root := fun _ => 2
      coroot := fun _ => LinearMap.id
      coroot_root_self := fun _ => rfl }
  isGCM :=
    { diag := fun _ => rfl
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
  two_isUnit := fun _ => (by norm_num : (2 : ℚ) ≠ 0).isUnit



private def m : Unit → ℕ := fun _ => 3
private def a : Unit → Polynomial ℚ := probePolynomial (probeDotExponent D) m
private theorem ha : CyclotomicPolynomialParity D a := probePolynomial_parity D m

private theorem h : (6 : ℤ) + D.α () = 8 := by decide


private def A : PiSCat.{0, 0, 1} ℚ where
  toSCat := globalWeightSpace D Sc a ha 6 6
  pi := globalWeightSpacePi D Sc a ha 6 6
private def B : PiSCat.{0, 0, 1} ℚ where
  toSCat := globalWeightSpace D Sc a ha 6 8
  pi := globalWeightSpacePi D Sc a ha 6 8
private abbrev E : A ⟶ B := globalActionE D Sc a ha () 6 h
private abbrev x : End E := globalActionDot D Sc a ha () 6 h
private abbrev R : B ⟶ B := 𝟙 B
private abbrev H : B ⟶ B := 𝟙 B
private def adj : SuperAdjunction (k := ℚ) R R :=
  ordinaryEvenSuperAdjunction R R Adjunction.id (fun M => id_mem M) (fun M => id_mem M)

local instance homPi {C D : PiSCat.{0, 0, 1} ℚ} : PiSupercategory ℚ (C ⟶ D) :=
  PiTwoSupercategory.homPiLeft C D

private abbrev Y := (homParityShift (k := ℚ) 1).obj H ≫ R
private abbrev S := E ≫ Y
private abbrev JSource := (homParityShift (k := ℚ) 1).obj (S ≫ R)
private abbrev J := homMixedInterchange (k := ℚ) E R 1 1 Y

private theorem source_zero :
    mixedPostSourcePostDot (k := ℚ) E 1 H adj (0 : R ⟶ R) = 0 := by
  have hz : SuperAdjunction.rightTranspose adj adj (0 : R ⟶ R) = 0 :=
    (SuperAdjunction.rightTransposeLinear adj adj).map_zero
  rw [mixedPostSourcePostDot, hz, whiskerLeft_zero', whiskerLeft_zero']

private theorem j_zero :
    mixedPostJPostDot (k := ℚ) E 1 1 H (F' := R) (0 : R ⟶ R) = 0 := by
  simp only [mixedPostJPostDot, whiskerLeft_zero', Functor.map_zero]

/-- A concrete odd cyclotomic probe, original integer weight, and nontrivial
parity shifts supply every norm unit of the odd categorical inverse criterion. -/
example : ∃ α : End JSource, IsIso (homDistinctMixedMateDot E adj 1 1 H
    (J.hom ≫ (-(α ≫ α ≫ J.inv)))) := by
  have hx : x ∈ parity (R := ℚ) _ _ 1 := globalActionDot_mem D Sc a ha () 6 h
  have hu : IsUnit x := probeGlobalActionDot_isUnit D Sc m ha () 6 h
  have huS : IsUnit (mixedPostSourcePreDot (k := ℚ) E 1 H (F' := R) x) :=
    hu.map ((homPost (k := ℚ) Y).mapEnd E)
  have huJ : IsUnit (mixedPostJPreDot (k := ℚ) E 1 1 H (E' := R) (F' := R) x) :=
    ((hu.map ((homPost (k := ℚ) Y).mapEnd E)).map
      ((homPost (k := ℚ) R).mapEnd S)).map
      ((homParityShift (k := ℚ) 1).mapEnd (S ≫ R))
  obtain ⟨u, huj⟩ := huJ
  refine ⟨(↑u⁻¹ : End JSource), ?_⟩
  apply homDistinctMixedMateDot_isIso_of_inverse_odd_units E adj 1 1 H hx (zero_mem _)
  · rw [j_zero, zero_pow two_ne_zero, sub_zero]
    exact (show IsUnit (mixedPostJPreDot (k := ℚ) E 1 1 H (E' := R) (F' := R) x) from
      ⟨u, huj⟩).pow 2
  · rw [source_zero, zero_pow two_ne_zero, sub_zero]
    exact huS.pow 2
  · rw [source_zero, zero_pow two_ne_zero, add_zero]
    exact huS.pow 2
  · rw [j_zero, Limits.zero_comp, sub_zero, sub_zero]
    change (↑u⁻¹ : End JSource) *
      (mixedPostJPreDot (k := ℚ) E 1 1 H (E' := R) (F' := R) x *
        mixedPostJPreDot (k := ℚ) E 1 1 H (E' := R) (F' := R) x) =
      mixedPostJPreDot (k := ℚ) E 1 1 H (E' := R) (F' := R) x
    rw [← huj, ← mul_assoc, Units.inv_mul, one_mul]

private theorem j_identity :
    mixedPostJPreDot (k := ℚ) E 1 1 H (E' := R) (F' := R) (𝟙 E) =
      (1 : End JSource) := by
  simp only [mixedPostJPreDot, TwoSupercategory.id_whiskerRight (R := ℚ), Functor.map_id]

/-- The even inverse identities on the same nonzero category also need no
whole-fibre reservoir nilpotence. -/
example : IsIso (homDistinctMixedMateDot E adj 1 1 H
    (J.hom ≫ (-((-1 : End JSource) ≫ -1 ≫ J.inv)))) := by
  apply homDistinctMixedMateDot_isIso_of_inverse_units E adj 1 1 H
    (id_mem E) (zero_mem _) (-1 : End JSource)
  · simp [j_zero, j_identity, ← End.mul_def]
  · simp [j_zero, j_identity, ← End.mul_def]
  · rw [source_zero, sub_zero]
    exact (isUnit_one : IsUnit (1 : End E)).map ((homPost (k := ℚ) Y).mapEnd E)

end NonVacuity.RouquierHomPostInverseUnits

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := `OddMath.SKM.RouquierHomPostInverseUnits
  let some idx := env.header.moduleNames.idxOf? owner
    | throwError "Module was not imported: {owner}"
  let names := env.header.moduleData[idx]!.constNames
  unless names.size > 0 do throwError "Empty owned declaration inventory"
  for name in names do
    for ax in ← Lean.collectAxioms name do
      unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
        throwError "Disallowed axiom {ax} in {name}"
  logInfo m!"Audited ALL {names.size} owned declarations, including private/generated"
