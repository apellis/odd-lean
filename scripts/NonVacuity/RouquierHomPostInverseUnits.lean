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

local instance homPi {A B : PiSCat.{0, 0, 1} ℚ} : PiSupercategory ℚ (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

private def identityAdj (B : PiSCat.{0, 0, 1} ℚ) :
    SuperAdjunction (k := ℚ) (𝟙 B) (𝟙 B) :=
  ordinaryEvenSuperAdjunction (𝟙 B) (𝟙 B) Adjunction.id
    (fun M => id_mem M) (fun M => id_mem M)

private abbrev middle (B : PiSCat.{0, 0, 1} ℚ) :=
  (homParityShift (k := ℚ) (C := B ⟶ B) 1).obj (𝟙 B) ≫ 𝟙 B

private abbrev jSource {A B : PiSCat.{0, 0, 1} ℚ} (E : A ⟶ B) :=
  (homParityShift (k := ℚ) (C := A ⟶ B) 1).obj ((E ≫ middle B) ≫ 𝟙 B)

private abbrev interchange {A B : PiSCat.{0, 0, 1} ℚ} (E : A ⟶ B) :=
  homMixedInterchange (k := ℚ) E (𝟙 B) 1 1 (middle B)

private abbrev InverseWitness {A B : PiSCat.{0, 0, 1} ℚ} (E : A ⟶ B) (x : End E) : Prop :=
  ∃ α : End (jSource E),
    α * mixedPostJPreDot (k := ℚ) E 1 1 (𝟙 B) (E' := 𝟙 B) (F' := 𝟙 B) x = 1 ∧
      IsIso (homDistinctMixedMateDot E (identityAdj B) 1 1 (𝟙 B)
        ((interchange E).hom ≫ (-(α ≫ α ≫ (interchange E).inv))))

private theorem source_zero {A B : PiSCat.{0, 0, 1} ℚ} (E : A ⟶ B) :
    mixedPostSourcePostDot (k := ℚ) E 1 (𝟙 B) (identityAdj B) (0 : End (𝟙 B)) = 0 := by
  have hz : SuperAdjunction.rightTranspose (identityAdj B) (identityAdj B)
      (0 : End (𝟙 B)) = 0 := (SuperAdjunction.rightTransposeLinear _ _).map_zero
  rw [mixedPostSourcePostDot, hz, whiskerLeft_zero' (k := ℚ), whiskerLeft_zero' (k := ℚ)]

private theorem j_zero {A B : PiSCat.{0, 0, 1} ℚ} (E : A ⟶ B) :
    mixedPostJPostDot (k := ℚ) E 1 1 (𝟙 B) (F' := 𝟙 B) (0 : End (𝟙 B)) = 0 := by
  rw [mixedPostJPostDot, whiskerLeft_zero' (k := ℚ)]
  exact (homParityShift (k := ℚ) (C := A ⟶ B) 1).map_zero _ _

private theorem j_identity {A B : PiSCat.{0, 0, 1} ℚ} (E : A ⟶ B) :
    mixedPostJPreDot (k := ℚ) E 1 1 (𝟙 B) (E' := 𝟙 B) (F' := 𝟙 B) (𝟙 E) =
      (1 : End (jSource E)) := by
  rw [mixedPostJPreDot, TwoSupercategory.id_whiskerRight (R := ℚ),
    TwoSupercategory.id_whiskerRight (R := ℚ)]
  exact (homParityShift (k := ℚ) (C := A ⟶ B) 1).map_id _

private theorem oddWitness {A B : PiSCat.{0, 0, 1} ℚ} (E : A ⟶ B) (x : End E)
    (hx : x ∈ parity (R := ℚ) _ _ 1) (hu : IsUnit x) : InverseWitness E x := by
  have huS : IsUnit (mixedPostSourcePreDot (k := ℚ) E 1 (𝟙 B) (F' := 𝟙 B) x) :=
    hu.map ((homPost (k := ℚ) (middle B)).mapEnd E)
  have huJ : IsUnit (mixedPostJPreDot (k := ℚ) E 1 1 (𝟙 B) (E' := 𝟙 B) (F' := 𝟙 B) x) :=
    ((hu.map ((homPost (k := ℚ) (middle B)).mapEnd E)).map
      ((homPost (k := ℚ) (𝟙 B)).mapEnd (E ≫ middle B))).map
      ((homParityShift (k := ℚ) (C := A ⟶ B) 1).mapEnd ((E ≫ middle B) ≫ 𝟙 B))
  obtain ⟨u, huj⟩ := huJ
  refine ⟨(↑u⁻¹ : End (jSource E)), ?_, ?_⟩
  · rw [← huj]
    exact Units.inv_mul u
  · apply homDistinctMixedMateDot_isIso_of_inverse_odd_units E (identityAdj B) 1 1 (𝟙 B)
      hx (zero_mem _)
    · rw [j_zero, zero_pow two_ne_zero, sub_zero]
      exact (show IsUnit (mixedPostJPreDot (k := ℚ) E 1 1 (𝟙 B)
        (E' := 𝟙 B) (F' := 𝟙 B) x) from ⟨u, huj⟩).pow 2
    · rw [source_zero, zero_pow two_ne_zero, sub_zero]
      exact huS.pow 2
    · rw [source_zero, zero_pow two_ne_zero, add_zero]
      exact huS.pow 2
    · rw [j_zero, Limits.zero_comp, sub_zero, sub_zero]
      change (↑u⁻¹ : End (jSource E)) *
        (mixedPostJPreDot (k := ℚ) E 1 1 (𝟙 B) (E' := 𝟙 B) (F' := 𝟙 B) x *
          mixedPostJPreDot (k := ℚ) E 1 1 (𝟙 B) (E' := 𝟙 B) (F' := 𝟙 B) x) =
        mixedPostJPreDot (k := ℚ) E 1 1 (𝟙 B) (E' := 𝟙 B) (F' := 𝟙 B) x
      rw [← huj, ← mul_assoc, Units.inv_mul, one_mul]

private theorem evenIdentity {A B : PiSCat.{0, 0, 1} ℚ} (E : A ⟶ B) :
    IsIso (homDistinctMixedMateDot E (identityAdj B) 1 1 (𝟙 B)
      ((interchange E).hom ≫ (-((-1 : End (jSource E)) ≫
        (-1 : End (jSource E)) ≫ (interchange E).inv)))) := by
  apply homDistinctMixedMateDot_isIso_of_inverse_units E (identityAdj B) 1 1 (𝟙 B)
    (id_mem E) (zero_mem _) (-1 : End (jSource E))
  · rw [j_zero, j_identity]
    change (-1 : End (jSource E)) * (-1) = 1
    simp
  · rw [j_zero, j_identity]
    change (-1 : End (jSource E)) * (-1) = 1
    simp
  · rw [source_zero, sub_zero]
    exact (isUnit_one : IsUnit (1 : End E)).map ((homPost (k := ℚ) (middle B)).mapEnd E)

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

/-- The coefficient is an actual inverse of the transported odd probe dot,
on the original integer weight spaces with both shifts nontrivial. -/
example : InverseWitness E x :=
  oddWitness E x (globalActionDot_mem D Sc a ha () 6 h)
    (probeGlobalActionDot_isUnit D Sc m ha () 6 h)

example : IsIso (homDistinctMixedMateDot E (identityAdj B) 1 1 (𝟙 B)
    ((interchange E).hom ≫ (-((-1 : End (jSource E)) ≫
      (-1 : End (jSource E)) ≫ (interchange E).inv)))) := evenIdentity E

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
