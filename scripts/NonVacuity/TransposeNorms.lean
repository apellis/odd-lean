import OddMath.QuiverHecke.SwappedAssembly.Sigma.TransposeNorms
import OddMath.QuiverHecke.CyclotomicAction.ProbeWeightDotInverse
import OddMath.QuiverHecke.CyclotomicAction.ProbePolynomialParity
import OddMath.QuiverHecke.CyclotomicAction.PiWeightSpaces
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightSuperAdjunction
import StringDiagrams.Super.PiTwo
import Lean.Util.CollectAxioms

noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct OddMath OddMath.SKM
open OddMath.QuiverHecke OddMath.QuiverHecke.CyclotomicAction OddMath.QuiverHecke.ELVOld
namespace NonVacuity.TransposeNorms

local instance homPi {A B : PiSCat.{0, 0, 1} ℚ} : PiSupercategory ℚ (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B

private def identityAdj (B : PiSCat.{0, 0, 1} ℚ) :
    SuperAdjunction (k := ℚ) (𝟙 B) (𝟙 B) :=
  ordinaryEvenSuperAdjunction (𝟙 B) (𝟙 B) Adjunction.id
    (fun M => id_mem M) (fun M => id_mem M)

private abbrev SourceNorms {A B : PiSCat.{0, 0, 1} ℚ} (E : A ⟶ B) (x : End E) : Prop :=
  IsUnit (mixedPostSourcePreDot (k := ℚ) E 1 (𝟙 B) (F' := 𝟙 B) x) ∧
    IsNilpotent (mixedPostSourcePostDot (k := ℚ) E 1 (𝟙 B) (identityAdj B) (0 : End (𝟙 B))) ∧
    IsUnit (mixedPostSourcePreDot (k := ℚ) E 1 (𝟙 B) (F' := 𝟙 B) x ^ 2 -
      mixedPostSourcePostDot (k := ℚ) E 1 (𝟙 B) (identityAdj B) (0 : End (𝟙 B)) ^ 2) ∧
    IsUnit (mixedPostSourcePreDot (k := ℚ) E 1 (𝟙 B) (F' := 𝟙 B) x ^ 2 +
      mixedPostSourcePostDot (k := ℚ) E 1 (𝟙 B) (identityAdj B) (0 : End (𝟙 B)) ^ 2)

private theorem oddNorms {A B : PiSCat.{0, 0, 1} ℚ} (E : A ⟶ B) (x : End E)
    (hx : x ∈ parity (R := ℚ) _ _ 1) (hu : IsUnit x) : SourceNorms E x := by
  have hz : IsNilpotent (0 : End (𝟙 B)) := ⟨1, by simp⟩
  have hh := mixedPostSource_square_norms_isUnit_of_nilpotent E (identityAdj B) 1 (𝟙 B)
    hx (zero_mem _) hu hz
  exact ⟨mixedPostSourcePreDot_isUnit (k := ℚ) E 1 (𝟙 B) hu,
    mixedPostSourcePostDot_isNilpotent E (identityAdj B) 1 (𝟙 B)
      (zero_mem (parity (R := ℚ) (𝟙 B) (𝟙 B) 1)) hz, hh.1, hh.2⟩

private theorem evenNorm {A B : PiSCat.{0, 0, 1} ℚ} (E : A ⟶ B) :
    IsUnit (mixedPostSourcePreDot (k := ℚ) E 1 (𝟙 B) (F' := 𝟙 B) (1 : End E) -
      mixedPostSourcePostDot (k := ℚ) E 1 (𝟙 B) (identityAdj B) (0 : End (𝟙 B))) :=
  mixedPostSource_difference_isUnit_of_nilpotent E (identityAdj B) 1 (𝟙 B)
    (id_mem E) (zero_mem (parity (R := ℚ) (𝟙 B) (𝟙 B) 0))
    isUnit_one (show IsNilpotent (0 : End (𝟙 B)) from ⟨1, by simp⟩)

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


/-- The odd probe uses the actual inverse producer at the original integer weight. -/
example : SourceNorms E x :=
  oddNorms E x (globalActionDot_mem D Sc a ha () 6 h)
    (probeGlobalActionDot_isUnit D Sc m ha () 6 h)

example : IsUnit (mixedPostSourcePreDot (k := ℚ) E 1 (𝟙 B) (F' := 𝟙 B) (1 : End E) -
    mixedPostSourcePostDot (k := ℚ) E 1 (𝟙 B) (identityAdj B) (0 : End (𝟙 B))) :=
  evenNorm E

end NonVacuity.TransposeNorms

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for owner in #[`OddMath.QuiverHecke.SwappedAssembly.Sigma.TransposeNorms] do
    let some idx := env.header.moduleNames.idxOf? owner
      | throwError "Module was not imported: {owner}"
    let names := env.header.moduleData[idx]!.constNames
    unless names.size > 0 do throwError "Empty owned declaration inventory: {owner}"
    for name in names do
      for ax in ← Lean.collectAxioms name do
        unless #[`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
    logInfo m!"Audited ALL {names.size} declarations in {owner}, including private/generated"
