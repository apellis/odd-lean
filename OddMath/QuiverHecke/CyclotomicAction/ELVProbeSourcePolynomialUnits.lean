import OddMath.QuiverHecke.CyclotomicAction.ELVProbeReservoir
import OddMath.QuiverHecke.CyclotomicAction.ELVMixedSourcePolynomialUnits
import OddMath.QuiverHecke.SwappedAssembly.Sigma.MixedEntryPureNilpotent
import OddMath.QuiverHecke.CyclotomicAction.ParameterTwistPureNilpotent

/-! # Distinct-colour source polynomial units for the ELV probe pair

BE2 (1.11), SwappedDistinctMixedMates (13)–(15): the prescribed probe dot
has an invertible even power, and the prescribed reservoir transpose has
contentwise nilpotent even powers. These construct the source polynomial
units needed by each distinct-colour sideways crossing.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction SwappedAssembly OddMath.SKM
universe u
local instance probeSourcePolynomialHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u + 1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "Sc'" => parameterTwist D Sc
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR

attribute [local irreducible] SKM.mixedPostSourcePreDot SKM.mixedPostSourcePostDot

/-- The actual whole-input source criterion for every pair of colours and
original weights; all admissible remainders and all coefficient units are retained. -/
theorem elvProbeMixedPostSourceUnits [Finite I] [Fact Sc.PureNilpotent]
    (hdot : TruncatedAppendDotNilpotent D Sc' cutoff bound) :
    ∀ (i j : I) {a b c d : X} (hT : a + D.α i = b) (hW : c + D.α j = d)
      (κ : ZMod 2) (H : (P).T.obj b ⟶ (P).W.obj d),
    SKM.MixedPostSourceUnits ((P).T.E i hT) ((P).W.adj j hW) κ H
      (SKM.rouquierPower ((P).T.dot i hT) (if D.parity i = 1 then 2 else 1))
      (SKM.rouquierPower ((P).W.dot j hW) (if D.parity j = 1 then 2 else 1)) := by
  let : Fintype I := Fintype.ofFinite I
  intro i j a b c d hT hW κ
  have hu := elvProbeReservoir_dot_isUnit D Sc m cutoff bound ΛP ΛR hP hR i hT
  generalize hTP : (P).T = T at hu ⊢
  set_option backward.dsimp.instances true in
    dsimp only [elvProbeReservoir, elvRouquierFamily, elvRouquierData]
  intro H
  have ha : SKM.rouquierPower (T.dot i hT) (if D.parity i = 1 then 2 else 1) ∈
      parity (R := k) _ _ 0 := by
    have hh := SKM.rouquierPower_mem (T.dot_mem i hT) (if D.parity i = 1 then 2 else 1)
    rwa [ProbeReservoir.mul_parity_pow_eq_zero] at hh
  have hau : IsUnit (show End (T.E i hT) from
      SKM.rouquierPower (T.dot i hT) (if D.parity i = 1 then 2 else 1)) := by
    rw [SKM.rouquierPower_eq_pow]
    exact hu.pow _
  exact elvMixedSource_polynomialUnits D Sc' cutoff bound j ΛR hW hdot (T.E i hT) κ H _ ha hau
    (if D.parity j = 1 then 2 else 1) (by split_ifs <;> decide)
    (ProbeReservoir.mul_parity_pow_eq_zero (D.parity j))

attribute [local irreducible] elvProbeReservoir ProbeReservoir.sigmaEntry

/-- All prescribed distinct-colour sideways entries are invertible from
constructed source units, without a common reservoir nilpotence exponent. -/
theorem elvProbe_distinct_sigmaEntry_isIso [Finite I] [Fact Sc.PureNilpotent]
    (hdot : TruncatedAppendDotNilpotent D Sc' cutoff bound)
    (c : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).CrossCoeff Sc)
    {i j : I} (hij : i ≠ j) (ν : X) (t : Sector I)
    (q : SPath (wd D ν [dn i, up j]) t
      (nextSector (dn i) false (nextSector (up j) true t)))
    (Z : (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).H
      (nextSector (dn i) false (nextSector (up j) true t))) :
    IsIso ((P).sigmaEntry c i j ν
      (SPath.cons _ true t trivial (SPath.cons _ false _ trivial (SPath.nil _))) q Z) :=
  (elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR).isIso_sigmaEntry_probe_reservoir_sourceUnits
    Fact.out
    (fun i j _ => elvProbeMixedPostSourceUnits D Sc m cutoff bound ΛP ΛR hP hR hdot i j)
    c hij ν t q Z

end OddMath.QuiverHecke
