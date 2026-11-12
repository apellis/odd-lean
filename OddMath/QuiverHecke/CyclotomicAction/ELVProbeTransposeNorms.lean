import OddMath.QuiverHecke.CyclotomicAction.ELVProbeDenominatorUnits
import OddMath.QuiverHecke.CyclotomicAction.ELVMixedSourceOddNorms
import OddMath.QuiverHecke.SwappedAssembly.Sigma.SwappingReservoir
import OddMath.QuiverHecke.CyclotomicAction.ParameterTwistPureNilpotent

/-! # Transposed source norms and swapping for the ELV probe pair

SwappedActionAssembly F2–F3 and SwappedHomInversion §2: package the three
literal source norm units for the prescribed OLD probe and ELV reservoir.
Their inverses were assembled at individual content blocks; no common
nilpotence exponent on a weight fibre is assumed. The existing swapping
mate theorem then applies to the chosen mixed crossing coefficient.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke
open ELVOld CyclotomicAction SwappedAssembly
universe u
local instance probeTransposeHomPi {k : Type u} [CommRing k]
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

/-- All three transposed source norms are units for the specified factor pair. -/
theorem ELVProbeCrossTransposeNormUnits [Fact Sc.PureNilpotent] [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc' cutoff bound) : (P).CrossTransposeNormUnits := by
  let : Fintype I := Fintype.ofFinite I
  constructor
  · intro i hi xP yP xW yW hp hw κ
    have hu := elvProbeReservoir_dot_isUnit D Sc m cutoff bound ΛP ΛR hP hR i hp
    generalize hT : (P).T = T at hu ⊢
    set_option backward.dsimp.instances true in
      dsimp only [elvProbeReservoir, elvRouquierFamily, elvRouquierData]
    intro H
    have hh := elvMixedSource_difference_isUnit (A := T.obj xP) (B := T.obj yP)
      D Sc' cutoff bound i ΛR hw (T.E i hp) κ H
      hdot hi (T.dot i hp)
      (hi ▸ T.dot_mem i hp) hu
    exact hh
  · intro i hi xP yP xW yW hp hw κ
    have hu := elvProbeReservoir_dot_isUnit D Sc m cutoff bound ΛP ΛR hP hR i hp
    generalize hT : (P).T = T at hu ⊢
    set_option backward.dsimp.instances true in
      dsimp only [elvProbeReservoir, elvRouquierFamily, elvRouquierData]
    intro H
    have hh := elvMixedSource_square_difference_isUnit (A := T.obj xP) (B := T.obj yP)
      D Sc' cutoff bound ΛR xW i hw (T.E i hp) κ H
      hdot hi (T.dot i hp)
      (hi ▸ T.dot_mem i hp) hu
    exact hh
  · intro i hi xP yP xW yW hp hw κ
    have hu := elvProbeReservoir_dot_isUnit D Sc m cutoff bound ΛP ΛR hP hR i hp
    generalize hT : (P).T = T at hu ⊢
    set_option backward.dsimp.instances true in
      dsimp only [elvProbeReservoir, elvRouquierFamily, elvRouquierData]
    intro H
    have hh := elvMixedSource_square_sum_isUnit (A := T.obj xP) (B := T.obj yP)
      D Sc' cutoff bound ΛR xW i hw (T.E i hp) κ H
      hdot hi (T.dot i hp)
      (hi ▸ T.dot_mem i hp) hu
    exact hh

/-- Every off-central swapping entry of the chosen mixed coefficient is invertible. -/
theorem elvProbeSwappingInvertible [Fact Sc.PureNilpotent] [Finite I]
    (hdot : TruncatedAppendDotNilpotent D Sc' cutoff bound) :
    (P).SwappingInvertible (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR
    hdot) :=
  (P).swappingInvertible_of_units
    (elvProbeCrossCoeffOf D Sc m cutoff bound ΛP ΛR hP hR
    hdot)
    (elvProbeCrossCoeffOf_isInverse D Sc m cutoff bound ΛP ΛR hP hR
    hdot)
    (elvProbeCrossDenominatorUnitsOf D Sc m cutoff bound ΛP ΛR hP hR hdot)
    (ELVProbeCrossTransposeNormUnits D Sc m cutoff bound ΛP ΛR hP hR hdot)

end OddMath.QuiverHecke
