import OddMath.QuiverHecke.SwappedAssembly.Sigma.OffCentralAugmentedMatrix
import OddMath.QuiverHecke.SwappedAssembly.SupportedPointwiseLeftwardInverse
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeTransposeNorms

/-! # Augmented inverse equations on every supported input

Brundan–Ellis (1.13)–(1.14): supported central augmented inverses and
the prescribed off-central swapping units cover every outer sector.
The resulting raw leftward data satisfy the local inversion identities
on supported inputs; no assertion is made on other raw Hom objects.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld
universe u
local instance supportedAugmentedInverseHomPi {k : Type u} [CommRing k]
    (A B : PiSCat.{u,u,u+1} k) : PiSupercategory k (A ⟶ B) :=
  PiTwoSupercategory.homPiLeft A B
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR
local notation "c" "[" sy "," hc "]" =>
  elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc
local notation "L" "[" sy "," hc "]" =>
  pointwiseLeftwardData D Sc m cutoff bound ΛP ΛR hP hR sy hc
attribute [local irreducible] elvProbeReservoir elvProbeCrossCoeff

/-- Both signs of the actual augmented matrix are invertible at every
outer sector of a supported, weight-matched input. -/
theorem augmentedMatrix_isIso [Finite I]
    (sy : Symmetrizer D) (hc : Sc.Homogeneous) (i : I) (ν : X)
    (t s : Sector I) (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR s)
    (hw : (P).wt s = ν) :
    (0 ≤ D.h i ν → IsIso ((P).augPosMat c[sy,hc] i ν t s Z.obj)) ∧
    (D.h i ν < 0 → IsIso ((P).augNegMat c[sy,hc] i ν t s Z.obj)) := by
  subst ν
  by_cases hts : t = s
  · subst t
    have h := centralAugmentedMatrix_isIso D Sc m cutoff bound ΛP ΛR hP hR sy hc i s Z
    exact ⟨h.1, fun hh => h.2 hh.le⟩
  · have hswap := elvProbeSwappingInvertible D Sc m cutoff bound ΛP ΛR hP hR sy hc
    exact ⟨fun _ => ProbeReservoir.isIso_augPosMat_of_ne c[sy,hc] i ((P).wt s) hts Z.obj
      (fun p q => hswap i ((P).wt s) t s hts p q Z.obj),
      fun _ => ProbeReservoir.isIso_augNegMat_of_ne c[sy,hc] i ((P).wt s) hts Z.obj
        (fun p q => hswap i ((P).wt s) t s hts p q Z.obj)⟩

/-- The five positive identities for the chosen data, on every supported input. -/
theorem pointwiseLeftward_posInverseAt [Finite I]
    (sy : Symmetrizer D) (hc : Sc.Homogeneous) (i : I) (ν : X)
    (t s : Sector I) (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR s)
    (hw : (P).wt s = ν) (hh : 0 ≤ D.h i ν) :
    (P).PosInverseAt c[sy,hc] i ν t s Z.obj
      (fun q p => (L[sy,hc]).lcrossSame i ν q p Z.obj)
      (fun n r p => (L[sy,hc]).dcup i n ν r p Z.obj) := by
  let := (augmentedMatrix_isIso D Sc m cutoff bound ΛP ΛR hP hR sy hc i ν t s Z hw).1 hh
  exact (P).leftwardOfPointwiseAugmentedInverse_posInverseAt c[sy,hc] i ν t s Z.obj hw hh

/-- The five negative identities for the same chosen data and every supported input. -/
theorem pointwiseLeftward_negInverseAt [Finite I]
    (sy : Symmetrizer D) (hc : Sc.Homogeneous) (i : I) (ν : X)
    (t s : Sector I) (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR s)
    (hw : (P).wt s = ν) (hh : D.h i ν < 0) :
    (P).NegInverseAt c[sy,hc] i ν t s Z.obj
      (fun q p => (L[sy,hc]).lcrossSame i ν q p Z.obj)
      (fun n q r => (L[sy,hc]).dcap i n ν q r Z.obj) := by
  let := (augmentedMatrix_isIso D Sc m cutoff bound ΛP ΛR hP hR sy hc i ν t s Z hw).2 hh
  exact (P).leftwardOfPointwiseAugmentedInverse_negInverseAt c[sy,hc] i ν t s Z.obj hw hh

/-- All ten local equal-colour inversion relations hold on the supported inputs. -/
theorem pointwiseLeftward_isInverseAt [Finite I]
    (sy : Symmetrizer D) (hc : Sc.Homogeneous) (s : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR s) :
    (L[sy,hc]).IsInverseAt c[sy,hc] s Z.obj := by
  exact (P).leftwardOfPointwiseAugmentedInverse_isInverseAt c[sy,hc] s Z.obj
    (fun i ν hh t hw =>
      (augmentedMatrix_isIso D Sc m cutoff bound ΛP ΛR hP hR sy hc i ν t s Z hw).1 hh)
    (fun i ν hh t hw =>
      (augmentedMatrix_isIso D Sc m cutoff bound ΛP ΛR hP hR sy hc i ν t s Z hw).2 hh)

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
