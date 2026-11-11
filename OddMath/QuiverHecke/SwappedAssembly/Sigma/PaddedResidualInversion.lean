import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.SignedResidualWindows
import OddMath.QuiverHecke.SwappedAssembly.Sigma.ReservoirWindowCoefficientIdeal
import OddMath.QuiverHecke.CyclotomicAction.ELVProbePaddedContentBends
import OddMath.QuiverHecke.CyclotomicAction.ParameterTwistPureNilpotent

/-! # The chosen central augmented matrix on each output content

SwappedActionAssembly §6 and SwappedHomInversion §§3–6: the chosen ELV
mixed coefficient gives invertible positive and negative central factor
matrices on every supported Hom input and every output content. The
finite bend series, chosen reservoir inverse entries and normalized OLD
probe windows discharge the six signed-height residual cases. Inversion
is lifted in the coefficient ideal of this one output-content category;
there is no uniform bound over a weight fibre and no Hom grading.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory OddMath.SKM BicategoryStruct
namespace OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
open CyclotomicAction ELVOld ProbeWindow
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Finite I]
  (D : Datum I X) (Sc : Scalars D k) (m cutoff : I → ℕ) (bound : ℕ)
  (ΛP ΛR : X)
  (hP : ∀ i, (probeCutoff D m i : ℤ) = D.h i ΛP)
  (hR : ∀ i, (cutoff i : ℤ) = D.h i ΛR)
local notation "P" => elvProbeReservoir D Sc m cutoff bound ΛP ΛR hP hR
local instance paddedResidualHomPi (A B : PiSCat.{u,u,u+1} k) :
    PiSupercategory k (A ⟶ B) := PiTwoSupercategory.homPiLeft A B

/-- Every output-content component of the prescribed padded central
matrix is invertible, in both signs and at every pair of local heights. -/
theorem centralFactorMatrix_content_isIso
    (sy : Symmetrizer D) (hc : Sc.Homogeneous) (i : I) (t : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t)
    (β : WeightBlocks D ΛR ((P).muM t)) :
    (0 ≤ D.h i ((P).wt t) → IsIso ((P).augPosFactorMatrix
      (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc) i ((P).wt t) t Z.obj
        (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β))) ∧
    (D.h i ((P).wt t) ≤ 0 → IsIso ((P).augNegFactorMatrix
      (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc) i ((P).wt t) t Z.obj
        (reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β))) := by
  have : Fact Sc.PureNilpotent := ⟨hc.noPure.pureNilpotent⟩
  let E := reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β
  let c := elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc
  let J := contentModuleCoefficientIdeal D (parameterTwist D Sc) cutoff bound β.1 sy
    (parameterTwist_homogeneous D Sc hc) ((P).T.obj (-((P).muP t)))
  let x := probeWindowX D Sc m cutoff bound ΛP ΛR hP hR i t Z E
  let y := probeWindowY D Sc m cutoff bound ΛP ΛR hP hR i t Z E
  let v := (P).centralPaddedCap i t Z.obj E true 0
  let u := (P).centralPaddedUnit i t Z.obj E true 0
  let vR := (P).centralPaddedCap i t Z.obj E false
  let uR := (P).centralPaddedUnit i t Z.obj E false
  let sR := (P).centralPaddedSigma c i t Z.obj E false false
  let sP := (P).centralPaddedSigma c i t Z.obj E true true
  let Cx := (P).centralPaddedSigma c i t Z.obj E false true
  let Dx := (P).centralPaddedSigma c i t Z.obj E true false
  let q := koszulSign (D.parity i) (D.parity i)
  let r := D.h i ((P).muM t)
  let p := -D.h i (-((P).muP t))
  have hheight : D.h i ((P).wt t) = r + p := by
    change D.cd.coroot i ((P).muP t + (P).muM t) =
      D.cd.coroot i ((P).muM t) + -D.cd.coroot i (-((P).muP t))
    rw [map_add, map_neg, neg_neg, add_comm]
  have hJ0 {A B : (P).T.obj (-((P).muP t)) ⟶
      contentModuleTarget D (parameterTwist D Sc) cutoff bound β.1} (f : A ⟶ B) :
      J.mem 0 f := mem_coeffIdeal_zero
        (Gr := contentModuleCoeffGrading D (parameterTwist D Sc) cutoff bound β.1 sy
          (parameterTwist_homogeneous D Sc hc)) f
  have hslide : sP ≫ y.hom - q • (x.hom ≫ sP) = v ≫ u :=
    probe_slide D Sc m cutoff bound ΛP ΛR hP hR c i t Z E
  have hq : q * q = 1 := koszulSign_mul_self _ _
  obtain ⟨N, hN, hDx, hCx⟩ := elvProbe_content_padded_central_separated_windows_above
    D Sc m cutoff bound ΛP ΛR hP hR i t Z.obj β sy hc (max r.toNat (-r).toNat)
  change Dx = -∑ a ∈ Finset.range N,
    q ^ (a + 1) • ((x ^ (-(a : ℤ) - 1)).hom ≫ v ≫ uR a) at hDx
  change Cx = ∑ a ∈ Finset.range N,
    q ^ (a + 2) • (vR a ≫ u ≫ (y ^ (-(a : ℤ) - 1)).hom) at hCx
  have hRcap (hr : 0 ≤ r) : ReservoirCapConditions J sR vR uR r.toNat := by
    let V := reservoirCapInverseData D Sc m cutoff bound ΛP ΛR hP hR i t Z E c hr
    refine ⟨V.principal, V.window, V.isInverse, ?_, ?_⟩
    · exact reservoirCapInverseData_closure_mem D Sc m cutoff bound ΛP ΛR hP hR sy hc i t Z β c hr
    · intro n a ha
      exact reservoirCapInverseData_boundary_mem D Sc m cutoff bound ΛP ΛR hP hR sy hc i t Z β c hr n a
        (lt_of_lt_of_le n.isLt ha)
  have hRcup (hr : r ≤ 0) : ReservoirCupConditions J sR vR uR (-r).toNat := by
    let V := reservoirCupInverseData D Sc m cutoff bound ΛP ΛR hP hR i t Z E c hr
    refine ⟨V.principal, V.window, V.isInverse, ?_, ?_⟩
    · exact reservoirCupInverseData_closure_mem D Sc m cutoff bound ΛP ΛR hP hR sy hc i t Z β c hr
    · intro n a ha
      exact reservoirCupInverseData_boundary_mem D Sc m cutoff bound ΛP ΛR hP hR sy hc i t Z β c hr n a
        (lt_of_lt_of_le n.isLt ha)
  have hPcap (hp : 0 ≤ p) : ∃ j A, IsCapInverse sP
      (fun n : Fin p.toNat => (x ^ (n : ℤ)).hom ≫ v) j A := by
    have hp' : D.h i (-((P).muP t)) ≤ 0 := by change 0 ≤ -_ at hp; omega
    obtain ⟨j, A, h⟩ := probe_capInverse D Sc m cutoff bound ΛP ΛR hP hR c i t Z E hp'
    refine ⟨j, A, ?_⟩
    have he : (fun n : Fin p.toNat => (P).centralPaddedCap i t Z.obj E true n) =
        (fun n : Fin p.toNat => (x ^ (n : ℤ)).hom ≫ v) := by
      funext n
      exact probe_cap_power D Sc m cutoff bound ΛP ΛR hP hR i t Z E n
    rw [he] at h
    exact h
  have hPcup (hp : p ≤ 0) : ∃ j B, IsCupInverse sP
      (fun n : Fin (-p).toNat => u ≫ (y ^ (n : ℤ)).hom) j B := by
    have hp' : 0 ≤ D.h i (-((P).muP t)) := by change -_ ≤ 0 at hp; omega
    have hcount : (-p).toNat = (D.h i (-((P).muP t))).toNat := by
      dsimp only [p]
      omega
    rw [hcount]
    obtain ⟨j, B, h⟩ := probe_cupInverse D Sc m cutoff bound ΛP ΛR hP hR c i t Z E hp'
    refine ⟨j, B, ?_⟩
    have he : (fun n : Fin (D.h i (-((P).muP t))).toNat =>
        (P).centralPaddedUnit i t Z.obj E true n) =
        (fun n : Fin (D.h i (-((P).muP t))).toNat => u ≫ (y ^ (n : ℤ)).hom) := by
      funext n
      exact probe_unit_power D Sc m cutoff bound ΛP ΛR hP hR i t Z E n
    rw [he] at h
    exact h
  constructor
  · intro hh
    have H := isIso_posMap_of_signed_windows J hJ0 vR uR x y v u q hq hslide r p hN hDx hCx
      hRcap hRcup hPcap hPcup (by rw [← hheight]; exact hh)
    change IsIso (posMap sR sP Cx Dx vR
      (fun a : Fin (D.h i ((P).wt t)).toNat => (P).centralPaddedCap i t Z.obj E true a))
    rw [hheight]
    have he : (fun a : Fin (r + p).toNat => (P).centralPaddedCap i t Z.obj E true a) =
        (fun a : Fin (r + p).toNat => (x ^ (a : ℤ)).hom ≫ v) := by
      funext a
      exact probe_cap_power D Sc m cutoff bound ΛP ΛR hP hR i t Z E a
    rw [he]
    exact H
  · intro hh
    have H := isIso_negMap_of_signed_windows J hJ0 vR uR x y v u q hq hslide r p hN hDx hCx
      hRcap hRcup hPcap hPcup (by rw [← hheight]; exact hh)
    have H' := isIso_negMap_neg_principals sR sP Cx Dx uR _ H
    change IsIso (negMap (-sR) (-sP) (-Cx) (-Dx) uR
      (fun a : Fin (-D.h i ((P).wt t)).toNat => (P).centralPaddedUnit i t Z.obj E true a))
    rw [hheight]
    have he : (fun a : Fin (-(r + p)).toNat => (P).centralPaddedUnit i t Z.obj E true a) =
        (fun a : Fin (-(r + p)).toNat => u ≫ (y ^ (a : ℤ)).hom) := by
      funext a
      exact probe_unit_power D Sc m cutoff bound ΛP ΛR hP hR i t Z E a
    rw [he]
    exact H'

/-- Component inverses assemble on the literal augmented matrices. Each
content may use its own coefficient-ideal bound and its own finite bend
length; the entire input superfunctor is retained. -/
theorem centralAugmentedMatrix_isIso
    (sy : Symmetrizer D) (hc : Sc.Homogeneous) (i : I) (t : Sector I)
    (Z : H D (parameterTwist D Sc) m cutoff bound ΛP ΛR t) :
    (0 ≤ D.h i ((P).wt t) → IsIso ((P).augPosMat
      (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc) i ((P).wt t) t t Z.obj)) ∧
    (D.h i ((P).wt t) ≤ 0 → IsIso ((P).augNegMat
      (elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc) i ((P).wt t) t t Z.obj)) := by
  let c := elvProbeCrossCoeff D Sc m cutoff bound ΛP ΛR hP hR sy hc
  constructor
  · intro hh
    apply RegularReservoir.isIso_of_eval
      (fun β : WeightBlocks D ΛR ((P).muM t) => ContentModules D (parameterTwist D Sc) cutoff bound β.1)
      ((P).T.obj (-((P).muP t)))
    intro β
    let E := reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β
    exact isIso_of_comp_eq_comp ((P).augPosSourceIso i ((P).wt t) t Z.obj E).hom _ _
      ((P).augPosTargetIso i ((P).wt t) t Z.obj E).hom inferInstance
      ((centralFactorMatrix_content_isIso D Sc m cutoff bound ΛP ΛR hP hR sy hc i t Z β).1 hh)
      inferInstance ((P).augPosFactorMatrix_square c i ((P).wt t) t Z.obj E)
  · intro hh
    apply RegularReservoir.isIso_of_eval
      (fun β : WeightBlocks D ΛR ((P).muM t) => ContentModules D (parameterTwist D Sc) cutoff bound β.1)
      ((P).T.obj (-((P).muP t)))
    intro β
    let E := reservoirOutputEval D Sc m cutoff bound ΛP ΛR hP hR t β
    exact isIso_of_comp_eq_comp ((P).augNegSourceIso i ((P).wt t) t Z.obj E).hom _ _
      ((P).augNegTargetIso i ((P).wt t) t Z.obj E).hom inferInstance
      ((centralFactorMatrix_content_isIso D Sc m cutoff bound ΛP ΛR hP hR sy hc i t Z β).2 hh)
      inferInstance ((P).augNegFactorMatrix_square c i ((P).wt t) t Z.obj E)

end OddMath.QuiverHecke.SwappedAssembly.SupportedSectors
