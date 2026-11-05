import OddMath.QuiverHecke.CyclotomicAction.ELVCoefficientPowerVacuum
import OddMath.QuiverHecke.CyclotomicAction.ELVUnitCoefficientRows

/-! # Coefficient extraction on the literal power vacuum

The normalized coefficient window in `SwappedVacuumNonpositiveBubbles.md`,
§2, on the actual regular A/T old vacuum. The prescribed inverse row and
the original even empty-component unit identify the target with literal A/T.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.PowerVacuumCoefficient
open CyclotomicCrossingTensor CyclotomicCrossingTensor.TensorMatrixCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (L : I × ℕ → ℕ)

private theorem height (i : I) :
    0 ≤ contentCrossingHeight D cutoff i (([] : List I) : Multiset I) := by
  simp [contentCrossingHeight]

private def topSlot (i : I) (hN : 0 < cutoff i) :
    Fin (contentUnitCount D cutoff i (([] : List I) : Multiset I)) :=
  ⟨cutoff i - 1, by rw [VacuumCoefficient.count]; omega⟩

/-- The ordinary append unit with its input the literal A/T, identified
with the empty old-vacuum component by the original even unit. -/
def unit (i : I) : CoefficientPowerQuotient (k := k) D cutoff L →ₗ[k]
    mateTargetSpace D Sc cutoff i (coefficientPowerVacuum D Sc cutoff L)
      (⟨[]⟩ : OldCategory D Sc cutoff) :=
  ((((BalancedInduction.adjunction (append D Sc cutoff i)).unit.app
    (coefficientPowerVacuum D Sc cutoff L)).total ⟨[]⟩)).comp
      (coefficientPowerVacuumEmptyEquiv D Sc cutoff L).toLinearMap

/-- The literal last inverse row, with its target the actual A/T. No
coefficient extractor is supplied as a premise and no cap is rescaled. -/
def functional (i : I) (hN : 0 < cutoff i) :
    mateTargetSpace D Sc cutoff i (coefficientPowerVacuum D Sc cutoff L)
      (⟨[]⟩ : OldCategory D Sc cutoff) →ₗ[k] CoefficientPowerQuotient (k := k) D cutoff L :=
  (coefficientPowerVacuumEmptyEquiv D Sc cutoff L).symm.toLinearMap.comp
    (moduleUnitCoefficient D Sc cutoff (coefficientPowerVacuum D Sc cutoff L) i ⟨[]⟩
      (height D cutoff i) (topSlot D cutoff i hN))

private theorem emptyInverse_even :
    (coefficientPowerVacuumEmptyEquiv D Sc cutoff L).symm.toLinearMap ∈ parity (R := k)
      ((coefficientPowerVacuum D Sc cutoff L).obj (⟨[]⟩ : OldCategory D Sc cutoff))
      (coefficientPowerSpace (k := k) D cutoff L) 0 := by
  let e := coefficientPowerVacuumEmptyEquiv D Sc cutoff L
  let eIso : coefficientPowerSpace (k := k) D cutoff L ≅
      (coefficientPowerVacuum D Sc cutoff L).obj (⟨[]⟩ : OldCategory D Sc cutoff) := {
    hom := e.toLinearMap
    inv := e.symm.toLinearMap
    hom_inv_id := by apply LinearMap.ext; intro x; exact e.symm_apply_apply x
    inv_hom_id := by apply LinearMap.ext; intro x; exact e.apply_symm_apply x }
  have he : eIso.hom ∈ parity (R := k) (coefficientPowerSpace (k := k) D cutoff L)
      ((coefficientPowerVacuum D Sc cutoff L).obj (⟨[]⟩ : OldCategory D Sc cutoff)) 0 := by
    apply SVec.mem_parityHom_of_apply_mem
    intro p x hx
    change e x ∈ ((coefficientPowerVacuum D Sc cutoff L).obj
      (⟨[]⟩ : OldCategory D Sc cutoff)).part (p + 0)
    simpa only [add_zero] using coefficientPowerVacuumEmptyEquiv_mem D Sc cutoff L hx
  exact Supercategory.inv_mem eIso he

/-- The normalized A/T-valued functional retains the prescribed top-row
parity. In particular odd coefficients cannot pass through it unsigned. -/
theorem functional_mem (i : I) (hN : 0 < cutoff i) :
    functional D Sc cutoff L i hN ∈ parity (R := k)
      (mateTargetSpace D Sc cutoff i (coefficientPowerVacuum D Sc cutoff L) ⟨[]⟩)
      (coefficientPowerSpace (k := k) D cutoff L) ((cutoff i - 1) • D.parity i) := by
  apply SVec.mem_parityHom_of_apply_mem
  intro q x hx
  have hc := SVec.apply_mem_part
    (moduleUnitCoefficient_mem D Sc cutoff (coefficientPowerVacuum D Sc cutoff L) i ⟨[]⟩
      (height D cutoff i) (topSlot D cutoff i hN)) hx
  have h := SVec.apply_mem_part (emptyInverse_even D Sc cutoff L) hc
  change (coefficientPowerVacuumEmptyEquiv D Sc cutoff L).symm
    (moduleUnitCoefficient D Sc cutoff (coefficientPowerVacuum D Sc cutoff L) i ⟨[]⟩
      (height D cutoff i) (topSlot D cutoff i hN) x) ∈
        (coefficientPowerSpace (k := k) D cutoff L).part (q + (cutoff i - 1) • D.parity i)
  change (coefficientPowerVacuumEmptyEquiv D Sc cutoff L).symm
    (moduleUnitCoefficient D Sc cutoff (coefficientPowerVacuum D Sc cutoff L) i ⟨[]⟩
      (height D cutoff i) (topSlot D cutoff i hN) x) ∈
        (coefficientPowerSpace (k := k) D cutoff L).part
          (q + (cutoff i - 1) • D.parity i + 0) at h
  simpa only [add_zero] using h

/-- The exact normalized extraction window as an identity on every
coefficient vector of literal A/T, for both moving parities. -/
theorem functional_dot_window (i : I) (hN : 0 < cutoff i)
    (a : ℕ) (ha : a < cutoff i) (z : CoefficientPowerQuotient (k := k) D cutoff L) :
    functional D Sc cutoff L i hN
      (((actualInductionDot D Sc cutoff i (coefficientPowerVacuum D Sc cutoff L)
        ((append D Sc cutoff i).obj ⟨[]⟩)) ^ a) (unit D Sc cutoff L i z)) =
      if a + 1 = cutoff i then z else 0 := by
  let e := coefficientPowerVacuumEmptyEquiv D Sc cutoff L
  let c := moduleUnitCoefficient D Sc cutoff (coefficientPowerVacuum D Sc cutoff L)
    i ⟨[]⟩ (height D cutoff i) (topSlot D cutoff i hN)
  let dot : Module.End k (mateTargetSpace D Sc cutoff i
      (coefficientPowerVacuum D Sc cutoff L) ⟨[]⟩) :=
    actualInductionDot D Sc cutoff i (coefficientPowerVacuum D Sc cutoff L)
      ((append D Sc cutoff i).obj ⟨[]⟩)
  let u0 : (coefficientPowerVacuum D Sc cutoff L).obj (⟨[]⟩ : OldCategory D Sc cutoff) →ₗ[k]
      mateTargetSpace D Sc cutoff i (coefficientPowerVacuum D Sc cutoff L) ⟨[]⟩ :=
    (((BalancedInduction.adjunction (append D Sc cutoff i)).unit.app
      (coefficientPowerVacuum D Sc cutoff L)).total ⟨[]⟩)
  have he : (a = cutoff i - 1) ↔ a + 1 = cutoff i := by omega
  have h := moduleUnitCoefficient_dot_window D Sc cutoff (coefficientPowerVacuum D Sc cutoff L)
    i ⟨[]⟩ (height D cutoff i) (topSlot D cutoff i hN) a
    (by simpa only [VacuumCoefficient.count] using ha) (e z)
  change c ((dot ^ a) (u0 (e z))) = if a = cutoff i - 1 then e z else 0 at h
  change e.symm (c ((dot ^ a) (u0 (e z)))) = _
  by_cases hh : a + 1 = cutoff i
  · have hv : c ((dot ^ a) (u0 (e z))) = e z := by
      simpa only [ite_eq_left (he.mpr hh)] using h
    simpa only [ite_eq_left hh] using (congrArg e.symm hv).trans (e.symm_apply_apply z)
  · have hv : c ((dot ^ a) (u0 (e z))) = 0 := by
      simpa only [ite_eq_right (fun hEq => hh (he.mp hEq))] using h
    simpa only [ite_eq_right hh] using (congrArg e.symm hv).trans (map_zero e.symm)

/-- The even empty-component unit retains the full coefficient action,
with its original multiplication order, including odd coefficients. -/
theorem empty_coefficient_action
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (x : CoefficientPowerQuotient (k := k) D cutoff L) :
    (coefficientPowerVacuum D Sc cutoff L).map (X := ⟨[]⟩) (Y := ⟨[]⟩)
      (coefficientEndomorphism D Sc cutoff [] a)
        (coefficientPowerVacuumEmptyEquiv D Sc cutoff L x) =
      coefficientPowerVacuumEmptyEquiv D Sc cutoff L
        ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a * x) := by
  let J := powerCoefficientEmbedding D Sc cutoff
  let R := liftedPowerRegular (k := k) D cutoff L
  let s := powerCoefficientStar (k := k) D cutoff
  have h := LinearMap.congr_fun (BalancedInduction.unit_naturality J R.toFunctor
    (show s ⟶ s from a)) x
  exact h

private theorem empty_coefficient_decode
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff)
    (x : (coefficientPowerVacuum D Sc cutoff L).obj (⟨[]⟩ : OldCategory D Sc cutoff)) :
    (coefficientPowerVacuumEmptyEquiv D Sc cutoff L).symm
      ((coefficientPowerVacuum D Sc cutoff L).map (X := ⟨[]⟩) (Y := ⟨[]⟩)
        (coefficientEndomorphism D Sc cutoff [] a) x) =
      (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a *
        (coefficientPowerVacuumEmptyEquiv D Sc cutoff L).symm x := by
  let e := coefficientPowerVacuumEmptyEquiv D Sc cutoff L
  have h := empty_coefficient_action D Sc cutoff L a (e.symm x)
  rw [e.apply_symm_apply] at h
  change (coefficientPowerVacuum D Sc cutoff L).map (X := ⟨[]⟩) (Y := ⟨[]⟩)
    (coefficientEndomorphism D Sc cutoff [] a) x =
    e ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a *
      e.symm x) at h
  have h' := congrArg e.symm h
  rw [e.symm_apply_apply] at h'
  exact h'

/-- The full A/T-superlinearity of the actual inverse row. The
coefficient acts in its original left order, with the top-row Koszul sign. -/
theorem functional_coefficient (i : I) (hN : 0 < cutoff i) {q : ZMod 2}
    {a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff}
    (ha : a ∈ SKM.SYM.elvCoefficientParity D cutoff q)
    (z : mateTargetSpace D Sc cutoff i (coefficientPowerVacuum D Sc cutoff L) ⟨[]⟩) :
    functional D Sc cutoff L i hN
      ((SVec.toLinearMap (((BalancedInduction.restriction (append D Sc cutoff i)).obj
        ((BalancedInduction.induction (append D Sc cutoff i)).obj
          (coefficientPowerVacuum D Sc cutoff L))).map (X := ⟨[]⟩) (Y := ⟨[]⟩)
            (coefficientEndomorphism D Sc cutoff [] a))) z) =
      koszulSign ((cutoff i - 1) • D.parity i) q •
        ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a *
          functional D Sc cutoff L i hN z) := by
  let M := coefficientPowerVacuum D Sc cutoff L
  let T := (BalancedInduction.restriction (append D Sc cutoff i)).obj
    ((BalancedInduction.induction (append D Sc cutoff i)).obj M)
  let f : (⟨[]⟩ : OldCategory D Sc cutoff) ⟶ ⟨[]⟩ := coefficientEndomorphism D Sc cutoff [] a
  let e := coefficientPowerVacuumEmptyEquiv D Sc cutoff L
  let row := moduleUnitCoefficient D Sc cutoff M i ⟨[]⟩
    (height D cutoff i) (topSlot D cutoff i hN)
  let K : ℤ := koszulSign ((cutoff i - 1) • D.parity i) q
  have hf : f ∈ parity (R := k) (⟨[]⟩ : OldCategory D Sc cutoff) ⟨[]⟩ q :=
    coefficientEndomorphism_mem D Sc cutoff [] ha
  have h := LinearMap.congr_fun (moduleUnitCoefficient_end_naturality D Sc cutoff M
    i ⟨[]⟩ (height D cutoff i) (topSlot D cutoff i hN) f hf) z
  change row ((SVec.toLinearMap (T.map (X := ⟨[]⟩) (Y := ⟨[]⟩) f)) z) =
    K • (M.map (X := ⟨[]⟩) (Y := ⟨[]⟩) f (row z)) at h
  have hd := empty_coefficient_decode D Sc cutoff L a (row z)
  change e.symm (M.map (X := ⟨[]⟩) (Y := ⟨[]⟩) f (row z)) =
    (coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a *
      e.symm (row z) at hd
  change e.symm (row ((SVec.toLinearMap (T.map (X := ⟨[]⟩) (Y := ⟨[]⟩) f)) z)) =
    K • ((coefficientPowerIdeal D cutoff (elementaryCoefficients (k := k) D cutoff) L).ringCon.mkₐ k a *
      e.symm (row z))
  calc
    _ = e.symm (K • M.map (X := ⟨[]⟩) (Y := ⟨[]⟩) f (row z)) := congrArg e.symm h
    _ = K • e.symm (M.map (X := ⟨[]⟩) (Y := ⟨[]⟩) f (row z)) := by rw [map_zsmul]
    _ = _ := congrArg (fun w : CoefficientPowerQuotient (k := k) D cutoff L => K • w) hd

end OddMath.QuiverHecke.ELVOld.PowerVacuumCoefficient
