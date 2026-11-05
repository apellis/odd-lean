import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumTensor
import OddMath.Algebra.HomogeneousSuperfunctorIso

/-! # Tensor-vacuum scalar coordinates

SwappedVacuumCoordinates: evaluation at the regular height-zero probe
recovers the reservoir vacuum as an even module isomorphism. The map uses
the prescribed probe scalar coordinate and the tensor right unitor.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld.VacuumTensor
universe u
variable {k : Type u} [CommRing k]

/-- Scalar extraction on the right tensor factor followed by the ordinary
right unitor, retaining its inverse as a linear equivalence. -/
def scalarTensorEquiv (U V : SVec k) (e : V ≃ₗ[k] k) :
    SVec.tensorObj U V ≃ₗ[k] U :=
  (TensorProduct.congr (LinearEquiv.refl k U) e).trans (TensorProduct.rid k U)

theorem scalarTensorEquiv_tmul (U V : SVec k) (e : V ≃ₗ[k] k) (v : U) (w : V) :
    scalarTensorEquiv U V e (v ⊗ₜ[k] w) = e w • v := by
  simp only [scalarTensorEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul,
    LinearEquiv.refl_apply, TensorProduct.rid_tmul]

private theorem scalarTensorEquiv_naturality {U U' V : SVec k}
    (e : V ≃ₗ[k] k) (f : U →ₗ[k] U') :
    (scalarTensorEquiv U' V e).toLinearMap ∘ₗ TensorProduct.map f LinearMap.id =
      f ∘ₗ (scalarTensorEquiv U V e).toLinearMap := by
  apply TensorProduct.ext'
  intro v w
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.id_apply,
    LinearEquiv.coe_coe]
  rw [scalarTensorEquiv_tmul U' V e (f v) w, scalarTensorEquiv_tmul U V e v w, map_smul]

private theorem scalarTensorEquiv_mem (U V : SVec k) (e : V ≃ₗ[k] k)
    (he : SVec.ofHom e.toLinearMap ∈ parity (R := k) V SVec.unit 0) :
    (SVec.isoOfLinearEquiv (scalarTensorEquiv U V e)).hom ∈
      parity (R := k) (SVec.tensorObj U V) U 0 := by
  have h := comp_mem (SVec.whiskerLeft_mem U he) (SVec.rightUnitor_mem U)
  rw [SVec.whiskerLeft_even U he] at h
  exact h

private theorem scalarCoordinate_mem {V : SVec k} (e : V ≃ₗ[k] k)
    (hV : ∀ v : V, v ∈ V.part 0) :
    SVec.ofHom e.toLinearMap ∈ parity (R := k) V SVec.unit 0 := by
  intro q
  apply LinearMap.ext
  intro v
  change e (V.proj q v) = (SVec.unit (k := k)).proj (q + 0) (e v)
  rw [SVec.proj_apply_of_mem_part V (p := q) (hV v)]
  rcases parity_eq_zero_or_one q with rfl | rfl
  · simp only [ite_true, add_zero]
    exact (SVec.unit_proj_zero_apply (e v)).symm
  · simp only [one_ne_zero, ite_false, map_zero, add_zero]
    exact (SVec.unit_proj_one_apply (e v)).symm

variable {C : Type u} [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]

private theorem scalarTensorEquiv_supernatural (W : Superfunctor k C (SVec k))
    (V : SVec k) (e : V ≃ₗ[k] k)
    (he : SVec.ofHom e.toLinearMap ∈ parity (R := k) V SVec.unit 0) :
    IsSupernatural k 0 (F := (object W V).toFunctor) (G := W.toFunctor)
      (fun c => (SVec.isoOfLinearEquiv (scalarTensorEquiv (W.obj c) V e)).hom) where
  mem c := scalarTensorEquiv_mem (W.obj c) V e he
  naturality {X Y q f} _ := by
    rw [zero_mul, sign_zero, one_smul]
    exact (scalarTensorEquiv_naturality e (SVec.toLinearMap (W.map f)))

/-- The right scalar coordinate is an even isomorphism of whole reservoir
modules, natural on all output arrows including odd ones. -/
def scalarTensorIso (W : Superfunctor k C (SVec k))
    (V : SVec k) (e : V ≃ₗ[k] k)
    (he : SVec.ofHom e.toLinearMap ∈ parity (R := k) V SVec.unit 0) :
    object W V ≅ W :=
  HomogeneousSuperfunctorIso.ofComponents
    (fun c => SVec.isoOfLinearEquiv (scalarTensorEquiv (W.obj c) V e))
    (scalarTensorEquiv_supernatural W V e he)

theorem scalarTensorIso_hom_mem (W : Superfunctor k C (SVec k))
    (V : SVec k) (e : V ≃ₗ[k] k)
    (he : SVec.ofHom e.toLinearMap ∈ parity (R := k) V SVec.unit 0) :
    (scalarTensorIso W V e he).hom ∈ parity (R := k) _ _ 0 :=
  HomogeneousSuperfunctorIso.ofComponents_hom_mem _ _

theorem scalarTensorIso_hom_tmul (W : Superfunctor k C (SVec k))
    (V : SVec k) (e : V ≃ₗ[k] k)
    (he : SVec.ofHom e.toLinearMap ∈ parity (R := k) V SVec.unit 0)
    (c : C) (v : W.obj c) (w : V) :
    (scalarTensorIso W V e he).hom.total c (v ⊗ₜ[k] w) = e w • v := by
  rw [scalarTensorIso, HomogeneousSuperfunctorIso.ofComponents_hom_total]
  exact scalarTensorEquiv_tmul (W.obj c) V e v w

private theorem scalarTensorIso_hom_tmul_inverse (W : Superfunctor k C (SVec k))
    (V : SVec k) (e : V ≃ₗ[k] k)
    (he : SVec.ofHom e.toLinearMap ∈ parity (R := k) V SVec.unit 0)
    (c : C) (v : W.obj c) :
    (scalarTensorIso W V e he).hom.total c (v ⊗ₜ[k] e.symm 1) = v := by
  rw [scalarTensorIso_hom_tmul W V e he c v (e.symm 1),
    LinearEquiv.apply_symm_apply, one_smul]

variable {I X : Type u} [AddCommGroup X]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)
  (cutoff : I → ℕ) (bound : ℕ) (W : ContentModules D Sc cutoff bound 0)

/-- The actual tensor vacuum evaluated at the regular probe is the given
reservoir vacuum, using precisely its original scalar coordinate. -/
def probeVacuumIso :
    (probeFunctor D Sc m cutoff bound W).obj (probeOldVacuumRegular D Sc m) ≅ W :=
  scalarTensorIso W _ (probeVacuumScalarEquiv D Sc m).symm
    (scalarCoordinate_mem (probeVacuumScalarEquiv D Sc m).symm (probeVacuum_even D Sc m))

theorem probeVacuumIso_hom_mem :
    (probeVacuumIso D Sc m cutoff bound W).hom ∈ parity (R := k) _ _ 0 :=
  scalarTensorIso_hom_mem _ _ _ _

/-- The occupied tensor vector goes to the same reservoir coefficient,
without a scalar rescaling or a parity sign. -/
theorem probeVacuumIso_hom_tmul (c : ContentCategory D Sc cutoff bound 0) (v : W.obj c) :
    (probeVacuumIso D Sc m cutoff bound W).hom.total c
      (v ⊗ₜ[k] probeVacuumScalarEquiv D Sc m 1) = v := by
  exact scalarTensorIso_hom_tmul_inverse W _ (probeVacuumScalarEquiv D Sc m).symm
    (scalarCoordinate_mem (probeVacuumScalarEquiv D Sc m).symm (probeVacuum_even D Sc m)) c v

end OddMath.QuiverHecke.ELVOld.VacuumTensor
