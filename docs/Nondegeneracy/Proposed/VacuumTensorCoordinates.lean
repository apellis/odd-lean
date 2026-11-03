import OddMath.QuiverHecke.CyclotomicAction.ELVProbeCapPrecomposition
import OddMath.Algebra.HomogeneousSuperfunctorIso

/-! # Tensor vacuum functors

SwappedVacuumCoordinates: the vacuum functor sends a probe module to the
reservoir vacuum tensored with its value at the empty object. Input maps
retain their Koszul signs. This construction supplies the occupied input
for the evaluated mixed-crossing bend.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.VacuumTensor
universe u
variable {k A C : Type u} [CommRing k]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]

def rightFunctor (V : SVec k) : SVec k ⥤ SVec k where
  obj U := SVec.tensorObj U V
  map f := SVec.whiskerRight f V
  map_id U := SVec.whiskerRight_id U V
  map_comp f g := SVec.comp_whiskerRight f g V

instance rightFunctorAdditive (V : SVec k) : (rightFunctor V).Additive where
  map_add {_ _ f g} := SVec.whiskerRight_add f g V

instance rightFunctorLinear (V : SVec k) : (rightFunctor V).Linear k where
  map_smul f r := MonoidalSupercategory.smul_whiskerRight r f V

instance rightFunctorSuper (V : SVec k) : IsSuperfunctor k (rightFunctor V) where
  map_mem hf := SVec.whiskerRight_mem hf V

def object (W : Superfunctor k C (SVec k)) (V : SVec k) :
    Superfunctor k C (SVec k) := W.comp ⟨rightFunctor V⟩

def map (W : Superfunctor k C (SVec k)) (a : A)
    {M N : Superfunctor k A (SVec k)} (f : M ⟶ N) :
    object W (M.obj a) ⟶ object W (N.obj a) where
  app p c := SVec.whiskerLeft (W.obj c) (f.app p a)
  app_mem p c := SVec.whiskerLeft_mem (W.obj c) (f.app_mem p a)
  naturality p X Y q g hg := by
    change SVec.whiskerRight (W.map g) (M.obj a) ≫ SVec.whiskerLeft (W.obj Y) (f.app p a) =
      koszulSign p q • (SVec.whiskerLeft (W.obj X) (f.app p a) ≫
        SVec.whiskerRight (W.map g) (N.obj a))
    simpa only [koszulSign_comm] using SVec.super_interchange (W.map_mem hg) (f.app_mem p a)

def functor (W : Superfunctor k C (SVec k)) (a : A) :
    Superfunctor k A (SVec k) ⥤ Superfunctor k C (SVec k) where
  obj M := object W (M.obj a)
  map f := map W a f
  map_id M := by
    apply Superfunctor.hom_ext_parity <;> intro c
    · change SVec.whiskerLeft (W.obj c) ((𝟙 M : M ⟶ M).app 0 a) = 𝟙 (SVec.tensorObj (W.obj c) (M.obj a))
      rw [Superfunctor.id_app_zero, SVec.whiskerLeft_id]
    · change SVec.whiskerLeft (W.obj c) ((𝟙 M : M ⟶ M).app 1 a) = 0
      rw [Superfunctor.id_app_one, SVec.whiskerLeft_zero]
  map_comp f g := by
    apply Superfunctor.hom_ext_parity <;> intro c
    · change SVec.whiskerLeft (W.obj c) ((f ≫ g).app 0 a) = _
      simp only [Superfunctor.comp_app_zero, SVec.whiskerLeft_add, SVec.whiskerLeft_comp]
      rfl
    · change SVec.whiskerLeft (W.obj c) ((f ≫ g).app 1 a) = _
      simp only [Superfunctor.comp_app_one, SVec.whiskerLeft_add, SVec.whiskerLeft_comp]
      rfl

instance functorAdditive (W : Superfunctor k C (SVec k)) (a : A) :
    (functor W a).Additive where
  map_add {M N f g} := by
    apply Superfunctor.hom_ext
    intro p c
    exact SVec.whiskerLeft_add (W.obj c) (f.app p a) (g.app p a)

instance functorLinear (W : Superfunctor k C (SVec k)) (a : A) :
    (functor W a).Linear k where
  map_smul f r := by
    apply Superfunctor.hom_ext
    intro p c
    exact SVec.whiskerLeft_smul (W.obj c) r (f.app p a)

instance functorSuper (W : Superfunctor k C (SVec k)) (a : A) :
    IsSuperfunctor k (functor W a) where
  map_mem {M N p f} hf := by
    rw [Superfunctor.mem_parity_iff] at hf ⊢
    funext c
    change SVec.whiskerLeft (W.obj c) (f.app (p + 1) a) = 0
    rw [congrFun hf a]
    change SVec.whiskerLeft (W.obj c) (0 : M.obj a ⟶ N.obj a) = 0
    exact SVec.whiskerLeft_zero (W.obj c)

def superfunctor (W : Superfunctor k C (SVec k)) (a : A) :
    Superfunctor k (Superfunctor k A (SVec k)) (Superfunctor k C (SVec k)) :=
  ⟨functor W a⟩

theorem superfunctor_obj_obj (W : Superfunctor k C (SVec k)) (a : A)
    (M : Superfunctor k A (SVec k)) (c : C) :
    ((superfunctor W a).obj M).obj c = SVec.tensorObj (W.obj c) (M.obj a) := rfl

theorem superfunctor_map_app (W : Superfunctor k C (SVec k)) (a : A)
    {M N : Superfunctor k A (SVec k)} (f : M ⟶ N) (p : ZMod 2) (c : C) :
    ((superfunctor W a).map f).app p c = SVec.whiskerLeft (W.obj c) (f.app p a) := rfl

theorem superfunctor_map_total (W : Superfunctor k C (SVec k)) (a : A)
    {M N : Superfunctor k A (SVec k)} (f : M ⟶ N) (c : C) :
    ((superfunctor W a).map f).total c = SVec.whiskerLeft (W.obj c) (f.total a) := by
  exact (SVec.whiskerLeft_add (W.obj c) (f.app 0 a) (f.app 1 a)).symm

def leftFunctor (U : SVec k) : SVec k ⥤ SVec k where
  obj V := SVec.tensorObj U V
  map f := SVec.whiskerLeft U f
  map_id V := SVec.whiskerLeft_id U V
  map_comp f g := SVec.whiskerLeft_comp U f g

def componentUnitIso (U : SVec k) {V : SVec k} (e : V ≅ SVec.unit) :
    SVec.tensorObj U V ≅ U :=
  (leftFunctor U).mapIso e ≪≫ SVec.rightUnitor U

private theorem componentUnitIso_supernatural (W : Superfunctor k C (SVec k))
    {V : SVec k} (e : V ≅ SVec.unit) (he : e.hom ∈ parity (R := k) _ _ 0) :
    IsSupernatural k 0 (F := (object W V).toFunctor) (G := W.toFunctor)
      (fun c => (componentUnitIso (W.obj c) e).hom) where
  mem c := comp_mem (SVec.whiskerLeft_mem (W.obj c) he) (SVec.rightUnitor_mem (W.obj c))
  naturality {X Y q f} hf := by
    change SVec.whiskerRight (W.map f) V ≫
        (SVec.whiskerLeft (W.obj Y) e.hom ≫ (SVec.rightUnitor (W.obj Y)).hom) =
      sign k (0 * q) • ((SVec.whiskerLeft (W.obj X) e.hom ≫
        (SVec.rightUnitor (W.obj X)).hom) ≫ W.map f)
    rw [zero_mul, sign_zero, one_smul, ← Category.assoc,
      SVec.super_interchange (W.map_mem hf) he]
    have hs : koszulSign q 0 = 1 := by simp [koszulSign]
    rw [hs, one_smul, Category.assoc,
      MonoidalSupercategory.rightUnitor_naturality (R := k) (W.map f), Category.assoc]

/-- An even scalar coordinate identifies the tensor module with its vacuum factor. -/
def unitIso (W : Superfunctor k C (SVec k)) {V : SVec k}
    (e : V ≅ SVec.unit) (he : e.hom ∈ parity (R := k) _ _ 0) : object W V ≅ W :=
  OddMath.HomogeneousSuperfunctorIso.ofComponents
    (fun c => componentUnitIso (W.obj c) e) (componentUnitIso_supernatural W e he)

open scoped TensorProduct in
theorem unitIso_hom_tmul (W : Superfunctor k C (SVec k)) {V : SVec k}
    (e : V ≅ SVec.unit) (he : e.hom ∈ parity (R := k) _ _ 0) (c : C)
    (v : W.obj c) (w : V) :
    (unitIso W e he).hom.total c (v ⊗ₜ[k] w) = e.hom w • v := by
  rw [unitIso, OddMath.HomogeneousSuperfunctorIso.ofComponents_hom_total]
  change (SVec.rightUnitor (W.obj c)).hom (SVec.whiskerLeft (W.obj c) e.hom (v ⊗ₜ[k] w)) = _
  rw [SVec.whiskerLeft_even (W.obj c) he]
  change (TensorProduct.rid k (W.obj c))
    (TensorProduct.map LinearMap.id (SVec.toLinearMap e.hom) (v ⊗ₜ[k] w)) = _
  simp only [TensorProduct.map_tmul, LinearMap.id_apply, TensorProduct.rid_tmul,
    SVec.coe_toLinearMap]

private theorem scalarEquiv_mem {V : SVec k} (e : k ≃ₗ[k] V)
    (hV : ∀ v : V, v ∈ V.part 0) :
    (SVec.isoOfLinearEquiv (V := SVec.unit) (W := V) e).hom ∈ parity (R := k) _ _ 0 := by
  apply SVec.mem_parityHom_of_apply_mem
  intro q c hc
  rcases parity_eq_zero_or_one q with rfl | rfl
  · exact hV (e c)
  · have hc0 : (0 : k) = c := by
      simpa only [SVec.mem_part_one_iff, SVec.unit, LinearMap.zero_apply] using hc
    subst c
    change e 0 ∈ V.part (1 + 0)
    rw [map_zero]
    exact Submodule.zero_mem _

open scoped TensorProduct in
theorem superfunctor_map_app_tmul (W : Superfunctor k C (SVec k)) (a : A)
    {M N : Superfunctor k A (SVec k)} (f : M ⟶ N) (p q : ZMod 2) (c : C)
    (v : W.obj c) (hv : v ∈ (W.obj c).part p) (w : M.obj a) :
    ((superfunctor W a).map f).app q c (v ⊗ₜ[k] w) =
      sign k (p * q) • (v ⊗ₜ[k] f.app q a w) :=
  SVec.whiskerLeft_tmul (f.app_mem q a) hv w

variable {I X : Type u} [AddCommGroup X]

/-- The specified tensor vacuum between the actual probe and reservoir targets. -/
def probeFunctor (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I]
    (m : I → ℕ) (cutoff : I → ℕ) (bound : ℕ)
    (W : ContentModules D Sc cutoff bound 0) :
    ProbeVacuumCap.modulePiCategory D Sc m ⟶ contentModuleTarget D Sc cutoff bound 0 :=
  superfunctor W (probeOldVacuumObject D Sc m)

def probeScalarIso (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ) :
    SVec.unit ≅ (probeOldVacuumRegular D Sc m).obj (probeOldVacuumObject D Sc m) :=
  SVec.isoOfLinearEquiv (probeVacuumScalarEquiv D Sc m)

theorem probeScalarIso_mem (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ) :
    (probeScalarIso D Sc m).hom ∈ parity (R := k) _ _ 0 :=
  scalarEquiv_mem (probeVacuumScalarEquiv D Sc m) (probeVacuum_even D Sc m)

/-- Evaluating the tensor vacuum on the actual regular probe recovers W. -/
def probeVacuumIso (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I]
    (m : I → ℕ) (cutoff : I → ℕ) (bound : ℕ) (W : ContentModules D Sc cutoff bound 0) :
    (probeFunctor D Sc m cutoff bound W).obj (probeOldVacuumRegular D Sc m) ≅ W :=
  unitIso W (probeScalarIso D Sc m).symm
    (inv_mem (probeScalarIso D Sc m) (probeScalarIso_mem D Sc m))

end OddMath.QuiverHecke.ELVOld.VacuumTensor
