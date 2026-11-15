import OddMath.QuiverHecke.CyclotomicAction.ProbeCap
import OddMath.Algebra.HomogeneousSuperfunctorIso
import OddMath.QuiverHecke.CyclotomicAction.InductionGridRouquier
import OddMath.Algebra.FiniteSupermoduleFunctor
import OddMath.QuiverHecke.CyclotomicAction.ModuleInduction
import OddMath.QuiverHecke.CyclotomicAction.ContentMatrix
import OddMath.QuiverHecke.CyclotomicAction.InductionGridMate
import OddMath.QuiverHecke.CyclotomicAction.InductionMixed
import OddMath.QuiverHecke.CyclotomicAction.WeightedAppend
import OddMath.QuiverHecke.CyclotomicAction.ContentBlockExtension
import OddMath.QuiverHecke.CyclotomicAction.CategoryGrading

/-!
# Induction triple braid

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

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

theorem superfunctor_map_total (W : Superfunctor k C (SVec k)) (a : A)
    {M N : Superfunctor k A (SVec k)} (f : M ⟶ N) (c : C) :
    ((superfunctor W a).map f).total c = SVec.whiskerLeft (W.obj c) (f.total a) := by
  exact (SVec.whiskerLeft_add (W.obj c) (f.app 0 a) (f.app 1 a)).symm

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

end OddMath.QuiverHecke.ELVOld.VacuumTensor
end

end

section

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
end

end

section

/-! # The zero lower cell inside the module target

The empty boundary of BE (1.14) uses a zero lower E/F cell inside the
same module parity category, rather than a separate zero category.
This supplies that cell and its even right adjunction for the local data.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k : Type u} [CommRing k]
  (C : Type u) [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]

/-- The empty coordinate product is a zero module on the given category. -/
def zeroModule : Superfunctor k C (SVec k) :=
  FiniteSupermodule.product (fun e : Empty => nomatch e)

/-- The zero module has zero identity in the existing module category. -/
theorem zeroModule_id : (𝟙 (zeroModule (k := k) C) : _ ⟶ _) = 0 := by
  apply Superfunctor.hom_ext
  intro p t
  apply SVec.hom_ext
  intro x
  funext e
  exact Empty.elim e

/-- The constant zero functor retains the existing source and target
module categories; it sends both parity components of every map to zero. -/
def zeroModuleFunctor : Superfunctor k C (SVec k) ⥤ Superfunctor k C (SVec k) where
  obj _ := zeroModule C
  map _ := 0
  map_id _ := (zeroModule_id C).symm
  map_comp _ _ := by simp

instance zeroModuleFunctor_additive : (zeroModuleFunctor (k := k) C).Additive where
  map_add := by intros; exact (add_zero _).symm

instance zeroModuleFunctor_linear : (zeroModuleFunctor (k := k) C).Linear k where
  map_smul _ _ := (smul_zero _).symm

instance zeroModuleFunctor_super : IsSuperfunctor k (zeroModuleFunctor (k := k) C) where
  map_mem _ := Submodule.zero_mem _

end OddMath.QuiverHecke.ELVOld.BalancedInduction
end

end

section

/-! # Three-path relations under balanced induction

Brundan–Ellis (1.9): the three crossing parities occur in reverse order
on the two sides of a multicolour braid. Their superopposite composition
signs agree. This intermediate transport lemma takes the literal source
path equation; concrete OLD specializations supply it from the quotient.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
private theorem multicolour_transform_total
    {k C A : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
    {F G : C ⥤ A} [F.Additive] [F.Linear k] [IsSuperfunctor k F]
    [G.Additive] [G.Linear k] [IsSuperfunctor k G]
    {p : ZMod 2} {γ : ∀ s, F.obj s ⟶ G.obj s} (hγ : IsSupernatural k p γ)
    (M : Superfunctor k C (SVec k)) (w : A) :
    (transformComponent hγ M).total w = transformLinear hγ M w := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [SuperNatTrans.total, transformComponent_app,
      ite_true, ite_false, zero_ne_one, one_ne_zero, add_zero, zero_add]

variable {k C A : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  (T₀ T₁ T₂ T₃ T₄ T₅ : C ⥤ A)
  [T₀.Additive] [T₀.Linear k] [IsSuperfunctor k T₀]
  [T₁.Additive] [T₁.Linear k] [IsSuperfunctor k T₁]
  [T₂.Additive] [T₂.Linear k] [IsSuperfunctor k T₂]
  [T₃.Additive] [T₃.Linear k] [IsSuperfunctor k T₃]
  [T₄.Additive] [T₄.Linear k] [IsSuperfunctor k T₄]
  [T₅.Additive] [T₅.Linear k] [IsSuperfunctor k T₅]
  {p q r : ZMod 2}
  {α₀ : ∀ s, T₀.obj s ⟶ T₁.obj s} {α₁ : ∀ s, T₁.obj s ⟶ T₂.obj s}
  {α₂ : ∀ s, T₂.obj s ⟶ T₃.obj s} {β₀ : ∀ s, T₀.obj s ⟶ T₄.obj s}
  {β₁ : ∀ s, T₄.obj s ⟶ T₅.obj s} {β₂ : ∀ s, T₅.obj s ⟶ T₃.obj s}
  (hα₀ : IsSupernatural k p α₀) (hα₁ : IsSupernatural k q α₁)
  (hα₂ : IsSupernatural k r α₂) (hβ₀ : IsSupernatural k r β₀)
  (hβ₁ : IsSupernatural k q β₁) (hβ₂ : IsSupernatural k p β₂)

/-- The two reversed three-map paths have the same superopposite sign. -/
theorem transformComponent_multicolour_braid
    (hb : ∀ s, α₀ s ≫ α₁ s ≫ α₂ s = β₀ s ≫ β₁ s ≫ β₂ s)
    (M : Superfunctor k C (SVec k)) :
    transformComponent hα₂ M ≫ transformComponent hα₁ M ≫ transformComponent hα₀ M =
      transformComponent hβ₂ M ≫ transformComponent hβ₁ M ≫ transformComponent hβ₀ M := by
  rw [transformComponent_comp hα₀ hα₁, Linear.comp_smul,
    transformComponent_comp (hα₀.comp hα₁) hα₂,
    transformComponent_comp hβ₀ hβ₁, Linear.comp_smul,
    transformComponent_comp (hβ₀.comp hβ₁) hβ₂,
    smul_smul, smul_smul, ← sign_add, ← sign_add]
  have hs : p * q + (p + q) * r = r * q + (r + q) * p := by ring
  rw [hs]
  congr 1
  apply OddMath.FiniteSupermodule.hom_ext_total (k := k)
  intro w
  have hp : (p + q) + r = (r + q) + p := by ring
  have he : (fun s => (α₀ s ≫ α₁ s) ≫ α₂ s) =
      (fun s => (β₀ s ≫ β₁ s) ≫ β₂ s) := by
    funext s
    simpa only [Category.assoc] using hb s
  rw [multicolour_transform_total, multicolour_transform_total]
  apply hom_ext
  intro s a b
  simp only [transformLinear_tensor, ← hp]
  rw [← congrFun he s]

end OddMath.QuiverHecke.ELVOld.BalancedInduction
end

end

section

/-! # Braids on a cube of balanced induction functors

Brundan–Ellis (1.9): the six prescribed rectangular crossing comparisons
transport a source braid through twelve independent induction edges.
The source equation is an explicit input only to this generic transport
lemma; concrete OLD quotient specializations supply it.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
private theorem cube_three_squares {C : Type*} [Category* C]
    {X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Y₃ : C}
    (e₀ : X₀ ⟶ Y₀) (e₁ : X₁ ⟶ Y₁) (e₂ : X₂ ⟶ Y₂) (e₃ : X₃ ⟶ Y₃)
    (a₀ : X₀ ⟶ X₁) (a₁ : X₁ ⟶ X₂) (a₂ : X₂ ⟶ X₃)
    (b₀ : Y₀ ⟶ Y₁) (b₁ : Y₁ ⟶ Y₂) (b₂ : Y₂ ⟶ Y₃)
    (h₀ : a₀ ≫ e₁ = e₀ ≫ b₀) (h₁ : a₁ ≫ e₂ = e₁ ≫ b₁)
    (h₂ : a₂ ≫ e₃ = e₂ ≫ b₂) :
    (a₀ ≫ a₁ ≫ a₂) ≫ e₃ = e₀ ≫ (b₀ ≫ b₁ ≫ b₂) := by
  simp only [Category.assoc]
  rw [h₂, ← Category.assoc a₁, h₁, Category.assoc e₁, ← Category.assoc a₀, h₀, Category.assoc]

variable {k C Aᵢ Aⱼ Aₗ Pᵢⱼ Pᵢₗ Pⱼₗ T : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} Aᵢ] [Preadditive Aᵢ] [Linear k Aᵢ] [Supercategory k Aᵢ]
  [Category.{u} Aⱼ] [Preadditive Aⱼ] [Linear k Aⱼ] [Supercategory k Aⱼ]
  [Category.{u} Aₗ] [Preadditive Aₗ] [Linear k Aₗ] [Supercategory k Aₗ]
  [Category.{u} Pᵢⱼ] [Preadditive Pᵢⱼ] [Linear k Pᵢⱼ] [Supercategory k Pᵢⱼ]
  [Category.{u} Pᵢₗ] [Preadditive Pᵢₗ] [Linear k Pᵢₗ] [Supercategory k Pᵢₗ]
  [Category.{u} Pⱼₗ] [Preadditive Pⱼₗ] [Linear k Pⱼₗ] [Supercategory k Pⱼₗ]
  [Category.{u} T] [Preadditive T] [Linear k T] [Supercategory k T]
  (Ai : C ⥤ Aᵢ) [Ai.Additive] [Ai.Linear k] [IsSuperfunctor k Ai]
  (Aj : C ⥤ Aⱼ) [Aj.Additive] [Aj.Linear k] [IsSuperfunctor k Aj]
  (Al : C ⥤ Aₗ) [Al.Additive] [Al.Linear k] [IsSuperfunctor k Al]
  (Bij_i : Aᵢ ⥤ Pᵢⱼ) [Bij_i.Additive] [Bij_i.Linear k] [IsSuperfunctor k Bij_i]
  (Bij_j : Aⱼ ⥤ Pᵢⱼ) [Bij_j.Additive] [Bij_j.Linear k] [IsSuperfunctor k Bij_j]
  (Bil_i : Aᵢ ⥤ Pᵢₗ) [Bil_i.Additive] [Bil_i.Linear k] [IsSuperfunctor k Bil_i]
  (Bil_l : Aₗ ⥤ Pᵢₗ) [Bil_l.Additive] [Bil_l.Linear k] [IsSuperfunctor k Bil_l]
  (Bjl_j : Aⱼ ⥤ Pⱼₗ) [Bjl_j.Additive] [Bjl_j.Linear k] [IsSuperfunctor k Bjl_j]
  (Bjl_l : Aₗ ⥤ Pⱼₗ) [Bjl_l.Additive] [Bjl_l.Linear k] [IsSuperfunctor k Bjl_l]
  (Cl : Pᵢⱼ ⥤ T) [Cl.Additive] [Cl.Linear k] [IsSuperfunctor k Cl]
  (Cj : Pᵢₗ ⥤ T) [Cj.Additive] [Cj.Linear k] [IsSuperfunctor k Cj]
  (Ci : Pⱼₗ ⥤ T) [Ci.Additive] [Ci.Linear k] [IsSuperfunctor k Ci]
  {p q r : ZMod 2}
  {α₀ : ∀ s, (Ai ⋙ Bij_i).obj s ⟶ (Aj ⋙ Bij_j).obj s}
  {α₁ : ∀ s, (Bij_j ⋙ Cl).obj s ⟶ (Bjl_j ⋙ Ci).obj s}
  {α₂ : ∀ s, (Aj ⋙ Bjl_j).obj s ⟶ (Al ⋙ Bjl_l).obj s}
  {β₀ : ∀ s, (Bij_i ⋙ Cl).obj s ⟶ (Bil_i ⋙ Cj).obj s}
  {β₁ : ∀ s, (Ai ⋙ Bil_i).obj s ⟶ (Al ⋙ Bil_l).obj s}
  {β₂ : ∀ s, (Bil_l ⋙ Cj).obj s ⟶ (Bjl_l ⋙ Ci).obj s}
  (hα₀ : IsSupernatural k p α₀) (hα₁ : IsSupernatural k q α₁)
  (hα₂ : IsSupernatural k r α₂) (hβ₀ : IsSupernatural k r β₀)
  (hβ₁ : IsSupernatural k q β₁) (hβ₂ : IsSupernatural k p β₂)

/-- The first path around the induction cube, with three independent pair crossings. -/
def inductionCubeLeftBraid (N : Superfunctor k C (SVec k)) :
    induced Ci (induced Bjl_l (induced Al N)) ⟶ induced Cl (induced Bij_i (induced Ai N)) :=
  (induction Ci).map (rectangularCrossComponent Aj Al Bjl_j Bjl_l hα₂ N) ≫
    rectangularCrossComponent Bij_j Bjl_j Cl Ci hα₁ ((induction Aj).obj N) ≫
      (induction Cl).map (rectangularCrossComponent Ai Aj Bij_i Bij_j hα₀ N)

/-- The second path uses the other three pairs of the same twelve edges. -/
def inductionCubeRightBraid (N : Superfunctor k C (SVec k)) :
    induced Ci (induced Bjl_l (induced Al N)) ⟶ induced Cl (induced Bij_i (induced Ai N)) :=
  rectangularCrossComponent Bil_l Bjl_l Cj Ci hβ₂ ((induction Al).obj N) ≫
    (induction Cj).map (rectangularCrossComponent Ai Al Bil_i Bil_l hβ₁ N) ≫
      rectangularCrossComponent Bij_i Bil_i Cl Cj hβ₀ ((induction Ai).obj N)

/-- The six flattening squares transport the literal source braid. -/
theorem inductionCube_braid
    (hb : ∀ s, Cl.map (α₀ s) ≫ α₁ (Aj.obj s) ≫ Ci.map (α₂ s) =
      β₀ (Ai.obj s) ≫ Cj.map (β₁ s) ≫ β₂ (Al.obj s))
    (N : Superfunctor k C (SVec k)) :
    inductionCubeLeftBraid Ai Aj Al Bij_i Bij_j Bjl_j Bjl_l Cl Ci hα₀ hα₁ hα₂ N =
      inductionCubeRightBraid Ai Al Bij_i Bil_i Bil_l Bjl_l Cl Cj Ci hβ₀ hβ₁ hβ₂ N := by
  let e₀ := inductionTripleFlattening Al Bjl_l Ci N
  let e₁ := inductionTripleFlattening Aj Bjl_j Ci N
  let e₂ := inductionTripleFlattening Aj Bij_j Cl N
  let e₃ := inductionTripleFlattening Ai Bij_i Cl N
  let e₄ := inductionTripleFlattening Al Bil_l Cj N
  let e₅ := inductionTripleFlattening Ai Bil_i Cj N
  have hL := cube_three_squares e₀.hom e₁.hom e₂.hom e₃.hom
    ((induction Ci).map (rectangularCrossComponent Aj Al Bjl_j Bjl_l hα₂ N))
    (rectangularCrossComponent Bij_j Bjl_j Cl Ci hα₁ ((induction Aj).obj N))
    ((induction Cl).map (rectangularCrossComponent Ai Aj Bij_i Bij_j hα₀ N))
    (transformComponent (hα₂.whiskerRight Ci) N)
    (transformComponent (hα₁.whiskerLeft Aj) N)
    (transformComponent (hα₀.whiskerRight Cl) N)
    (inductionTripleFlattening_prefix_rectangular Al Bjl_l Aj Bjl_j Ci hα₂ N)
    (inductionTripleFlattening_suffix_rectangular Aj Bjl_j Ci Bij_j Cl hα₁ N)
    (inductionTripleFlattening_prefix_rectangular Aj Bij_j Ai Bij_i Cl hα₀ N)
  have hR := cube_three_squares e₀.hom e₄.hom e₅.hom e₃.hom
    (rectangularCrossComponent Bil_l Bjl_l Cj Ci hβ₂ ((induction Al).obj N))
    ((induction Cj).map (rectangularCrossComponent Ai Al Bil_i Bil_l hβ₁ N))
    (rectangularCrossComponent Bij_i Bil_i Cl Cj hβ₀ ((induction Ai).obj N))
    (transformComponent (hβ₂.whiskerLeft Al) N)
    (transformComponent (hβ₁.whiskerRight Cj) N)
    (transformComponent (hβ₀.whiskerLeft Ai) N)
    (inductionTripleFlattening_suffix_rectangular Al Bjl_l Ci Bil_l Cj hβ₂ N)
    (inductionTripleFlattening_prefix_rectangular Al Bil_l Ai Bil_i Cj hβ₁ N)
    (inductionTripleFlattening_suffix_rectangular Ai Bil_i Cj Bij_i Cl hβ₀ N)
  have hd := transformComponent_multicolour_braid
    ((Ai ⋙ Bij_i) ⋙ Cl) ((Aj ⋙ Bij_j) ⋙ Cl) ((Aj ⋙ Bjl_j) ⋙ Ci)
    ((Al ⋙ Bjl_l) ⋙ Ci) ((Ai ⋙ Bil_i) ⋙ Cj) ((Al ⋙ Bil_l) ⋙ Cj)
    (hα₀.whiskerRight Cl) (hα₁.whiskerLeft Aj) (hα₂.whiskerRight Ci)
    (hβ₀.whiskerLeft Ai) (hβ₁.whiskerRight Cj) (hβ₂.whiskerLeft Al) hb N
  apply (cancel_mono e₃.hom).mp
  exact hL.trans ((congrArg (fun f => e₀.hom ≫ f) hd).trans hR.symm)

end OddMath.QuiverHecke.ELVOld.BalancedInduction
end

end

section

/-! # Ordered three-dot corrections in arbitrary balanced induction

Brundan–Ellis (1.9): keep the superopposite three-power signs and the
reflection of the correction summation index on arbitrary source/target
categories. No coefficient-power truncation is assumed. The scalar
support and parameter involution retain the original-Sc correction.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (F : C ⥤ E) [F.Additive] [F.Linear k] [IsSuperfunctor k F]

private theorem triple_end_pow_mem {V : E} {p : ZMod 2} {a : End V}
    (ha : a ∈ parity (R := k) _ _ p) (n : ℕ) :
    a ^ n ∈ parity (R := k) _ _ ((n : ZMod 2) * p) := by
  induction n with
  | zero => simpa using id_mem (R := k) V
  | succ n ih =>
    rw [pow_succ', End.mul_def]
    simpa [add_mul] using comp_mem ih ha

/-- Full ordered three-power evaluation, including the twist of every kernel coefficient. -/
theorem transformLinear_three_powers
    {p q t : ZMod 2} {a b c : ∀ s, End (F.obj s)}
    (ha : IsSupernatural k p a) (hb : IsSupernatural k q b) (hc : IsSupernatural k t c)
    (N : Superfunctor k C (SVec k)) (w : E) (l s n : ℕ)
    (v : C) (g : F.obj v ⟶ w) (z : N.obj v) :
    ((transformLinear hc N w ^ n) * (transformLinear hb N w ^ s) *
        (transformLinear ha N w ^ l)) (tensor F N.toFunctor v g z) =
      sign k (p * (l / 2 : ℕ) + q * (s / 2 : ℕ) + t * (n / 2 : ℕ) +
        (s : ZMod 2) * q * ((l : ZMod 2) * p) +
        (n : ZMod 2) * t * ((s : ZMod 2) * q + (l : ZMod 2) * p)) •
      inductionEndTensorEval F N w v
        (twist k ((n : ZMod 2) * t + ((s : ZMod 2) * q + (l : ZMod 2) * p)) g) z
        (a v ^ l * b v ^ s * c v ^ n) := by
  rw [Module.End.mul_apply, Module.End.mul_apply,
    transformLinear_pow_tensor, map_smul, transformLinear_pow_tensor,
    map_smul, map_smul, transformLinear_pow_tensor]
  dsimp only [inductionEndTensorEval, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [twist_comp, twist_of_mem _ (triple_end_pow_mem (ha.mem v) l),
    twist_of_mem _ (triple_end_pow_mem (hb.mem v) s), ← twist_add,
    Linear.smul_comp, Linear.comp_smul, tensor, ← TensorProduct.smul_tmul',
    map_smul, smul_smul, ← sign_add]
  congr 1
  · congr 1
    ring
  congr 2
  simp only [End.mul_def, Category.assoc]

/-- Supported three-power summands reflect to the twisted source coefficient. -/
theorem transformLinear_three_supported
    {p q : ZMod 2} {a b c : ∀ v, End (F.obj v)}
    (ha : IsSupernatural k p a) (hb : IsSupernatural k q b) (hc : IsSupernatural k p c)
    (N : Superfunctor k C (SVec k)) (w : E)
    (r s l : ℕ) (hr : (r : ZMod 2) * p = 0) (hs : (s : ZMod 2) * q = 0)
    (hl : l < r) (d : k) (v : C) (g : F.obj v ⟶ w) (z : N.obj v) :
    ((sign k (p * (q + (l : ZMod 2))) * d) •
      ((transformLinear hc N w ^ (r - 1 - l)) *
        (transformLinear hb N w ^ s) * (transformLinear ha N w ^ l)))
        (tensor F N.toFunctor v g z) =
      sign k (p * q) • inductionEndTensorEval F N w v (twist k p g) z
        ((sign k (p * (q + ((r - 1 - l : ℕ) : ZMod 2))) *
          (sign k (p * q + p * (r / 2 : ℕ) + q * (s / 2 : ℕ)) * d)) •
          (a v ^ l * b v ^ s * c v ^ (r - 1 - l))) := by
  rw [LinearMap.smul_apply, transformLinear_three_powers,
    mixed_braid_total_parity p q r s l hr hs hl, map_smul, smul_smul, smul_smul]
  congr 1
  let n := r - 1 - l
  have hp : p * p = p := by
    rcases parity_eq_zero_or_one p with hp | hp <;> simp [hp]
  have he := mixed_braid_sign_identity p q r s l n hr hs hl rfl
  have hsign : sign k (p * (q + (l : ZMod 2))) *
      sign k (p * (l / 2 : ℕ) + q * (s / 2 : ℕ) + p * (n / 2 : ℕ) +
        (s : ZMod 2) * q * ((l : ZMod 2) * p) +
        (n : ZMod 2) * p * ((s : ZMod 2) * q + (l : ZMod 2) * p)) =
      sign k (p * q) * (sign k (p * (q + (n : ZMod 2))) *
        sign k (p * q + p * (r / 2 : ℕ) + q * (s / 2 : ℕ))) := by
    simp only [← sign_add]
    congr 1
    have hz : (2 : ZMod 2) = 0 := rfl
    linear_combination he + (n : ZMod 2) * (l : ZMod 2) * hp - p * q * hz
  calc
    _ = (sign k (p * (q + (l : ZMod 2))) *
      sign k (p * (l / 2 : ℕ) + q * (s / 2 : ℕ) + p * (n / 2 : ℕ) +
        (s : ZMod 2) * q * ((l : ZMod 2) * p) +
        (n : ZMod 2) * p * ((s : ZMod 2) * q + (l : ZMod 2) * p))) * d := by ring
    _ = _ := by rw [hsign]; ring

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (i j : I) {a b c : ∀ v, End (F.obj v)}
  (ha : IsSupernatural k (D.parity i) a) (hb : IsSupernatural k (D.parity j) b)
  (hc : IsSupernatural k (D.parity i) c)

/-- Reflection of the summation index retains the exact parameter involution. -/
theorem transformLinear_tripleSum_tensor
    (r s : ℕ) (d : k)
    (hd : d ≠ 0 → (r : ZMod 2) * D.parity i = 0 ∧ (s : ZMod 2) * D.parity j = 0)
    (N : Superfunctor k C (SVec k)) (w : E) (v : C) (g : F.obj v ⟶ w) (z : N.obj v) :
    tripleDotCorrectionSum D i j r s d (transformLinear ha N w) (transformLinear hb N w)
        (transformLinear hc N w) (tensor F N.toFunctor v g z) =
      sign k (D.parity i * D.parity j) •
        inductionEndTensorEval F N w v (twist k (D.parity i) g) z
          (tripleDotCorrectionSum D i j r s
            (SKM.zsign k (parameterSignExponent D i j r s) * d) (c v) (b v) (a v)) := by
  by_cases hd0 : d = 0
  · simp [tripleDotCorrectionSum, hd0]
  obtain ⟨hr, hs⟩ := hd hd0
  unfold tripleDotCorrectionSum
  rw [← Finset.sum_range_reflect (fun l =>
    (SKM.zsign k (D.parity i * (D.parity j + l)) *
      (SKM.zsign k (parameterSignExponent D i j r s) * d)) •
      (a v ^ (r - 1 - l) * b v ^ s * c v ^ l)) r]
  simp only [LinearMap.sum_apply, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  have hl' := Finset.mem_range.mp hl
  have he : r - 1 - (r - 1 - l) = l := by omega
  rw [he]
  simpa only [sign_eq_zsign, parameterSignExponent] using
    transformLinear_three_supported F ha hb hc N w r s l hr hs hl' d v g z

/-- The ordered original-Sc correction is the full parameter-twisted source evaluation. -/
theorem transformLinear_triplePolynomial_tensor (hij : i ≠ j)
    (N : Superfunctor k C (SVec k)) (w : E) (v : C) (g : F.obj v ⟶ w) (z : N.obj v) :
    tripleDotCorrectionPolynomial D Sc i j
        (transformLinear ha N w) (transformLinear hb N w) (transformLinear hc N w)
        (tensor F N.toFunctor v g z) =
      sign k (D.parity i * D.parity j) •
        inductionEndTensorEval F N w v (twist k (D.parity i) g) z
          (tripleDotCorrectionPolynomial D (parameterTwist D Sc) i j (c v) (b v) (a v)) := by
  have ht := transformLinear_tripleSum_tensor F D i j ha hb hc (D.dn i j) 0 (Sc.t i j : k)
    (fun _ => ⟨CyclotomicAction.dn_cast_mul_parity D hij, by simp⟩) N w v g z
  have hs (r s : ℕ) := transformLinear_tripleSum_tensor F D i j ha hb hc
    r s (Sc.s i j r s) (fun hz => elvParameter_support D Sc hz) N w v g z
  unfold tripleDotCorrectionPolynomial
  simp only [LinearMap.add_apply, LinearMap.sum_apply, map_add, map_sum, smul_add,
    Finset.smul_sum, ht, hs, CyclotomicAction.parameterTwist_t_of_ne D Sc hij,
    CyclotomicAction.parameterTwist_s]

end OddMath.QuiverHecke.ELVOld.BalancedInduction
end

end

section

/-! # The whole ordered induction correction

Brundan–Ellis (1.9): the parameter-supported three-dot source correction
is supernatural of the outer colour parity. Its entire induced linear
operator equals the ordered correction with the original parameters.
No polynomial-naturality, braid or comparison premise is imposed.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
variable {k C E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (F : C ⥤ E) [F.Additive] [F.Linear k] [IsSuperfunctor k F]

omit [F.Additive] [F.Linear k] [IsSuperfunctor k F] in
private theorem correction_zero_supernatural (p : ZMod 2) :
    IsSupernatural k p (F := F) (G := F) (fun _ => 0) where
  mem _ := Submodule.zero_mem _
  naturality _ := by simp

omit [F.Additive] [F.Linear k] [IsSuperfunctor k F] in
private theorem correction_smul_supernatural {p : ZMod 2}
    {a : ∀ s, F.obj s ⟶ F.obj s} (ha : IsSupernatural k p a) (d : k) :
    IsSupernatural k p (fun s => d • a s) where
  mem s := Submodule.smul_mem _ d (ha.mem s)
  naturality hf := by
    simp only [Linear.comp_smul, Linear.smul_comp, ha.naturality hf, smul_smul]
    rw [mul_comm d]

omit [F.Additive] [F.Linear k] [IsSuperfunctor k F] in
private theorem correction_sum_supernatural {ι : Type*} (S : Finset ι) {p : ZMod 2}
    {a : ι → ∀ s, F.obj s ⟶ F.obj s}
    (ha : ∀ x ∈ S, IsSupernatural k p (a x)) :
    IsSupernatural k p (fun s => ∑ x ∈ S, a x s) where
  mem s := Submodule.sum_mem _ (fun x hx => (ha x hx).mem s)
  naturality hf := by
    simp only [Preadditive.comp_sum, Preadditive.sum_comp, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    exact (ha x hx).naturality hf

omit [F.Additive] [F.Linear k] [IsSuperfunctor k F] in
private theorem correction_add_supernatural {p : ZMod 2}
    {a b : ∀ s, F.obj s ⟶ F.obj s} (ha : IsSupernatural k p a) (hb : IsSupernatural k p b) :
    IsSupernatural k p (fun s => a s + b s) where
  mem s := Submodule.add_mem _ (ha.mem s) (hb.mem s)
  naturality hf := by
    simp only [Preadditive.comp_add, Preadditive.add_comp, ha.naturality hf,
      hb.naturality hf, smul_add]

omit [IsSuperfunctor k F] in
private theorem correction_pow_supernatural {p : ZMod 2}
    {a : ∀ s, End (F.obj s)} (ha : IsSupernatural k p a) (n : ℕ) :
    IsSupernatural k ((n : ZMod 2) * p) (fun s => a s ^ n) := by
  induction n with
  | zero => simpa using isSupernatural_id (R := k) (F := F)
  | succ n ih =>
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, pow_succ', End.mul_def] using ih.comp ha

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (i j : I) {a b c : ∀ s, End (F.obj s)}
  (ha : IsSupernatural k (D.parity i) a) (hb : IsSupernatural k (D.parity j) b)
  (hc : IsSupernatural k (D.parity i) c)

include ha hb hc in
omit [IsSuperfunctor k F] in
/-- The supported source summand has the outer parity, including every reflected term. -/
theorem tripleSourceSum_supernatural (r s : ℕ) (d : k)
    (hd : d ≠ 0 → (r : ZMod 2) * D.parity i = 0 ∧ (s : ZMod 2) * D.parity j = 0) :
    IsSupernatural k (D.parity i) (fun v =>
      tripleDotCorrectionSum D (R := End (F.obj v)) i j r s d (c v) (b v) (a v)) := by
  by_cases hd0 : d = 0
  · simpa only [tripleDotCorrectionSum, hd0, mul_zero, zero_smul, Finset.sum_const_zero] using
      correction_zero_supernatural F (D.parity i)
  obtain ⟨hr, hs⟩ := hd hd0
  apply correction_sum_supernatural F (Finset.range r)
  intro l hl
  have hdeg : ((l : ZMod 2) * D.parity i + (s : ZMod 2) * D.parity j) +
      ((r - 1 - l : ℕ) : ZMod 2) * D.parity i = D.parity i := by
    calc
      _ = ((r - 1 - l : ℕ) : ZMod 2) * D.parity i +
          ((s : ZMod 2) * D.parity j + (l : ZMod 2) * D.parity i) := by ring
      _ = _ := mixed_braid_total_parity (D.parity i) (D.parity j) r s l hr hs (Finset.mem_range.mp hl)
  have hm := ((correction_pow_supernatural F hc l).comp
    (correction_pow_supernatural F hb s)).comp (correction_pow_supernatural F ha (r - 1 - l))
  rw [hdeg] at hm
  have hm' : IsSupernatural k (D.parity i) (fun v =>
      a v ^ (r - 1 - l) * b v ^ s * c v ^ l) := by
    simpa only [End.mul_def, Category.assoc] using hm
  exact correction_smul_supernatural F hm' (SKM.zsign k (D.parity i * (D.parity j + l)) * d)

include ha hb hc in
omit [IsSuperfunctor k F] in
/-- The full source correction is natural without an additional naturality hypothesis. -/
theorem tripleSourcePolynomial_supernatural (hij : i ≠ j) :
    IsSupernatural k (D.parity i) (fun v =>
      tripleDotCorrectionPolynomial D Sc (R := End (F.obj v)) i j (c v) (b v) (a v)) := by
  apply correction_add_supernatural F
  · exact tripleSourceSum_supernatural F D i j ha hb hc (D.dn i j) 0 (Sc.t i j : k)
      (fun _ => ⟨CyclotomicAction.dn_cast_mul_parity D hij, by simp⟩)
  · apply correction_sum_supernatural F (Finset.range (D.dn i j))
    intro r _
    apply correction_sum_supernatural F (Finset.range (D.dn j i))
    intro s _
    exact tripleSourceSum_supernatural F D i j ha hb hc r s (Sc.s i j r s)
      (fun hz => elvParameter_support D Sc hz)

/-- Whole linear operators retain the ordered original-Sc correction. -/
theorem transformLinear_triplePolynomial_eq (hij : i ≠ j)
    (N : Superfunctor k C (SVec k)) (w : E) :
    tripleDotCorrectionPolynomial D Sc i j
        (transformLinear ha N w) (transformLinear hb N w) (transformLinear hc N w) =
      sign k (D.parity i * D.parity j) •
        transformLinear (tripleSourcePolynomial_supernatural F D (parameterTwist D Sc) i j ha hb hc hij) N w := by
  apply hom_ext
  intro v g z
  rw [LinearMap.smul_apply, transformLinear_tensor,
    transformLinear_triplePolynomial_tensor F D Sc i j ha hb hc hij N w v g z]
  rfl

end OddMath.QuiverHecke.ELVOld.BalancedInduction
end

end

section

/-! # The three independent dots under triple-induction flattening

Brundan–Ellis (1.9): the one chosen triple flattening intertwines the
first, middle and last independently whiskered induction dots with their
literal source positional transformations. Changing categories and the
ordinary induction-composition isomorphisms are retained throughout.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u

private theorem mapped_dot_square
    {C A : Type*} [Category* C] [Category* A] (F : C ⥤ A)
    {X Y : C} {Z : A} (a : End X) (e : X ⟶ Y) (b : End Y)
    (f : F.obj Y ⟶ Z) (c : End Z)
    (ha : a ≫ e = e ≫ b) (hb : F.map b ≫ f = f ≫ c) :
    F.map a ≫ (F.map e ≫ f) = (F.map e ≫ f) ≫ c := by
  rw [← Category.assoc, ← Functor.map_comp, ha, Functor.map_comp,
    Category.assoc, hb, Category.assoc]

private theorem composite_dot_square {C : Type*} [Category* C]
    {X Y Z : C} (a : End X) (e : X ⟶ Y) (b : End Y) (f : Y ⟶ Z) (c : End Z)
    (ha : a ≫ e = e ≫ b) (hb : b ≫ f = f ≫ c) :
    a ≫ (e ≫ f) = (e ≫ f) ≫ c := by
  rw [← Category.assoc, ha, Category.assoc, hb, Category.assoc]

variable {k C A B E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (L : B ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]

/-- The actual first dot, mapped by both later inductions, uses the selected triple flattening. -/
theorem inductionTripleFlattening_first_dot {p : ZMod 2}
    {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
    (M : Superfunctor k C (SVec k)) :
    (induction L).map ((induction K).map (dotEnd J hα M)) ≫
        (inductionTripleFlattening J K L M).hom =
      (inductionTripleFlattening J K L M).hom ≫
        dotEnd ((J ⋙ K) ⋙ L) ((hα.whiskerRight K).whiskerRight L) M :=
  mapped_dot_square (induction L) ((induction K).map (dotEnd J hα M))
    ((inductionComp J K).hom.app M) (dotEnd (J ⋙ K) (hα.whiskerRight K) M)
    ((inductionComp (J ⋙ K) L).hom.app M)
    (dotEnd ((J ⋙ K) ⋙ L) ((hα.whiskerRight K).whiskerRight L) M)
    (inductionComp_inner_dot J K hα M) (inductionComp_inner_dot (J ⋙ K) L (hα.whiskerRight K) M)

/-- The independently chosen middle dot uses that same triple flattening. -/
theorem inductionTripleFlattening_middle_dot {p : ZMod 2}
    {β : ∀ s, K.obj s ⟶ K.obj s} (hβ : IsSupernatural k p β)
    (M : Superfunctor k C (SVec k)) :
    (induction L).map (dotEnd K hβ ((induction J).obj M)) ≫
        (inductionTripleFlattening J K L M).hom =
      (inductionTripleFlattening J K L M).hom ≫
        dotEnd ((J ⋙ K) ⋙ L) ((hβ.whiskerLeft J).whiskerRight L) M :=
  mapped_dot_square (induction L) (dotEnd K hβ ((induction J).obj M))
    ((inductionComp J K).hom.app M) (dotEnd (J ⋙ K) (hβ.whiskerLeft J) M)
    ((inductionComp (J ⋙ K) L).hom.app M)
    (dotEnd ((J ⋙ K) ⋙ L) ((hβ.whiskerLeft J).whiskerRight L) M)
    (inductionComp_outer_dot J K hβ M) (inductionComp_inner_dot (J ⋙ K) L (hβ.whiskerLeft J) M)

/-- The independent last dot uses the prefix-first flattening via its proved suffix equality. -/
theorem inductionTripleFlattening_last_dot {p : ZMod 2}
    {γ : ∀ s, L.obj s ⟶ L.obj s} (hγ : IsSupernatural k p γ)
    (M : Superfunctor k C (SVec k)) :
    dotEnd L hγ ((induction K).obj ((induction J).obj M)) ≫
        (inductionTripleFlattening J K L M).hom =
      (inductionTripleFlattening J K L M).hom ≫
        dotEnd ((J ⋙ K) ⋙ L) (hγ.whiskerLeft (J ⋙ K)) M := by
  rw [inductionTripleFlattening_suffix]
  exact composite_dot_square
    (dotEnd L hγ ((induction K).obj ((induction J).obj M)))
    ((inductionComp K L).hom.app ((induction J).obj M))
    (dotEnd (K ⋙ L) (hγ.whiskerLeft K) ((induction J).obj M))
    ((inductionComp J (K ⋙ L)).hom.app M)
    (dotEnd ((J ⋙ K) ⋙ L) (hγ.whiskerLeft (J ⋙ K)) M)
    (inductionComp_outer_dot K L hγ ((induction J).obj M))
    (inductionComp_outer_dot J (K ⋙ L) (hγ.whiskerLeft K) M)

end OddMath.QuiverHecke.ELVOld.BalancedInduction
end

end

section

/-! # The whole original-parameter correction through the triple chart

Brundan–Ellis (1.9): the polynomial in the three independent nested
induction dots is the same original-Sc correction through the prescribed
triple flattening. The source correction and its naturality are constructed
from the dots and parameter support, without comparison premises.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u

private theorem triple_transform_total {k C E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    {F G : C ⥤ E} [F.Additive] [F.Linear k] [IsSuperfunctor k F]
    [G.Additive] [G.Linear k] [IsSuperfunctor k G]
    {p : ZMod 2} {γ : ∀ s, F.obj s ⟶ G.obj s} (hγ : IsSupernatural k p γ)
    (N : Superfunctor k C (SVec k)) (w : E) :
    (transformComponent hγ N).total w = transformLinear hγ N w := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [SuperNatTrans.total, transformComponent_app,
      ite_true, ite_false, zero_ne_one, one_ne_zero, add_zero, zero_add]

variable {k C E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (F : C ⥤ E) [F.Additive] [F.Linear k] [IsSuperfunctor k F]
  {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (i j : I) {a b c : ∀ s, End (F.obj s)}
  (ha : IsSupernatural k (D.parity i) a) (hb : IsSupernatural k (D.parity j) b)
  (hc : IsSupernatural k (D.parity i) c)

/-- The entire module correction is the original-Sc ordered polynomial. -/
theorem transformComponent_triplePolynomial (hij : i ≠ j)
    (N : Superfunctor k C (SVec k)) :
    tripleDotCorrectionPolynomial D Sc (R := End (induced F N)) i j
        (transformComponent ha N) (transformComponent hb N) (transformComponent hc N) =
      sign k (D.parity i * D.parity j) •
        transformComponent (tripleSourcePolynomial_supernatural F D (parameterTwist D Sc)
          i j ha hb hc hij) N := by
  apply OddMath.FiniteSupermodule.hom_ext_total
  intro w
  let ev : End (induced F N) →ₐ[k] Module.End k ((induced F N).obj w) :=
    (svecEndEvaluation ((induced F N).obj w)).comp (supernaturalEndEvaluation (induced F N) w)
  change ev (tripleDotCorrectionPolynomial D Sc i j
      (transformComponent ha N) (transformComponent hb N) (transformComponent hc N)) =
    ev (sign k (D.parity i * D.parity j) • transformComponent
      (tripleSourcePolynomial_supernatural F D (parameterTwist D Sc) i j ha hb hc hij) N)
  rw [tripleDotCorrectionPolynomial_map, map_smul]
  change tripleDotCorrectionPolynomial D Sc (R := Module.End k ((induced F N).obj w)) i j
      ((transformComponent ha N).total w) ((transformComponent hb N).total w)
      ((transformComponent hc N).total w) =
    sign k (D.parity i * D.parity j) •
      ((transformComponent (tripleSourcePolynomial_supernatural F D (parameterTwist D Sc)
        i j ha hb hc hij) N).total w)
  rw [triple_transform_total, triple_transform_total, triple_transform_total, triple_transform_total]
  exact transformLinear_triplePolynomial_eq F D Sc i j ha hb hc hij N w

section Chart
variable {A B : Type u}
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (L : B ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
  {α : ∀ s, End (J.obj s)} {β : ∀ s, End (K.obj s)} {γ : ∀ s, End (L.obj s)}
  (hα : IsSupernatural k (D.parity i) α) (hβ : IsSupernatural k (D.parity j) β)
  (hγ : IsSupernatural k (D.parity i) γ)

/-- The actual three nested dots give the same correction under the chosen triple chart. -/
theorem inductionTripleFlattening_polynomial (hij : i ≠ j)
    (N : Superfunctor k C (SVec k)) :
    tripleDotCorrectionPolynomial D Sc (R := End (induced L (induced K (induced J N)))) i j
        ((induction L).map ((induction K).map (dotEnd J hα N)))
        ((induction L).map (dotEnd K hβ ((induction J).obj N)))
        (dotEnd L hγ ((induction K).obj ((induction J).obj N))) =
      inductionEndConjugation (k := k) (inductionTripleFlattening J K L N)
        (sign k (D.parity i * D.parity j) • transformComponent
          (tripleSourcePolynomial_supernatural ((J ⋙ K) ⋙ L) D (parameterTwist D Sc) i j
            ((hα.whiskerRight K).whiskerRight L) ((hβ.whiskerLeft J).whiskerRight L)
            (hγ.whiskerLeft (J ⋙ K)) hij) N) := by
  let e := inductionTripleFlattening J K L N
  have ht := transformComponent_triplePolynomial ((J ⋙ K) ⋙ L) D Sc i j
    ((hα.whiskerRight K).whiskerRight L) ((hβ.whiskerLeft J).whiskerRight L)
    (hγ.whiskerLeft (J ⋙ K)) hij N
  have hp := congrArg (fun z : End (induced ((J ⋙ K) ⋙ L) N) =>
    inductionEndConjugation (k := k) e z) ht
  rw [tripleDotCorrectionPolynomial_map] at hp
  have h₁ : inductionEndConjugation (k := k) e
      (transformComponent ((hα.whiskerRight K).whiskerRight L) N) =
      (induction L).map ((induction K).map (dotEnd J hα N)) :=
    inductionEndConjugation_of_square e _ _ (inductionTripleFlattening_first_dot J K L hα N)
  have h₂ : inductionEndConjugation (k := k) e
      (transformComponent ((hβ.whiskerLeft J).whiskerRight L) N) =
      (induction L).map (dotEnd K hβ ((induction J).obj N)) :=
    inductionEndConjugation_of_square e _ _ (inductionTripleFlattening_middle_dot J K L hβ N)
  have h₃ : inductionEndConjugation (k := k) e
      (transformComponent (hγ.whiskerLeft (J ⋙ K)) N) =
      dotEnd L hγ ((induction K).obj ((induction J).obj N)) :=
    inductionEndConjugation_of_square e _ _ (inductionTripleFlattening_last_dot J K L hγ N)
  rw [h₁, h₂, h₃] at hp
  exact hp
end Chart
end OddMath.QuiverHecke.ELVOld.BalancedInduction
end

end

section

/-! # Corrected three-path relations under balanced induction

Brundan–Ellis (1.9): transport the literal repeated-outer source coefficient
relation across three possibly different composite functors. This generic
intermediate takes that source coefficient equation explicitly. Concrete
OLD and stored-target actions supply it from the proved quotient relation;
no such premise belongs to the final action field.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u

private theorem corrected_three_linear_comp
    {k C E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    {F₀ F₁ F₂ F₃ : C ⥤ E}
    [F₀.Additive] [F₀.Linear k] [IsSuperfunctor k F₀]
    [F₁.Additive] [F₁.Linear k] [IsSuperfunctor k F₁]
    [F₂.Additive] [F₂.Linear k] [IsSuperfunctor k F₂]
    [F₃.Additive] [F₃.Linear k] [IsSuperfunctor k F₃]
    {p q r : ZMod 2}
    {a : ∀ s, F₀.obj s ⟶ F₁.obj s} {b : ∀ s, F₁.obj s ⟶ F₂.obj s}
    {c : ∀ s, F₂.obj s ⟶ F₃.obj s}
    (ha : IsSupernatural k p a) (hb : IsSupernatural k q b) (hc : IsSupernatural k r c)
    (N : Superfunctor k C (SVec k)) (w : E) :
    transformLinear ha N w ∘ₗ transformLinear hb N w ∘ₗ transformLinear hc N w =
      sign k (p * q + (p + q) * r) • transformLinear ((ha.comp hb).comp hc) N w := by
  rw [← LinearMap.comp_assoc, transformLinear_comp, LinearMap.smul_comp,
    transformLinear_comp, smul_smul, ← sign_add]

private theorem corrected_degree (p q : ZMod 2) : (p * q + p * p) + q * p = p := by
  rcases parity_eq_zero_or_one p with hp | hp <;>
    rcases parity_eq_zero_or_one q with hq | hq <;> rw [hp, hq] <;> decide

private theorem corrected_sign (p q : ZMod 2) :
    (p * q) * (p * p) + (p * q + p * p) * (q * p) = p * q := by
  rcases parity_eq_zero_or_one p with hp | hp <;>
    rcases parity_eq_zero_or_one q with hq | hq <;> rw [hp, hq] <;> decide

private theorem corrected_total
    {k C E : Type u} [CommRing k]
    [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
    {F G : C ⥤ E} [F.Additive] [F.Linear k] [IsSuperfunctor k F]
    [G.Additive] [G.Linear k] [IsSuperfunctor k G]
    {p : ZMod 2} {γ : ∀ s, F.obj s ⟶ G.obj s} (hγ : IsSupernatural k p γ)
    (N : Superfunctor k C (SVec k)) (w : E) :
    (transformComponent hγ N).total w = transformLinear hγ N w := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp only [SuperNatTrans.total, transformComponent_app,
      ite_true, ite_false, zero_ne_one, one_ne_zero, add_zero, zero_add]

private theorem corrected_path_total
    {k C : Type u} [CommRing k] [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
    {M A B : Superfunctor k C (SVec k)}
    (f₀ : M ⟶ A) (f₁ : End A) (f₂ : A ⟶ M)
    (g₀ : M ⟶ B) (g₁ : End B) (g₂ : B ⟶ M) (w : C) :
    (f₀ ≫ (-f₁) ≫ f₂ - g₀ ≫ (-g₁) ≫ g₂).total w =
      f₂.total w ∘ₗ (-f₁.total w) ∘ₗ f₀.total w -
        g₂.total w ∘ₗ (-g₁.total w) ∘ₗ g₀.total w := by
  have hsub {P Q : Superfunctor k C (SVec k)} (f g : P ⟶ Q) :
      (f - g).total w = f.total w - g.total w := by
    simp only [SuperNatTrans.total, Superfunctor.sub_app]
    abel
  have hneg {P Q : Superfunctor k C (SVec k)} (f : P ⟶ Q) :
      (-f).total w = -f.total w := by
    simp only [SuperNatTrans.total, Superfunctor.neg_app, neg_add]
  simp only [hsub, Superfunctor.comp_total, hneg]
  rfl

variable {k C E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (F₀ F₁ F₂ : C ⥤ E)
  [F₀.Additive] [F₀.Linear k] [IsSuperfunctor k F₀]
  [F₁.Additive] [F₁.Linear k] [IsSuperfunctor k F₁]
  [F₂.Additive] [F₂.Linear k] [IsSuperfunctor k F₂]
  {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  (i j : I) {a b c : ∀ s, End (F₀.obj s)}
  (ha : IsSupernatural k (D.parity i) a) (hb : IsSupernatural k (D.parity j) b)
  (hc : IsSupernatural k (D.parity i) c)
  {α₀ : ∀ s, F₀.obj s ⟶ F₂.obj s} {α₁ : ∀ s, F₂.obj s ⟶ F₂.obj s}
  {α₂ : ∀ s, F₂.obj s ⟶ F₀.obj s} {β₀ : ∀ s, F₀.obj s ⟶ F₁.obj s}
  {β₁ : ∀ s, F₁.obj s ⟶ F₁.obj s} {β₂ : ∀ s, F₁.obj s ⟶ F₀.obj s}
  (hα₀ : IsSupernatural k (D.parity i * D.parity j) α₀)
  (hα₁ : IsSupernatural k (D.parity i * D.parity i) α₁)
  (hα₂ : IsSupernatural k (D.parity j * D.parity i) α₂)
  (hβ₀ : IsSupernatural k (D.parity j * D.parity i) β₀)
  (hβ₁ : IsSupernatural k (D.parity i * D.parity i) β₁)
  (hβ₂ : IsSupernatural k (D.parity i * D.parity j) β₂)
  (hsource : ∀ s, (α₀ s ≫ α₁ s ≫ α₂ s) - (β₀ s ≫ β₁ s ≫ β₂ s) =
    tripleDotCorrectionPolynomial D (parameterTwist D Sc) (R := End (F₀.obj s)) i j (c s) (b s) (a s))

include hα₀ hα₁ hα₂ hβ₀ hβ₁ hβ₂ hsource in
private theorem corrected_linear_paths (hij : i ≠ j)
    (N : Superfunctor k C (SVec k)) (w : E) :
    transformLinear hβ₀ N w ∘ₗ (-transformLinear hβ₁ N w) ∘ₗ transformLinear hβ₂ N w -
      transformLinear hα₀ N w ∘ₗ (-transformLinear hα₁ N w) ∘ₗ transformLinear hα₂ N w =
    tripleDotCorrectionPolynomial D Sc i j
      (transformLinear ha N w) (transformLinear hb N w) (transformLinear hc N w) := by
  rw [transformLinear_triplePolynomial_eq F₀ D Sc i j ha hb hc hij N w]
  simp only [LinearMap.comp_neg, LinearMap.neg_comp, neg_sub_neg]
  rw [corrected_three_linear_comp, corrected_three_linear_comp]
  have hdL := corrected_degree (D.parity i) (D.parity j)
  have hdR : (D.parity j * D.parity i + D.parity i * D.parity i) +
      D.parity i * D.parity j = D.parity i := by
    simpa only [mul_comm] using hdL
  have hsL := corrected_sign (D.parity i) (D.parity j)
  have hsR : (D.parity j * D.parity i) * (D.parity i * D.parity i) +
      (D.parity j * D.parity i + D.parity i * D.parity i) * (D.parity i * D.parity j) =
      D.parity i * D.parity j := by
    simpa only [mul_comm] using hsL
  rw [hsL, hsR]
  erw [← smul_sub]
  apply hom_ext
  intro s g z
  rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.sub_apply,
    transformLinear_tensor, transformLinear_tensor, transformLinear_tensor]
  simp only [hdL, hdR]
  change sign k (D.parity i * D.parity j) •
      (inductionEndTensorEval F₀ N w s (twist k (D.parity i) g) z ((α₀ s ≫ α₁ s) ≫ α₂ s) -
        inductionEndTensorEval F₀ N w s (twist k (D.parity i) g) z ((β₀ s ≫ β₁ s) ≫ β₂ s)) = _
  rw [← map_sub]
  have hs := hsource s
  simp only [← Category.assoc] at hs
  rw [hs]
  rfl

include hsource in
/-- The entire corrected induction braid, with its literal source coefficient equation. -/
theorem transformComponent_corrected_braid (hij : i ≠ j)
    (N : Superfunctor k C (SVec k)) :
    (show End (induced F₀ N) from transformComponent hβ₂ N ≫ (-transformComponent hβ₁ N) ≫ transformComponent hβ₀ N) -
      (show End (induced F₀ N) from transformComponent hα₂ N ≫ (-transformComponent hα₁ N) ≫ transformComponent hα₀ N) =
    tripleDotCorrectionPolynomial D Sc (R := End (induced F₀ N)) i j
      (transformComponent ha N) (transformComponent hb N) (transformComponent hc N) := by
  apply OddMath.FiniteSupermodule.hom_ext_total
  intro w
  let ev : End (induced F₀ N) →ₐ[k] Module.End k ((induced F₀ N).obj w) :=
    (svecEndEvaluation ((induced F₀ N).obj w)).comp (supernaturalEndEvaluation (induced F₀ N) w)
  change _ = ev (tripleDotCorrectionPolynomial D Sc (R := End (induced F₀ N)) i j
    (transformComponent ha N) (transformComponent hb N) (transformComponent hc N))
  rw [tripleDotCorrectionPolynomial_map, corrected_path_total]
  change _ = tripleDotCorrectionPolynomial D Sc (R := Module.End k ((induced F₀ N).obj w)) i j
    ((transformComponent ha N).total w) ((transformComponent hb N).total w) ((transformComponent hc N).total w)
  simp only [corrected_total]
  exact corrected_linear_paths F₀ F₁ F₂ D Sc i j ha hb hc
    hα₀ hα₁ hα₂ hβ₀ hβ₁ hβ₂ hsource hij N w

end OddMath.QuiverHecke.ELVOld.BalancedInduction
end

end

section

/-! # The corrected braid on a seven-edge induction grid

Brundan–Ellis (1.9): retain the seven different append edges in the three
repeated-outer orderings. The six independent rectangular/equal crossings
and three independent dots are compared through the chosen triple charts.
The generic intermediate takes the literal source coefficient equation;
concrete stored-target actions must discharge it from the OLD quotient.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u

private theorem grid_three_squares {C : Type*} [Category* C]
    {X₀ X₁ X₂ X₃ Y₀ Y₁ Y₂ Y₃ : C}
    (e₀ : X₀ ⟶ Y₀) (e₁ : X₁ ⟶ Y₁) (e₂ : X₂ ⟶ Y₂) (e₃ : X₃ ⟶ Y₃)
    (a₀ : X₀ ⟶ X₁) (a₁ : X₁ ⟶ X₂) (a₂ : X₂ ⟶ X₃)
    (b₀ : Y₀ ⟶ Y₁) (b₁ : Y₁ ⟶ Y₂) (b₂ : Y₂ ⟶ Y₃)
    (h₀ : a₀ ≫ e₁ = e₀ ≫ b₀) (h₁ : a₁ ≫ e₂ = e₁ ≫ b₁)
    (h₂ : a₂ ≫ e₃ = e₂ ≫ b₂) :
    (a₀ ≫ a₁ ≫ a₂) ≫ e₃ = e₀ ≫ (b₀ ≫ b₁ ≫ b₂) := by
  simp only [Category.assoc]
  rw [h₂, ← Category.assoc a₁, h₁, Category.assoc e₁,
    ← Category.assoc a₀, h₀, Category.assoc]

private theorem grid_negative_square {C : Type*} [Category* C] [Preadditive C]
    {X Y : C} (a : End X) (e : X ⟶ Y) (b : End Y)
    (h : a ≫ e = e ≫ b) : (-a) ≫ e = e ≫ (-b) := by
  rw [Preadditive.neg_comp, Preadditive.comp_neg, h]

private theorem grid_difference_square {C : Type*} [Category* C] [Preadditive C]
    {X Y : C} (a b : End X) (c d : End Y) (e : X ⟶ Y)
    (ha : a ≫ e = e ≫ c) (hb : b ≫ e = e ≫ d) :
    (a - b) ≫ e = e ≫ (c - d) := by
  rw [Preadditive.sub_comp, Preadditive.comp_sub, ha, hb]

variable {k C A B P Q E : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  [Category.{u} P] [Preadditive P] [Linear k P] [Supercategory k P]
  [Category.{u} Q] [Preadditive Q] [Linear k Q] [Supercategory k Q]
  [Category.{u} E] [Preadditive E] [Linear k E] [Supercategory k E]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : C ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  (U : A ⥤ P) [U.Additive] [U.Linear k] [IsSuperfunctor k U]
  (V : A ⥤ Q) [V.Additive] [V.Linear k] [IsSuperfunctor k V]
  (W : B ⥤ Q) [W.Additive] [W.Linear k] [IsSuperfunctor k W]
  (L : P ⥤ E) [L.Additive] [L.Linear k] [IsSuperfunctor k L]
  (M : Q ⥤ E) [M.Additive] [M.Linear k] [IsSuperfunctor k M]
  {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (i j : I)
  {σ : ∀ s, (J ⋙ V).obj s ⟶ (K ⋙ W).obj s}
  {σ' : ∀ s, (K ⋙ W).obj s ⟶ (J ⋙ V).obj s}
  {τ : ∀ s, (J ⋙ U).obj s ⟶ (J ⋙ U).obj s}
  {ρ : ∀ s, (V ⋙ M).obj s ⟶ (U ⋙ L).obj s}
  {ρ' : ∀ s, (U ⋙ L).obj s ⟶ (V ⋙ M).obj s}
  {ξ : ∀ s, (W ⋙ M).obj s ⟶ (W ⋙ M).obj s}
  (hσ : IsSupernatural k (D.parity i * D.parity j) σ)
  (hσ' : IsSupernatural k (D.parity j * D.parity i) σ')
  (hτ : IsSupernatural k (D.parity i * D.parity i) τ)
  (hρ : IsSupernatural k (D.parity j * D.parity i) ρ)
  (hρ' : IsSupernatural k (D.parity i * D.parity j) ρ')
  (hξ : IsSupernatural k (D.parity i * D.parity i) ξ)
local notation "F₀" => (J ⋙ V) ⋙ M
local notation "F₁" => (J ⋙ U) ⋙ L
local notation "F₂" => (K ⋙ W) ⋙ M

/-- The independent paths on all seven grid edges, with the equal crossing negative. -/
def gridMixedBraid (N : Superfunctor k C (SVec k)) :
    End (induced M (induced V (induced J N))) :=
  (show End (induced M (induced V (induced J N))) from
    rectangularCrossComponent U V L M hρ' ((induction J).obj N) ≫
      (-(induction L).map (gridDoubleCrossComponent J U hτ N)) ≫
        rectangularCrossComponent V U M L hρ ((induction J).obj N)) -
  (show End (induced M (induced V (induced J N))) from
    (induction M).map (rectangularCrossComponent K J W V hσ' N) ≫
      (-gridDoubleCrossComponent W M hξ ((induction K).obj N)) ≫
        (induction M).map (rectangularCrossComponent J K V W hσ N))

/-- The direct three-functor source paths for this same grid. -/
def gridDirectMixedBraid (N : Superfunctor k C (SVec k)) : End (induced F₀ N) :=
  (show End (induced F₀ N) from
    transformComponent (hρ'.whiskerLeft J) N ≫
      (-transformComponent (hτ.whiskerRight L) N) ≫ transformComponent (hρ.whiskerLeft J) N) -
  (show End (induced F₀ N) from
    transformComponent (hσ'.whiskerRight M) N ≫
      (-transformComponent (hξ.whiskerLeft K) N) ≫ transformComponent (hσ.whiskerRight M) N)

/-- The six rectangular squares use the three prescribed triple charts. -/
theorem gridMixedBraid_conjugate (N : Superfunctor k C (SVec k)) :
    gridMixedBraid J K U V W L M D i j hσ hσ' hτ hρ hρ' hξ N =
      inductionEndConjugation (k := k) (inductionTripleFlattening J V M N)
        (gridDirectMixedBraid J K U V W L M D i j hσ hσ' hτ hρ hρ' hξ N) := by
  let e := inductionTripleFlattening J V M N
  let eR := inductionTripleFlattening J U L N
  let eL := inductionTripleFlattening K W M N
  have hR := grid_three_squares e.hom eR.hom eR.hom e.hom
    (rectangularCrossComponent U V L M hρ' ((induction J).obj N))
    (-(induction L).map (gridDoubleCrossComponent J U hτ N))
    (rectangularCrossComponent V U M L hρ ((induction J).obj N))
    (transformComponent (hρ'.whiskerLeft J) N) (-transformComponent (hτ.whiskerRight L) N)
    (transformComponent (hρ.whiskerLeft J) N)
    (inductionTripleFlattening_suffix_rectangular J V M U L hρ' N)
    (grid_negative_square _ _ _ (inductionTripleFlattening_prefix_rectangular J U J U L hτ N))
    (inductionTripleFlattening_suffix_rectangular J U L V M hρ N)
  have hL := grid_three_squares e.hom eL.hom eL.hom e.hom
    ((induction M).map (rectangularCrossComponent K J W V hσ' N))
    (-gridDoubleCrossComponent W M hξ ((induction K).obj N))
    ((induction M).map (rectangularCrossComponent J K V W hσ N))
    (transformComponent (hσ'.whiskerRight M) N) (-transformComponent (hξ.whiskerLeft K) N)
    (transformComponent (hσ.whiskerRight M) N)
    (inductionTripleFlattening_prefix_rectangular J V K W M hσ' N)
    (grid_negative_square _ _ _ (inductionTripleFlattening_suffix_rectangular K W M W M hξ N))
    (inductionTripleFlattening_prefix_rectangular K W J V M hσ N)
  have hrow : gridMixedBraid J K U V W L M D i j hσ hσ' hτ hρ hρ' hξ N ≫ e.hom =
      e.hom ≫ gridDirectMixedBraid J K U V W L M D i j hσ hσ' hτ hρ hρ' hξ N :=
    grid_difference_square _ _ _ _ _ hR hL
  exact (inductionEndConjugation_of_square e _ _ hrow).symm

variable {α : ∀ s, End (J.obj s)} {β : ∀ s, End (V.obj s)} {γ : ∀ s, End (M.obj s)}
  (hα : IsSupernatural k (D.parity i) α) (hβ : IsSupernatural k (D.parity j) β)
  (hγ : IsSupernatural k (D.parity i) γ)

/-- The whole grid correction, with the literal source equation exposed at this generic intermediate. -/
theorem gridMixedBraid_polynomial (hij : i ≠ j)
    (hsource : ∀ s,
      (show End ((F₀).obj s) from M.map (σ s) ≫ ξ (K.obj s) ≫ M.map (σ' s)) -
      (show End ((F₀).obj s) from ρ (J.obj s) ≫ L.map (τ s) ≫ ρ' (J.obj s)) =
        tripleDotCorrectionPolynomial D (parameterTwist D Sc) (R := End ((F₀).obj s)) i j
          (γ ((J ⋙ V).obj s)) (M.map (β (J.obj s))) (M.map (V.map (α s))))
    (N : Superfunctor k C (SVec k)) :
    gridMixedBraid J K U V W L M D i j hσ hσ' hτ hρ hρ' hξ N =
      tripleDotCorrectionPolynomial D Sc (R := End (induced M (induced V (induced J N)))) i j
        ((induction M).map ((induction V).map (dotEnd J hα N)))
        ((induction M).map (dotEnd V hβ ((induction J).obj N)))
        (dotEnd M hγ ((induction V).obj ((induction J).obj N))) := by
  have hd := transformComponent_corrected_braid F₀ F₁ F₂ D Sc i j
    ((hα.whiskerRight V).whiskerRight M) ((hβ.whiskerLeft J).whiskerRight M)
    (hγ.whiskerLeft (J ⋙ V))
    (hσ.whiskerRight M) (hξ.whiskerLeft K) (hσ'.whiskerRight M)
    (hρ.whiskerLeft J) (hτ.whiskerRight L) (hρ'.whiskerLeft J) hsource hij N
  have hp := transformComponent_triplePolynomial F₀ D Sc i j
    ((hα.whiskerRight V).whiskerRight M) ((hβ.whiskerLeft J).whiskerRight M)
    (hγ.whiskerLeft (J ⋙ V)) hij N
  have ht := inductionTripleFlattening_polynomial D Sc i j J V M hα hβ hγ hij N
  rw [gridMixedBraid_conjugate]
  change inductionEndConjugation (k := k) (inductionTripleFlattening J V M N) _ = _
  rw [show gridDirectMixedBraid J K U V W L M D i j hσ hσ' hτ hρ hρ' hξ N = _ from hd, hp]
  exact ht.symm

end OddMath.QuiverHecke.ELVOld.BalancedInduction
end

end

section

/-! # The signed grid mate as a rectangular mate

Brundan–Ellis (1.13)–(1.14): the diagonal ordinary cup-crossing-cap is
the rectangular mate of the negative crossing. This identifies the
prescribed diagonal fields with the full-inclusion comparison theorem.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld.BalancedInduction
universe u
private theorem coend_ext
    {k C A V : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive A] [Linear k A] [AddCommMonoid V] [Module k V]
    (J : C ⥤ A) (M : C ⥤ SVec k) {w : A}
    {f g : Obj J M w →ₗ[k] V}
    (h : ∀ s (a : J.obj s ⟶ w) (b : M.obj s),
      f (tensor J M s a b) = g (tensor J M s a b)) : f = g := by
  classical
  apply LinearMap.cancel_right (Submodule.mkQ_surjective (relations J M w)) |>.mp
  apply DirectSum.linearMap_ext
  intro s
  apply TensorProduct.ext
  ext a b
  exact h s a b

variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {p : ZMod 2} {α : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
  (hα : IsSupernatural k p α)

omit [Preadditive A] [Linear k A] [Supercategory k A]
  [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  [K.Additive] [K.Linear k] [IsSuperfunctor k K] in
private theorem negativeFamily (hx : IsSupernatural k p α) : IsSupernatural k p (fun s => -α s) where
  mem s := neg_mem (hx.mem s)
  naturality hf := by
    rw [Preadditive.comp_neg, hx.naturality hf, Preadditive.neg_comp, smul_neg]

/-- The prescribed whole grid mate is the rectangular mate of the negative crossing. -/
theorem rectangularMate_negative_eq_grid (N : Superfunctor k A (SVec k)) (t : A) :
    orderedRectangularMateLinear J J K K (negativeFamily J K hα) N t =
      orderedGridMateLinear J K hα N t := by
  apply coend_ext _ _
  intro s g b
  rw [orderedRectangularMateLinear_tensor, orderedGridMateLinear_tensor, Preadditive.neg_comp]

/-- Changing the degree by its equality changes no prescribed grid mate map. -/
theorem gridMateLinear_degree_eq {r : ZMod 2} (hp : p = r)
    (hr : IsSupernatural k r α) (N : Superfunctor k A (SVec k)) (t : A) :
    orderedGridMateLinear J K hα N t = orderedGridMateLinear J K hr N t := by
  cases hp
  rfl

end OddMath.QuiverHecke.ELVOld.BalancedInduction

namespace OddMath.QuiverHecke.ELVOld
open BalancedInduction
universe u
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
  (A : C ⥤ C) [A.Additive] [A.Linear k] [IsSuperfunctor k A]
  {p : ZMod 2} {α : ∀ s, (A ⋙ A).obj s ⟶ (A ⋙ A).obj s}
  (hα : IsSupernatural k p α)

omit [A.Additive] [A.Linear k] [IsSuperfunctor k A] in
private theorem negativeFamily (hx : IsSupernatural k p α) : IsSupernatural k p (fun s => -α s) where
  mem s := neg_mem (hx.mem s)
  naturality hf := by
    rw [Preadditive.comp_neg, hx.naturality hf, Preadditive.neg_comp, smul_neg]

/-- The negative-crossing ordinary mixed mate is the prescribed global diagonal mate. -/
theorem mixedMate_negative_eq_ordered (N : Superfunctor k C (SVec k)) (t : C) :
    orderedMixedMateCoend A A (negativeFamily A hα) N t =
      orderedMateLinear A hα N t := by
  apply coend_ext _ _
  intro s g b
  have hL := orderedMixedMateCoend_tensor A A (negativeFamily A hα) N s t g b
  have hs : tensor A (A ⋙ N.toFunctor) s g b =
      tensor A ((restriction A).obj N).toFunctor s g b := rfl
  have hR := congrArg (orderedMateLinear A hα N t) hs
  have hR₂ := orderedMateLinear_tensor A hα N s t g b
  have hn : tensor A N.toFunctor (A.obj s) ((-α s) ≫ twist k p (A.map g)) b =
      -tensor A N.toFunctor (A.obj s) (α s ≫ twist k p (A.map g)) b := by
    rw [Preadditive.neg_comp]
    change inclusion A N.toFunctor (A.obj t) (A.obj s)
      ((-(α s ≫ twist k p (A.map g))) ⊗ₜ[k] b) = _
    rw [TensorProduct.neg_tmul, map_neg]
    rfl
  exact hL.trans (hn.trans (hR.trans hR₂).symm)

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # The normalized rectangular mate is the prescribed grid mate

BE (1.13)–(1.14): promote the signed coend comparison to the whole module
morphism and retain independently stored successor content certificates.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
namespace BalancedInduction
universe u
variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
  {p : ZMod 2} {α : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
  (hα : IsSupernatural k p α)

/-- The signed comparison retains the whole prescribed module morphism. -/
theorem rectangularMate_negative_component
    (hNeg : IsSupernatural k p (fun s => -α s))
    (N : Superfunctor k A (SVec k)) :
    orderedRectangularMateComponent J J K K hNeg N = orderedGridMateComponent J K hα N := by
  apply OddMath.FiniteSupermodule.hom_ext_total (k := k)
  intro t
  have h := rectangularMate_negative_eq_grid J K hα N t
  dsimp only [orderedRectangularMateLinear, orderedGridMateLinear] at h
  exact h

private theorem rectangularMate_component_eq
    {β : ∀ s, (J ⋙ K).obj s ⟶ (J ⋙ K).obj s}
    (hβ : IsSupernatural k p β) (hab : α = β) (N : Superfunctor k A (SVec k)) :
    orderedRectangularMateComponent J J K K hα N =
      orderedRectangularMateComponent J J K K hβ N := by
  cases hab
  rfl

/-- Equal degrees give the same given grid mate module morphism. -/
theorem gridMateComponent_degree_eq {q : ZMod 2} (hpq : p = q)
    (hq : IsSupernatural k q α) (N : Superfunctor k A (SVec k)) :
    orderedGridMateComponent J K hα N = orderedGridMateComponent J K hq N := by
  cases hpq
  rfl

end BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β δ γ : Multiset I) (i : I)
  (hδ : β + ([i] : Multiset I) = δ) (hγ : δ + ([i] : Multiset I) = γ)
local notation "J" => contentAppendTo D Sc cutoff N β [i] δ hδ
local notation "K" => contentAppendTo D Sc cutoff N δ [i] γ hγ
local notation "hRaw" => contentDistinctTargetsCross_supernatural D Sc cutoff N β i i δ δ γ hδ hδ hγ hγ
local notation "hNorm" => normalizedContentTargetsCross_supernatural D Sc cutoff N β i i δ δ γ hδ hδ hγ hγ

/-- The prescribed stored-content equal-colour crossing has the matrix parity. -/
theorem contentTargetsGridCross_supernatural :
    IsSupernatural k (D.parity i)
      (contentDistinctTargetsCross D Sc cutoff N β i i δ δ γ hδ hδ hγ hγ) :=
  (SKM.zmod2_mul_self (D.parity i)) ▸ hRaw

/-- The negative normalized rectangular mate is the exact matrix grid mate,
including its rank-one degree and all stored successor contents. -/
theorem normalizedContentTargetsMate_eq_grid
    (M : ContentModules D Sc cutoff N δ) :
    BalancedInduction.orderedRectangularMateComponent J J K K hNorm M =
      BalancedInduction.orderedGridMateComponent J K
        (contentTargetsGridCross_supernatural D Sc cutoff N β δ γ i hδ hγ) M := by
  have hn : normalizedContentTargetsCross D Sc cutoff N β i i δ δ γ hδ hδ hγ hγ =
      fun s => -contentDistinctTargetsCross D Sc cutoff N β i i δ δ γ hδ hδ hγ hγ s := by
    funext s
    simp only [normalizedContentTargetsCross, ite_true]
  have hNeg : IsSupernatural k (D.parity i * D.parity i)
      (fun s => -contentDistinctTargetsCross D Sc cutoff N β i i δ δ γ hδ hδ hγ hγ s) :=
    hn ▸ hNorm
  have h := BalancedInduction.rectangularMate_negative_component J K hRaw hNeg M
  have he := BalancedInduction.gridMateComponent_degree_eq J K hRaw
    (SKM.zmod2_mul_self (D.parity i))
    (contentTargetsGridCross_supernatural D Sc cutoff N β δ γ i hδ hγ) M
  have hc := BalancedInduction.rectangularMate_component_eq J K hNorm hNeg hn M
  exact hc.trans (h.trans he)

end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Induction of content representables

The balanced append induction of `Hom(v,-)` is represented by the appended
word. The comparison composes the appended source arrow with the tensor's
first factor; its inverse inserts the identity of `v`. This supplies the
representable step in the vacuum word construction, without local inverses.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)
  (β : Multiset I) (σ : List I)

namespace InductionRepresentable
local notation "J" => contentAppend D Sc cutoff N β σ
local notation "H" v => contentRepresentableFunctor D Sc cutoff N β v
variable (v : ContentCategory D Sc cutoff N β)

/-- Composition on an unbalanced tensor summand. -/
def pairing (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I)))
    (z : ContentCategory D Sc cutoff N β) :
    ((J).obj z ⟶ w) ⊗[k] (H v).obj z →ₗ[k] ((J).obj v ⟶ w) :=
  TensorProduct.lift {
    toFun := fun h => {
      toFun := fun g => (J).map g ≫ h
      map_add' := by
        intro g g'
        change v ⟶ z at g g'
        change (J).map (g + g') ≫ h = (J).map g ≫ h + (J).map g' ≫ h
        rw [Functor.map_add, Preadditive.add_comp]
      map_smul' := by
        intro r g
        change v ⟶ z at g
        change (J).map (r • g) ≫ h = r • ((J).map g ≫ h)
        rw [Functor.map_smul, Linear.smul_comp] }
    map_add' := by
      intro h h'
      apply LinearMap.ext
      intro g
      exact Preadditive.comp_add ((J).obj v) ((J).obj z) w ((J).map g) h h'
    map_smul' := by
      intro r h
      apply LinearMap.ext
      intro g
      exact Linear.comp_smul ((J).obj v) ((J).obj z) w ((J).map g) r h }

/-- The forward map on the actual balanced quotient. -/
def forward (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I))) :
    BalancedInduction.Obj J (H v) w →ₗ[k] ((J).obj v ⟶ w) :=
  BalancedInduction.lift J (H v) w (pairing D Sc cutoff N β σ v w) (by
    intro z z' f h g
    change v ⟶ z at g
    change (J).map g ≫ ((J).map f ≫ h) = (J).map (g ≫ f) ≫ h
    rw [Functor.map_comp, Category.assoc])

@[simp] theorem forward_tensor (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I)))
    (z : ContentCategory D Sc cutoff N β) (h : (J).obj z ⟶ w) (g : v ⟶ z) :
    forward D Sc cutoff N β σ v w (BalancedInduction.tensor J (H v) z h g) =
      (J).map g ≫ h := by
  exact BalancedInduction.lift_tensor J (H v) w
    (pairing D Sc cutoff N β σ v w) _ z h g

/-- The inverse inserts the identity at the representing source object. -/
def backward (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I))) :
    ((J).obj v ⟶ w) →ₗ[k] BalancedInduction.Obj J (H v) w :=
  BalancedInduction.inclusion J (H v) w v ∘ₗ
    (TensorProduct.mk k ((J).obj v ⟶ w) ((H v).obj v)).flip (𝟙 v)

@[simp] theorem backward_apply (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I)))
    (h : (J).obj v ⟶ w) :
    backward D Sc cutoff N β σ v w h = BalancedInduction.tensor J (H v) v h (𝟙 v) := rfl

theorem forward_backward (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I))) :
    forward D Sc cutoff N β σ v w ∘ₗ backward D Sc cutoff N β σ v w = LinearMap.id := by
  ext h
  simp

theorem backward_forward (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I))) :
    backward D Sc cutoff N β σ v w ∘ₗ forward D Sc cutoff N β σ v w = LinearMap.id := by
  apply BalancedInduction.hom_ext
  intro z h g
  change v ⟶ z at g
  change backward D Sc cutoff N β σ v w
    (forward D Sc cutoff N β σ v w (BalancedInduction.tensor J (H v) z h g)) = _
  rw [forward_tensor, backward_apply]
  have hb := BalancedInduction.balance J (H v) g h (𝟙 v)
  change BalancedInduction.tensor J (H v) v ((J).map g ≫ h) (𝟙 v) =
    BalancedInduction.tensor J (H v) z h (𝟙 v ≫ g) at hb
  dsimp only [LinearMap.id_apply]
  simpa only [Category.id_comp] using hb

/-- Objectwise comparison, with both quotient roundtrips. -/
def equiv (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I))) :
    BalancedInduction.Obj J (H v) w ≃ₗ[k] ((J).obj v ⟶ w) :=
  LinearEquiv.ofLinearMap (forward D Sc cutoff N β σ v w)
    (backward D Sc cutoff N β σ v w) (forward_backward D Sc cutoff N β σ v w)
    (backward_forward D Sc cutoff N β σ v w)

theorem forward_naturality {w z : ContentCategory D Sc cutoff N (β + (σ : Multiset I))}
    (a : w ⟶ z) :
    forward D Sc cutoff N β σ v z ∘ₗ BalancedInduction.postcompose J (H v) a =
      (contentRepresentableFunctor D Sc cutoff N (β + (σ : Multiset I)) ((J).obj v)).map a ∘ₗ
        forward D Sc cutoff N β σ v w := by
  apply BalancedInduction.hom_ext
  intro t h g
  change v ⟶ t at g
  change forward D Sc cutoff N β σ v z
    (BalancedInduction.postcompose J (H v) a (BalancedInduction.tensor J (H v) t h g)) =
      forward D Sc cutoff N β σ v w (BalancedInduction.tensor J (H v) t h g) ≫ a
  calc
    _ = forward D Sc cutoff N β σ v z (BalancedInduction.tensor J (H v) t (h ≫ a) g) :=
      congrArg (forward D Sc cutoff N β σ v z)
        (BalancedInduction.postcompose_tensor J (H v) a t h g)
    _ = _ := by rw [forward_tensor, forward_tensor, Category.assoc]

theorem backward_naturality {w z : ContentCategory D Sc cutoff N (β + (σ : Multiset I))}
    (a : w ⟶ z) :
    backward D Sc cutoff N β σ v z ∘ₗ
      (contentRepresentableFunctor D Sc cutoff N (β + (σ : Multiset I)) ((J).obj v)).map a =
      BalancedInduction.postcompose J (H v) a ∘ₗ backward D Sc cutoff N β σ v w := by
  apply LinearMap.ext
  intro h
  exact (BalancedInduction.postcompose_tensor J (H v) a v h (𝟙 v)).symm

/-- Inserting the even identity preserves total parity. -/
theorem backward_mem (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I))) :
    (backward D Sc cutoff N β σ v w :
      contentHomSpace D Sc cutoff N (β + (σ : Multiset I)) ((J).obj v) w ⟶
        BalancedInduction.superspace J (H v) w) ∈ parity (R := k)
      (contentHomSpace D Sc cutoff N (β + (σ : Multiset I)) ((J).obj v) w)
      (BalancedInduction.superspace J (H v) w) 0 := by
  change ∀ q, backward D Sc cutoff N β σ v w ∘ₗ
      (contentHomSpace D Sc cutoff N (β + (σ : Multiset I)) ((J).obj v) w).proj q =
    (BalancedInduction.superspace J (H v) w).proj (q + 0) ∘ₗ
      backward D Sc cutoff N β σ v w
  intro q
  apply LinearMap.ext
  intro h
  change (J).obj v ⟶ w at h
  change BalancedInduction.tensor J (H v) v
      ((contentHomSpace D Sc cutoff N (β + (σ : Multiset I)) ((J).obj v) w).proj q h) (𝟙 v) =
    (BalancedInduction.superspace J (H v) w).proj (q + 0)
      (BalancedInduction.tensor J (H v) v h (𝟙 v))
  rw [add_zero]
  have hp := BalancedInduction.proj_tensor J (H v) w q v h (𝟙 v)
  rw [hp]
  have hid0 : ((H v).obj v).proj 0 (𝟙 v) = 𝟙 v := by
    change 𝟙 v - proj k 1 (𝟙 v) = 𝟙 v
    simp [proj_id]
  have hid1 : ((H v).obj v).proj 1 (𝟙 v) = 0 := by
    change proj k 1 (𝟙 v) = 0
    simp only [proj_id, one_ne_zero, ↓reduceIte]
  rw [hid0, hid1, BalancedInduction.tensor_zero_right, add_zero]
  congr 1
  rcases parity_eq_zero_or_one q with rfl | rfl
  · change h - proj k 1 h = proj k 0 h
    exact eq_sub_iff_add_eq.mpr (proj_add_proj h) |>.symm
  · rfl

/-- The forward quotient map is even, including both odd tensor factors. -/
theorem forward_mem (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I))) :
    (forward D Sc cutoff N β σ v w : BalancedInduction.superspace J (H v) w ⟶
      contentHomSpace D Sc cutoff N (β + (σ : Multiset I)) ((J).obj v) w) ∈
      parity (R := k) (BalancedInduction.superspace J (H v) w)
        (contentHomSpace D Sc cutoff N (β + (σ : Multiset I)) ((J).obj v) w) 0 := by
  have hb := backward_mem D Sc cutoff N β σ v w
  change ∀ q, _ at hb ⊢
  intro q
  apply LinearMap.ext
  intro x
  apply (equiv D Sc cutoff N β σ v w).symm.injective
  have h := congrArg (fun f => f (forward D Sc cutoff N β σ v w x)) (hb q)
  change backward D Sc cutoff N β σ v w
      ((contentHomSpace D Sc cutoff N (β + (σ : Multiset I)) ((J).obj v) w).proj q
        (forward D Sc cutoff N β σ v w x)) =
    (BalancedInduction.superspace J (H v) w).proj (q + 0)
      (backward D Sc cutoff N β σ v w (forward D Sc cutoff N β σ v w x)) at h
  have hr (y) : backward D Sc cutoff N β σ v w (forward D Sc cutoff N β σ v w y) = y :=
    congrArg (fun f => f y) (backward_forward D Sc cutoff N β σ v w)
  change backward D Sc cutoff N β σ v w (forward D Sc cutoff N β σ v w
      ((BalancedInduction.superspace J (H v) w).proj q x)) =
    backward D Sc cutoff N β σ v w
      ((contentHomSpace D Sc cutoff N (β + (σ : Multiset I)) ((J).obj v) w).proj (q + 0)
        (forward D Sc cutoff N β σ v w x))
  simpa only [hr, add_zero] using h.symm

/-- The even forward supernatural transformation. -/
def forwardTransform :
    (contentInduction D Sc cutoff N β σ).obj (contentRepresentable D Sc cutoff N β v) ⟶
      contentRepresentable D Sc cutoff N (β + (σ : Multiset I)) ((J).obj v) :=
  Superfunctor.homMk (IsSupernatural.toSuperNatTrans (p := 0)
    (x := forward D Sc cutoff N β σ v) {
      mem := forward_mem D Sc cutoff N β σ v
      naturality := by
        intro w z q a ha
        simp only [zero_mul, Supercategory.sign_zero, one_smul]
        exact forward_naturality D Sc cutoff N β σ v a })

/-- The even inverse supernatural transformation. -/
def backwardTransform :
    contentRepresentable D Sc cutoff N (β + (σ : Multiset I)) ((J).obj v) ⟶
      (contentInduction D Sc cutoff N β σ).obj (contentRepresentable D Sc cutoff N β v) :=
  Superfunctor.homMk (IsSupernatural.toSuperNatTrans (p := 0)
    (x := backward D Sc cutoff N β σ v) {
      mem := backward_mem D Sc cutoff N β σ v
      naturality := by
        intro w z q a ha
        simp only [zero_mul, Supercategory.sign_zero, one_smul]
        exact backward_naturality D Sc cutoff N β σ v a })

@[simp] theorem forwardTransform_app (p : ZMod 2)
    (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I))) :
    (forwardTransform D Sc cutoff N β σ v).app p w =
      if p = 0 then forward D Sc cutoff N β σ v w else 0 := rfl

@[simp] theorem backwardTransform_app (p : ZMod 2)
    (w : ContentCategory D Sc cutoff N (β + (σ : Multiset I))) :
    (backwardTransform D Sc cutoff N β σ v).app p w =
      if p = 0 then backward D Sc cutoff N β σ v w else 0 := rfl

/-- Append induction of the covariant content representable is represented by
its appended word. Both maps are even and natural against every target arrow. -/
def iso :
    (contentInduction D Sc cutoff N β σ).obj (contentRepresentable D Sc cutoff N β v) ≅
      contentRepresentable D Sc cutoff N (β + (σ : Multiset I)) ((J).obj v) where
  hom := forwardTransform D Sc cutoff N β σ v
  inv := backwardTransform D Sc cutoff N β σ v
  hom_inv_id := by
    apply Superfunctor.hom_ext
    intro p w
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      simp only [Superfunctor.comp_app, forwardTransform_app, backwardTransform_app,
        Superfunctor.id_app_zero, Superfunctor.id_app_one, ↓reduceIte, zero_add, one_ne_zero,
        SVec.zmod2_one_add_one]
    · change backward D Sc cutoff N β σ v w ∘ₗ forward D Sc cutoff N β σ v w +
        (0 : BalancedInduction.Obj J (H v) w →ₗ[k] BalancedInduction.Obj J (H v) w) = LinearMap.id
      rw [add_zero, backward_forward]
    · apply LinearMap.ext
      intro x
      change 0 + backward D Sc cutoff N β σ v w 0 = 0
      rw [map_zero, add_zero]
  inv_hom_id := by
    apply Superfunctor.hom_ext
    intro p w
    rcases parity_eq_zero_or_one p with rfl | rfl <;>
      simp only [Superfunctor.comp_app, forwardTransform_app, backwardTransform_app,
        Superfunctor.id_app_zero, Superfunctor.id_app_one, ↓reduceIte, zero_add, one_ne_zero,
        SVec.zmod2_one_add_one]
    · change forward D Sc cutoff N β σ v w ∘ₗ backward D Sc cutoff N β σ v w +
        (0 : ((J).obj v ⟶ w) →ₗ[k] ((J).obj v ⟶ w)) = LinearMap.id
      rw [add_zero, forward_backward]
    · change (0 : ((J).obj v ⟶ w) →ₗ[k] ((J).obj v ⟶ w)) = 0
      rfl

end InductionRepresentable
end OddMath.QuiverHecke.ELVOld
end

end

section

/-! # Representable vacuum words

The initial vacuum is the actual empty-word representable of the
coefficient-truncated full ELV category. Iterating the constructed one-colour
induction functors represents the appended word, without a local inverse.
Lists of induction operators are written with the outermost operator first;
the represented word is therefore their reversal.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ)

/-- Rank-zero object; its endomorphisms retain the full coefficient truncation. -/
def vacuumObject : ContentCategory D Sc cutoff N 0 := ⟨⟨[]⟩, rfl⟩

/-- The actual rank-zero representable, not a prescribed polynomial quotient. -/
def vacuumModule : ContentModules D Sc cutoff N 0 :=
  contentRepresentable D Sc cutoff N 0 (vacuumObject D Sc cutoff N)

namespace VacuumRepresentable

/-- Exact content after applying operators from right to left. -/
def content : List I → Multiset I
  | [] => 0
  | i :: σ => content σ + ([i] : List I)

/-- The represented object of an iterated induction word. -/
def wordObject : (σ : List I) → ContentCategory D Sc cutoff N (content σ)
  | [] => vacuumObject D Sc cutoff N
  | i :: σ => (contentAppend D Sc cutoff N (content σ) [i]).obj (wordObject σ)

theorem wordObject_word (σ : List I) : (wordObject D Sc cutoff N σ).obj.word = σ.reverse := by
  induction σ with
  | nil => rfl
  | cons i σ ih =>
    change (wordObject D Sc cutoff N σ).obj.word ++ [i] = (i :: σ).reverse
    rw [ih, List.reverse_cons]

end VacuumRepresentable
end OddMath.QuiverHecke.ELVOld
end

end
