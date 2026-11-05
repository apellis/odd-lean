import OddMath.QuiverHecke.CyclotomicAction.ELVWeightTensorVacuum
import OddMath.QuiverHecke.CyclotomicAction.ELVPowerWordCoefficients
import OddMath.QuiverHecke.CyclotomicAction.ELVEndEvaluation
import OddMath.QuiverHecke.CyclotomicAction.ELVTensorReservoirWords

/-! # Coefficient maps on the tensor-vacuum input

SwappedVacuumCoordinates §§2–6: coefficients act on the reservoir factor
of the entire tensor-vacuum functor, before evaluation at a regular probe.
The action retains both supernatural parities and the original ordered
coefficient algebra. Postcomposition on word Homs preserves that order.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld.VacuumTensorCoefficientMaps
universe u
private theorem total_add {k : Type*} [CommRing k] {B E : Type*}
    [Category* B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category* E] [Preadditive E] [Linear k E] [Supercategory k E]
    {F G : Superfunctor k B E} (f g : F ⟶ G) (b : B) :
    (f + g).total b = f.total b + g.total b :=
  (supernaturalTotalLinearMap F G b).map_add f g
private theorem total_smul {k : Type*} [CommRing k] {B E : Type*}
    [Category* B] [Preadditive B] [Linear k B] [Supercategory k B]
    [Category* E] [Preadditive E] [Linear k E] [Supercategory k E]
    {F G : Superfunctor k B E} (r : k) (f : F ⟶ G) (b : B) :
    (r • f).total b = r • f.total b :=
  (supernaturalTotalLinearMap F G b).map_smul r f
section Tensor
variable {k A C : Type u} [CommRing k]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]

private def tensorMap {W W' : Superfunctor k C (SVec k)} (f : W ⟶ W') (V : SVec k) :
    VacuumTensor.object W V ⟶ VacuumTensor.object W' V :=
  Superfunctor.whiskerRight f ⟨VacuumTensor.rightFunctor V⟩

private theorem tensorMap_total {W W' : Superfunctor k C (SVec k)}
    (f : W ⟶ W') (V : SVec k) (c : C) :
    (tensorMap f V).total c = SVec.whiskerRight (f.total c) V := by
  change SVec.whiskerRight (f.app 0 c) V + SVec.whiskerRight (f.app 1 c) V = _
  exact (SVec.whiskerRight_add _ _ V).symm

/-- A reservoir map acts on the first tensor factor at every probe module. -/
def reservoirMap {W W' : Superfunctor k C (SVec k)} (a : A) (f : W ⟶ W') :
    VacuumTensor.superfunctor W a ⟶ VacuumTensor.superfunctor W' a where
  app p M := tensorMap (proj k p f) (M.obj a)
  app_mem p M := Superfunctor.whiskerRight_mem (proj_mem p f) _
  naturality p M N q g hg := by
    apply OddMath.HomogeneousSuperfunctorIso.total_ext
    intro c
    rw [Superfunctor.comp_total]
    change (VacuumTensor.map W a g).total c ≫
        (tensorMap (proj k p f) (N.obj a)).total c =
      (koszulSign p q • (tensorMap (proj k p f) (M.obj a) ≫
        VacuumTensor.map W' a g)).total c
    rw [koszulSign_smul (R := k), total_smul, Superfunctor.comp_total, tensorMap_total, tensorMap_total,
      show (VacuumTensor.map W a g).total c = SVec.whiskerLeft (W.obj c) (g.total a) from
        VacuumTensor.superfunctor_map_total W a g c,
      show (VacuumTensor.map W' a g).total c = SVec.whiskerLeft (W'.obj c) (g.total a) from
        VacuumTensor.superfunctor_map_total W' a g c,
      OddMath.HomogeneousSuperfunctorIso.total_eq_app g hg a,
      OddMath.HomogeneousSuperfunctorIso.total_eq_app (proj k p f) (proj_mem p f) c]
    have h := SVec.super_interchange ((proj k p f).app_mem p c) (g.app_mem q a)
    have h' := congrArg (fun z => koszulSign p q • z) h
    rw [koszulSign_smul_smul] at h'
    simpa only [koszulSign_smul (R := k)] using h'.symm

/-- The total map is literal first-factor tensoring, for arbitrary maps. -/
theorem reservoirMap_total {W W' : Superfunctor k C (SVec k)}
    (a : A) (f : W ⟶ W') (M : Superfunctor k A (SVec k)) (c : C) :
    ((reservoirMap a f).total M).total c = SVec.whiskerRight (f.total c) (M.obj a) := by
  change ((tensorMap (proj k 0 f) (M.obj a)) + tensorMap (proj k 1 f) (M.obj a)).total c = _
  rw [total_add, tensorMap_total, tensorMap_total, ← SVec.whiskerRight_add,
    ← total_add, proj_add_proj]

private theorem tensorMap_eq_square {W : Superfunctor k C (SVec k)}
    (f : End W) (a : A) {M M' : Superfunctor k A (SVec k)} (h : M = M') :
    tensorMap f (M.obj a) ≫ eqToHom (congrArg (fun T => VacuumTensor.object W (T.obj a)) h) =
      eqToHom (congrArg (fun T => VacuumTensor.object W (T.obj a)) h) ≫ tensorMap f (M'.obj a) := by
  subst M'
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

private theorem tensorMap_scalar_square {W : Superfunctor k C (SVec k)}
    (f : End W) (V : SVec k) (e : V ≃ₗ[k] k)
    (he : SVec.ofHom e.toLinearMap ∈ parity (R := k) V SVec.unit 0) :
    tensorMap f V ≫ (VacuumTensor.scalarTensorIso W V e he).hom =
      (VacuumTensor.scalarTensorIso W V e he).hom ≫ f := by
  apply OddMath.HomogeneousSuperfunctorIso.total_ext
  intro c
  rw [Superfunctor.comp_total, Superfunctor.comp_total, tensorMap_total]
  apply TensorProduct.ext'
  intro v w
  change (VacuumTensor.scalarTensorIso W V e he).hom.total c
      (SVec.whiskerRight (f.total c) V (v ⊗ₜ[k] w)) =
    f.total c ((VacuumTensor.scalarTensorIso W V e he).hom.total c (v ⊗ₜ[k] w))
  rw [SVec.whiskerRight_tmul, VacuumTensor.scalarTensorIso_hom_tmul,
    VacuumTensor.scalarTensorIso_hom_tmul, map_smul]

/-- Tensoring the reservoir factor preserves the endomorphism algebra. -/
def reservoirEndAction (W : Superfunctor k C (SVec k)) (a : A) :
    End W →ₐ[k] End (VacuumTensor.superfunctor W a) :=
  AlgHom.ofLinearMap
    { toFun := reservoirMap a
      map_add' := by
        intro f g
        apply Superfunctor.hom_ext
        intro p M
        change tensorMap (proj k p (f + g)) (M.obj a) =
          tensorMap (proj k p f) (M.obj a) + tensorMap (proj k p g) (M.obj a)
        rw [map_add]
        exact Superfunctor.add_whiskerRight _ _ _
      map_smul' := by
        intro r f
        apply Superfunctor.hom_ext
        intro p M
        change tensorMap (proj k p (r • f)) (M.obj a) =
          r • tensorMap (proj k p f) (M.obj a)
        rw [map_smul]
        exact Superfunctor.smul_whiskerRight _ _ _ }
    (by
      apply OddMath.HomogeneousSuperfunctorIso.total_ext
      intro M
      apply OddMath.HomogeneousSuperfunctorIso.total_ext
      intro c
      change ((reservoirMap a (𝟙 W)).total M).total c = ((𝟙 _ : End (VacuumTensor.superfunctor W a)).total M).total c
      rw [reservoirMap_total]
      simp only [SuperNatTrans.total, Superfunctor.id_app_zero, Superfunctor.id_app_one, add_zero]
      exact SVec.whiskerRight_id _ _)
    (by
      intro f g
      apply OddMath.HomogeneousSuperfunctorIso.total_ext
      intro M
      apply OddMath.HomogeneousSuperfunctorIso.total_ext
      intro c
      change ((reservoirMap a (g ≫ f)).total M).total c =
        ((reservoirMap a g ≫ reservoirMap a f).total M).total c
      rw [Superfunctor.comp_total, Superfunctor.comp_total,
        reservoirMap_total, reservoirMap_total, reservoirMap_total,
        Superfunctor.comp_total, SVec.comp_whiskerRight])
end Tensor
section Composition
variable {k : Type*} [CommRing k] {B C E : Type*}
  [Category* B] [Preadditive B] [Linear k B] [Supercategory k B]
  [Category* C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category* E] [Preadditive E] [Linear k E] [Supercategory k E]

/-- Prewhiskering a supernatural endomorphism retains chronological composition. -/
def prewhiskerEndAction (F : Superfunctor k B C) (G : Superfunctor k C E) :
    End G →ₐ[k] End (F.comp G) :=
  AlgHom.ofLinearMap
    { toFun := Superfunctor.whiskerLeft F
      map_add' := Superfunctor.whiskerLeft_add F
      map_smul' := Superfunctor.whiskerLeft_smul F }
    (Superfunctor.whiskerLeft_id F G)
    (fun f g => Superfunctor.whiskerLeft_comp F g f)
/-- Postwhiskering coefficients by the prescribed word functor keeps its algebra. -/
def postwhiskerEndAction (F : Superfunctor k B C) (G : Superfunctor k C E) :
    End F →ₐ[k] End (F.comp G) :=
  AlgHom.ofLinearMap
    { toFun := fun f => Superfunctor.whiskerRight f G
      map_add' := fun f g => Superfunctor.add_whiskerRight f g G
      map_smul' := fun r f => Superfunctor.smul_whiskerRight r f G }
    (Superfunctor.id_whiskerRight F G)
    (fun f g => Superfunctor.comp_whiskerRight g f G)
end Composition

section Functor
variable {k : Type*} [CommRing k] {C B : Type*}
  [Category* C] [Preadditive C] [Linear k C]
  [Category* B] [Preadditive B] [Linear k B]
/-- Mapping endomorphisms by a linear functor preserves their algebra. -/
def functorEndAction (F : C ⥤ B) [F.Additive] [F.Linear k] (M : C) :
    End M →ₐ[k] End (F.obj M) where
  toFun := F.map
  map_one' := F.map_id M
  map_mul' f g := F.map_comp g f
  map_zero' := F.map_zero M M
  map_add' _ _ := F.map_add
  commutes' r := by
    simp only [Algebra.algebraMap_eq_smul_one, End.one_def]
    rw [Functor.map_smul, F.map_id]
end Functor

section Vacuum
open CyclotomicAction SwappedAssembly
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ)

private def weightedEndAction (N : ℕ)
    (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))
    (hM : KillsWeightedCoefficients D Sc cutoff N M) :
    End M →ₐ[k] End (weightedModule D Sc cutoff N M hM) :=
  AlgHom.ofLinearMap
    { toFun := weightedModuleHom D Sc cutoff N M M hM hM
      map_add' := by
        intro f g
        apply Superfunctor.hom_ext
        intro p v
        rfl
      map_smul' := by
        intro r f
        apply Superfunctor.hom_ext
        intro p v
        rfl }
    (weightedModuleHom_id D Sc cutoff N M hM)
    (fun f g => weightedModuleHom_comp D Sc cutoff N M M M hM hM hM g f)

variable [Fintype I] (L : I × ℕ → ℕ) (ΛP ΛR : X)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "W" => ReservoirWordValue.initialValue D ΛR Sc cutoff L
local notation "Z" => WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L
local notation "A" => SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff

/-- The original coefficient action on each entire reservoir-vacuum block. -/
def vacuumBlockAction (β : WeightBlocks D ΛR (ReservoirWord.weight D ΛR 0)) :
    A →ₐ[k] End (W β) :=
  (functorEndAction
    (BalancedInduction.restriction (contentInclusion D Sc cutoff N β.1))
      (PowerWordContent.weightedWord D Sc cutoff L [])).comp
    ((weightedEndAction D Sc cutoff N (powerWordModule D Sc cutoff L [])
      (PowerWordContent.word_killsWeighted D Sc cutoff L [])).comp
      (coefficientModuleAction D Sc cutoff (powerWordModule D Sc cutoff L [])))

private def blockTensorAction (β : WeightBlocks D ΛR (ReservoirWord.weight D ΛR 0)) :
    A →ₐ[k] End (WeightTensorVacuum.blockFunctor D Sc m cutoff N ΛP ΛR W β) :=
  (prewhiskerEndAction (WeightTensorVacuum.emptyProbe D Sc m ΛP)
    (VacuumTensor.superfunctor (W β) (probeOldVacuumObject D Sc m))).comp
    ((reservoirEndAction (W β) (probeOldVacuumObject D Sc m)).comp
      (vacuumBlockAction D Sc cutoff L ΛR β))

private def coefficientMap (a : A) : End Z where
  app p M β := (blockTensorAction D Sc m cutoff L ΛP ΛR β a).app p M
  app_mem p M β := (blockTensorAction D Sc m cutoff L ΛP ΛR β a).app_mem p M
  naturality p M M' q f hf := by
    funext β
    exact (blockTensorAction D Sc m cutoff L ΛP ΛR β a).naturality p f hf

/-- Full coefficients act on the whole tensor-vacuum Hom, before regular-probe evaluation. -/
def coefficientAction : A →ₐ[k] End Z :=
  AlgHom.ofLinearMap
    { toFun := coefficientMap D Sc m cutoff L ΛP ΛR
      map_add' := by
        intro a b
        apply Superfunctor.hom_ext
        intro p M
        funext β
        exact congrArg (fun f => f.app p M)
          ((blockTensorAction D Sc m cutoff L ΛP ΛR β).map_add a b)
      map_smul' := by
        intro r a
        apply Superfunctor.hom_ext
        intro p M
        funext β
        exact congrArg (fun f => f.app p M)
          ((blockTensorAction D Sc m cutoff L ΛP ΛR β).toLinearMap.map_smul r a) }
    (by
      apply Superfunctor.hom_ext
      intro p M
      funext β
      have h := congrArg (fun f => f.app p M)
        (blockTensorAction D Sc m cutoff L ΛP ΛR β).map_one
      rcases parity_eq_zero_or_one p with rfl | rfl <;> exact h)
    (by
      intro a b
      apply Superfunctor.hom_ext
      intro p M
      funext β
      exact congrArg (fun f => f.app p M)
        ((blockTensorAction D Sc m cutoff L ΛP ΛR β).map_mul a b))

/-- Original SYM coefficients act through their specified ELV quotient classes. -/
def sourceCoefficientAction : SKM.SYM D k →ₐ[k] End Z :=
  (coefficientAction D Sc m cutoff L ΛP ΛR).comp (SKM.SYM.elvCoefficientQuotient D cutoff)

/-- Every input module and every vector retains the literal first-factor action. -/
theorem coefficientAction_total (a : A)
    (M : ProbeOldWeightProduct D Sc m ΛP (-ΛP))
    (β : WeightBlocks D ΛR (ReservoirWord.weight D ΛR 0))
    (c : ContentCategory D Sc cutoff N β.1) :
    (((coefficientAction D Sc m cutoff L ΛP ΛR a).total M) β).total c =
      SVec.whiskerRight ((vacuumBlockAction D Sc cutoff L ΛR β a).total c)
        (((WeightTensorVacuum.emptyProbe D Sc m ΛP).obj M).obj
          (probeOldVacuumObject D Sc m)) := by
  change ((reservoirMap (probeOldVacuumObject D Sc m)
    (vacuumBlockAction D Sc cutoff L ΛR β a)).total
      ((WeightTensorVacuum.emptyProbe D Sc m ΛP).obj M)).total c = _
  exact reservoirMap_total _ _ _ _

private theorem coefficientAction_block (a : A)
    (M : ProbeOldWeightProduct D Sc m ΛP (-ΛP))
    (β : WeightBlocks D ΛR (ReservoirWord.weight D ΛR 0)) :
    ((coefficientAction D Sc m cutoff L ΛP ΛR a).total M) β =
      tensorMap (vacuumBlockAction D Sc cutoff L ΛR β a)
        (((WeightTensorVacuum.emptyProbe D Sc m ΛP).obj M).obj (probeOldVacuumObject D Sc m)) := by
  change tensorMap (proj k 0 (vacuumBlockAction D Sc cutoff L ΛR β a)) _ +
    tensorMap (proj k 1 (vacuumBlockAction D Sc cutoff L ΛR β a)) _ = _
  unfold tensorMap
  rw [← Superfunctor.add_whiskerRight, proj_add_proj]

private theorem regularBlock_square
    (V : ELVWeightProduct D Sc cutoff N ΛR (ReservoirWord.weight D ΛR 0))
    (β : WeightBlocks D ΛR (ReservoirWord.weight D ΛR 0)) (f : End (V β)) :
    tensorMap f (((WeightTensorVacuum.emptyProbe D Sc m ΛP).obj
      (WeightTensorVacuum.regularProbe D Sc m ΛP)).obj (probeOldVacuumObject D Sc m)) ≫
        (WeightTensorVacuum.regularIso D Sc m cutoff N ΛP ΛR V).hom β =
      (WeightTensorVacuum.regularIso D Sc m cutoff N ΛP ΛR V).hom β ≫ f := by
  have h₀ := tensorMap_eq_square f (probeOldVacuumObject D Sc m)
    (WeightTensorVacuum.emptyProbe_regular D Sc m ΛP)
  have h₁ := tensorMap_scalar_square f _ (probeVacuumScalarEquiv D Sc m).symm
    (show SVec.ofHom (probeVacuumScalarEquiv D Sc m).symm.toLinearMap ∈
      parity (R := k) _ SVec.unit 0 from by
        intro q
        apply LinearMap.ext
        intro v
        change (probeVacuumScalarEquiv D Sc m).symm
          (((probeOldVacuumRegular D Sc m).obj (probeOldVacuumObject D Sc m)).proj q v) =
          SVec.unit.proj (q + 0) ((probeVacuumScalarEquiv D Sc m).symm v)
        rw [SVec.proj_apply_of_mem_part _ (p := q) (probeVacuum_even D Sc m v)]
        rcases parity_eq_zero_or_one q with rfl | rfl
        · simp only [ite_true, add_zero]
          exact (SVec.unit_proj_zero_apply _).symm
        · simp only [one_ne_zero, ite_false, map_zero, add_zero]
          exact (SVec.unit_proj_one_apply _).symm)
  change tensorMap f _ ≫
      (eqToHom (WeightTensorVacuum.regularBlock_eq D Sc m cutoff N ΛP ΛR V β) ≫ _) =
    (eqToHom (WeightTensorVacuum.regularBlock_eq D Sc m cutoff N ΛP ΛR V β) ≫ _) ≫ f
  rw [← Category.assoc, h₀, Category.assoc, h₁, Category.assoc]

/-- The regular-probe chart intertwines the full tensor coefficient
map with its literal reservoir action on all blocks and all vectors. -/
theorem coefficientAction_regular (a : A) :
    (coefficientAction D Sc m cutoff L ΛP ΛR a).total
        (WeightTensorVacuum.regularProbe D Sc m ΛP) ≫
      (WeightTensorVacuum.selectedIso D Sc m cutoff ΛP ΛR L).hom =
    (WeightTensorVacuum.selectedIso D Sc m cutoff ΛP ΛR L).hom ≫
      (fun β => vacuumBlockAction D Sc cutoff L ΛR β a) := by
  funext β
  change ((coefficientAction D Sc m cutoff L ΛP ΛR a).total
      (WeightTensorVacuum.regularProbe D Sc m ΛP) β) ≫
      (WeightTensorVacuum.selectedIso D Sc m cutoff ΛP ΛR L).hom β =
    (WeightTensorVacuum.selectedIso D Sc m cutoff ΛP ΛR L).hom β ≫ _
  rw [coefficientAction_block]
  exact regularBlock_square D Sc m cutoff L ΛP ΛR W β _

/-- On every regular tensor vector the original coefficient acts on its
reservoir vector, retaining an arbitrary probe scalar in the other factor. -/
theorem coefficientAction_regular_apply (a : A)
    (β : WeightBlocks D ΛR (ReservoirWord.weight D ΛR 0))
    (c : ContentCategory D Sc cutoff N β.1)
    (z : (((Z).obj (WeightTensorVacuum.regularProbe D Sc m ΛP)) β).obj c) :
    ((WeightTensorVacuum.selectedIso D Sc m cutoff ΛP ΛR L).hom β).total c
      ((((coefficientAction D Sc m cutoff L ΛP ΛR a).total
        (WeightTensorVacuum.regularProbe D Sc m ΛP)) β).total c z) =
    (vacuumBlockAction D Sc cutoff L ΛR β a).total c
      (((WeightTensorVacuum.selectedIso D Sc m cutoff ΛP ΛR L).hom β).total c z) := by
  have h := congrArg (fun f => (f β).total c z)
    (coefficientAction_regular D Sc m cutoff L ΛP ΛR a)
  change ((((coefficientAction D Sc m cutoff L ΛP ΛR a).total
      (WeightTensorVacuum.regularProbe D Sc m ΛP) β) ≫
      (WeightTensorVacuum.selectedIso D Sc m cutoff ΛP ΛR L).hom β).total c) z =
    (((WeightTensorVacuum.selectedIso D Sc m cutoff ΛP ΛR L).hom β ≫
      vacuumBlockAction D Sc cutoff L ΛR β a).total c) z at h
  simpa only [Superfunctor.comp_total, SVec.comp_apply] using h

/-- Source SYM coefficients on every tensor vector agree with their
original reservoir action after the prescribed regular vacuum chart. -/
theorem sourceCoefficientAction_tensorVector (a : SKM.SYM D k)
    (β : WeightBlocks D ΛR (ReservoirWord.weight D ΛR 0))
    (c : ContentCategory D Sc cutoff N β.1) (v : (W β).obj c) :
    ((WeightTensorVacuum.selectedIso D Sc m cutoff ΛP ΛR L).hom β).total c
      ((((sourceCoefficientAction D Sc m cutoff L ΛP ΛR a).total
        (WeightTensorVacuum.regularProbe D Sc m ΛP)) β).total c
          (WeightTensorVacuum.tensorVector D Sc m cutoff N ΛP ΛR W β c v)) =
    (vacuumBlockAction D Sc cutoff L ΛR β (SKM.SYM.elvCoefficientQuotient D cutoff a)).total c v := by
  exact (coefficientAction_regular_apply D Sc m cutoff L ΛP ΛR
    (SKM.SYM.elvCoefficientQuotient D cutoff a) β c
      (WeightTensorVacuum.tensorVector D Sc m cutoff N ΛP ΛR W β c v)).trans
    (congrArg (fun z =>
      (vacuumBlockAction D Sc cutoff L ΛR β (SKM.SYM.elvCoefficientQuotient D cutoff a)).total c z)
        (WeightTensorVacuum.regularIso_hom_tensorVector D Sc m cutoff N ΛP ΛR W β c v))

end Vacuum

section Hom
variable {k : Type*} [CommRing k] {C : Type*}
  [Category* C] [Preadditive C] [Linear k C]

/-- Coefficients act on a word Hom by literal postcomposition.
The source object can be arbitrary, and multiplication keeps its original order. -/
def postcompositionAlgHom (A B : C) : End B →ₐ[k] Module.End k (A ⟶ B) :=
  AlgHom.ofLinearMap
    { toFun b :=
        { toFun := fun f => f ≫ b
          map_add' := by intros; apply Preadditive.add_comp
          map_smul' := by intros; apply Linear.smul_comp }
      map_add' := by
        intro b c
        apply LinearMap.ext
        intro f
        apply Preadditive.comp_add
      map_smul' := by
        intro r b
        apply LinearMap.ext
        intro f
        apply Linear.comp_smul }
    (by apply LinearMap.ext; intro f; exact Category.comp_id f)
    (by
      intro a b
      apply LinearMap.ext
      intro f
      exact (Category.assoc f b a).symm)

@[simp] theorem postcompositionAlgHom_apply (A B : C) (a : End B) (f : A ⟶ B) :
    postcompositionAlgHom (k := k) A B a f = f ≫ a := rfl
end Hom

section Paths
open CyclotomicAction SwappedAssembly
variable {I X k : Type u} [AddCommGroup X] [CommRing k] [Fintype I]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m cutoff : I → ℕ)
  (L : I × ℕ → ℕ) (ΛP ΛR : X)
local notation "N" => PowerWordContent.powerBound D cutoff L
local notation "Z" => WeightTensorVacuum.selectedHom D Sc m cutoff ΛP ΛR L

/-- Source coefficients on a literal reservoir-path Hom are the full
vacuum coefficient maps whiskered by that same path functor. -/
def pathCoefficientAction {l : List (SKM.Col I X)} {c : I →₀ ℕ}
    (p : SPath l (0,c) (0,0)) (hl : ∀ a ∈ l, a.l.1 = true) :
    SKM.SYM D k →ₐ[k] End (TensorReservoirWords.pathHom D Sc m cutoff L ΛP ΛR p hl) :=
  (postwhiskerEndAction Z (ReservoirWord.word (elvRouquierData D Sc cutoff N ΛR) ΛR p hl)).comp
    (sourceCoefficientAction D Sc m cutoff L ΛP ΛR)

/-- The whole word-Hom action is literal postcomposition by the path-whiskered
vacuum coefficient. An arbitrary source object and all its vectors are retained. -/
def pathHomCoefficientAction {l : List (SKM.Col I X)} {c : I →₀ ℕ}
    (p : SPath l (0,c) (0,0)) (hl : ∀ a ∈ l, a.l.1 = true)
    (G : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶
      elvWeightSpace D Sc cutoff N ΛR (ReservoirWord.weight D ΛR c)) :
    SKM.SYM D k →ₐ[k] Module.End k (G ⟶ TensorReservoirWords.pathHom D Sc m cutoff L ΛP ΛR p hl) :=
  (postcompositionAlgHom G (TensorReservoirWords.pathHom D Sc m cutoff L ΛP ΛR p hl)).comp
    (pathCoefficientAction D Sc m cutoff L ΛP ΛR p hl)

/-- Placement on a word Hom is postcomposition, including inhomogeneous
coefficients and arbitrary whole-functor maps from the source. -/
@[simp] theorem pathHomCoefficientAction_apply {l : List (SKM.Col I X)} {c : I →₀ ℕ}
    (p : SPath l (0,c) (0,0)) (hl : ∀ a ∈ l, a.l.1 = true)
    (G : probeOldWeightSpace D Sc m ΛP (-ΛP) ⟶
      elvWeightSpace D Sc cutoff N ΛR (ReservoirWord.weight D ΛR c))
    (a : SKM.SYM D k) (f : G ⟶ TensorReservoirWords.pathHom D Sc m cutoff L ΛP ΛR p hl) :
    pathHomCoefficientAction D Sc m cutoff L ΛP ΛR p hl G a f =
      f ≫ pathCoefficientAction D Sc m cutoff L ΛP ΛR p hl a := rfl

end Paths

end OddMath.QuiverHecke.ELVOld.VacuumTensorCoefficientMaps
