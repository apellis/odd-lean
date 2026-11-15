import OddMath.QuiverHecke.CyclotomicAction.WeightMixed
import OddMath.QuiverHecke.CyclotomicAction.RouquierPowerWords
import OddMath.QuiverHecke.CyclotomicAction.TensorWords
import OddMath.QuiverHecke.CyclotomicAction.InductionTripleBraid
import OddMath.SKM.BubbleCoefficientGradedBase
import OddMath.Diagrams.SuperalgebraGradedBase
import OddMath.Diagrams.CoefficientGradedSupercategory
import OddMath.QuiverHecke.CoefficientGrading
import OddMath.QuiverHecke.CyclotomicAction.CoefficientTransport
import OddMath.SKM.BubbleELVPolynomialGradingOver
import OddMath.QuiverHecke.CyclotomicAction.VacuumGrading
import OddMath.QuiverHecke.CyclotomicAction.TruncatedAppend

/-!
# Vacuum tensor faithful

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # Coefficient maps on the tensor-vacuum input

SwappedVacuumCoordinates §§2–6: coefficients act on the reservoir factor
of the entire tensor-vacuum functor, before evaluation at a regular probe.
The action retains both supernatural parities and the original ordered
coefficient algebra. Postcomposition on word Homs preserves that order.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELV.VacuumTensorCoefficientMaps
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

end OddMath.QuiverHecke.ELV.VacuumTensorCoefficientMaps
end

end

section

/-! # Faithfulness of tensor vacuum transformations at a generating module

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, §8, the
Nondegeneracy Conjecture (research scope of `FieldScopeBoundary.md`): input to
the vacuum-entry match of the positive-height bubble field.

For a superfunctor `G` followed by the tensor vacuum `M ↦ W ⊗ M(a)`, a
supernatural transformation out of it is determined by its components at one
object `Y₀`, provided every homogeneous vector of every `(G X)(a)` is the image of
a fixed vector `y₀ ∈ (G Y₀)(a)` under `G f` for a homogeneous `f : Y₀ ⟶ X` of the
same parity. This is
the Yoneda step: the vacuum entries of the tensor vacuum are read at the regular
probe.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELV.VacuumTensor
universe u
variable {k A C : Type u} [CommRing k]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]

variable {P : Type*} [Category P] [Preadditive P] [Linear k P] [Supercategory k P]

/-- The signed naturality of a transformation out of `G` followed by the tensor
vacuum, evaluated on `v ⊗ y` along a morphism `f` of parity `q`. -/
theorem app_tmul_of_naturality (W : Superfunctor k C (SVec k)) (a : A)
    (G : Superfunctor k P (Superfunctor k A (SVec k)))
    {H : Superfunctor k P (Superfunctor k C (SVec k))}
    (χ : G.comp (superfunctor W a) ⟶ H) (p r : ZMod 2) {Y M : P}
    {q : ZMod 2} (f : Y ⟶ M) (hfm : f ∈ parity (R := k) Y M q) (c : C) {s : ZMod 2}
    {v : W.obj c} (hv : v ∈ (W.obj c).part s) (y : (G.obj Y).obj a) :
    sign k (s * q) • (χ.app p M).app (r + q) c (v ⊗ₜ[k] (G.map f).app q a y) =
      koszulSign p q • ((χ.app p Y ≫ H.map f).app r c) (v ⊗ₜ[k] y) := by
  have hf : (G.map f).app (q + 1) = 0 := Superfunctor.mem_parityHom.mp (G.map_mem hfm)
  have h := congrArg
    (fun x : (G.comp (superfunctor W a)).obj Y ⟶ H.obj M => (x.app r c) (v ⊗ₜ[k] y))
    (χ.naturality p f hfm)
  rw [Superfunctor.zsmul_app, SVec.zsmul_apply] at h
  rw [← h, Superfunctor.comp_app, SVec.add_apply, SVec.comp_apply, SVec.comp_apply]
  have hz : ((G.comp (superfunctor W a)).map f).app (q + 1) c = 0 := by
    change SVec.whiskerLeft (W.obj c) ((G.map f).app (q + 1) a) = 0
    rw [congrFun hf a]; exact SVec.whiskerLeft_zero _
  have ht : ∀ q', ((G.comp (superfunctor W a)).map f).app q' c (v ⊗ₜ[k] y) =
      sign k (s * q') • (v ⊗ₜ[k] (G.map f).app q' a y) := fun q' =>
    superfunctor_map_app_tmul W a (G.map f) s q' c v hv y
  rcases parity_eq_zero_or_one q with rfl | rfl
  · rw [zero_add] at hz
    rw [hz, SVec.zero_apply, map_zero, add_zero, add_zero, ht]
    simp
  · rw [SVec.zmod2_one_add_one] at hz
    rw [hz, SVec.zero_apply, map_zero, zero_add, ht, map_smul]

/-- **Faithfulness at a generating object.** Two transformations out of `G`
followed by the tensor vacuum `M ↦ W ⊗ M(a)` agree if they agree at `Y₀`,
provided every homogeneous vector of every `(G X)(a)` is `(G f)(y₀)` for a
homogeneous `f : Y₀ ⟶ X` of its parity. -/
theorem hom_ext_of_generating (W : Superfunctor k C (SVec k)) (a : A)
    (G : Superfunctor k P (Superfunctor k A (SVec k)))
    {H : Superfunctor k P (Superfunctor k C (SVec k))}
    {Y₀ : P} (y₀ : (G.obj Y₀).obj a)
    (hgen : ∀ (X : P) (q : ZMod 2) (m : (G.obj X).obj a),
      m ∈ ((G.obj X).obj a).part q →
        ∃ f : Y₀ ⟶ X, f ∈ parity (R := k) Y₀ X q ∧ (G.map f).app q a y₀ = m)
    {φ ψ : G.comp (superfunctor W a) ⟶ H} (h : ∀ p, φ.app p Y₀ = ψ.app p Y₀) : φ = ψ := by
  apply Superfunctor.hom_ext
  intro p X
  apply Superfunctor.hom_ext
  intro r c
  apply SVec.hom_ext
  intro x
  change SVec.toLinearMap ((φ.app p X).app r c) x = SVec.toLinearMap ((ψ.app p X).app r c) x
  congr 1
  apply SVec.ext_tensor
  intro s q v m hv hm
  obtain ⟨f, hf, rfl⟩ := hgen X q m hm
  have hφ := app_tmul_of_naturality W a G φ p (r + q) f hf c hv y₀
  have hψ := app_tmul_of_naturality W a G ψ p (r + q) f hf c hv y₀
  rw [h p] at hφ
  have hrq : r + q + q = r := by
    rcases parity_eq_zero_or_one q with rfl | rfl <;> simp [add_assoc]
  rw [hrq] at hφ hψ
  have := hφ.trans hψ.symm
  have := congrArg (fun z => sign k (s * q) • z) this
  simp only [sign_smul_sign_smul] at this
  exact this

/-- Faithfulness at a generating object, read on the total components. -/
theorem hom_ext_of_generating_total (W : Superfunctor k C (SVec k)) (a : A)
    (G : Superfunctor k P (Superfunctor k A (SVec k)))
    {H : Superfunctor k P (Superfunctor k C (SVec k))}
    {Y₀ : P} (y₀ : (G.obj Y₀).obj a)
    (hgen : ∀ (X : P) (q : ZMod 2) (m : (G.obj X).obj a),
      m ∈ ((G.obj X).obj a).part q →
        ∃ f : Y₀ ⟶ X, f ∈ parity (R := k) Y₀ X q ∧ (G.map f).app q a y₀ = m)
    {φ ψ : G.comp (superfunctor W a) ⟶ H}
    (h : SuperNatTrans.total φ Y₀ = SuperNatTrans.total ψ Y₀) : φ = ψ := by
  apply hom_ext_of_generating W a G y₀ hgen
  have hp : ∀ χ : G.comp (superfunctor W a) ⟶ H, ∀ p,
      χ.app p Y₀ = Supercategory.proj (R := k) p (SuperNatTrans.total χ Y₀) := by
    intro χ p
    rcases parity_eq_zero_or_one p with rfl | rfl
    · exact (Supercategory.proj_eq_of_add (R := k) rfl (χ.app_mem 0 Y₀) (χ.app_mem 1 Y₀)).symm
    · exact (Supercategory.proj_eq_of_add (R := k) (add_comm _ _) (χ.app_mem 1 Y₀)
        (χ.app_mem 0 Y₀)).symm
  intro p
  rw [hp φ, hp ψ, h]

end OddMath.QuiverHecke.ELV.VacuumTensor
end

end

section

/-!
# Integer grading of the ELV coefficient category over a graded base ring

Let `R` be a commutative `K`-algebra graded by `𝒜 : ℤ → Submodule K R`, and let `Sc` be a
parameter system over `R` whose quiver Hecke presentation is coefficient-graded homogeneous
(for instance the truncated Rees parameters, `QuiverHecke.isHomogeneous_truncatedRees`). The
ELV coefficient category over `R` is the box product over `R` of the one-object category of the
ELV coefficient algebra with the quiver Hecke category. Both factors are graded supercategories
over `K` with compatible base-ring degrees, so the box product is one
(`QuiverHecke.elvHomGradingOver`).

For `K = R` with the trivial grading this is the shape of `QuiverHecke.elvHomGrading`; over the
truncated Rees rings it is the ELV grading of `docs/Nondegeneracy/Phase2Plan.md`, step 2.
-/

noncomputable section

open CategoryTheory StringDiagrams OddMath.Diagrams

namespace OddMath.QuiverHecke

universe u

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  {K : Type u} [CommRing K] {R : Type u} [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R) [GradedAlgebra 𝒜]
  (Sc : SKM.Scalars D R)
  (hP : CoefficientGrading.IsHomogeneous 𝒜 (gdeg D sy) (pres D Sc)) (cutoff : I → ℕ)

/-- The coefficient factor: the one-object category of the ELV coefficient algebra over `R`,
graded over `K` by the coefficientwise degree. -/
@[instance_reducible]
def elvCoefficientCategoryGradingOver :
    letI := Linear.restrictScalars K R
      (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff))
    letI := Supercategory.restrictScalars K R
      (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff))
    GradedSupercategory K (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff)) :=
  letI := SKM.SYM.elvCoefficientDegreeGradedAlgebraOver D sy 𝒜 cutoff
  SuperalgebraCatOver.gradedSupercategory _ (SKM.SYM.elvCoefficientDegreeOver D sy 𝒜 cutoff)
    (fun p hx => SKM.SYM.elvCoefficientDegreeOver_parity cutoff p hx)

/-- The quiver Hecke factor, graded over `K`. -/
@[instance_reducible]
def quiverHeckeGradingOver :
    letI := Linear.restrictScalars K R (H D Sc)
    letI := Supercategory.restrictScalars K R (H D Sc)
    GradedSupercategory K (H D Sc) :=
  CoefficientGrading.gradedSupercategory (isParityHomogeneous D Sc) hP

/-- **Integer grading of the ELV coefficient category over a graded base.** -/
@[instance_reducible]
def elvHomGradingOver :
    letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
    letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
    GradedSupercategory K (ELVCoefficientCategory D Sc cutoff) :=
  letI := Linear.restrictScalars K R
    (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff))
  letI := Supercategory.restrictScalars K R
    (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff))
  haveI : ∀ A B : SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff),
      IsScalarTower K R (A ⟶ B) :=
    Linear.isScalarTower_restrictScalars K R _
  letI := elvCoefficientCategoryGradingOver D sy 𝒜 cutoff
  letI := Linear.restrictScalars K R (H D Sc)
  letI := Supercategory.restrictScalars K R (H D Sc)
  letI := quiverHeckeGradingOver D sy 𝒜 Sc hP
  BoxProdCoefficient.gradedSupercategory (𝒜 := 𝒜)
    (fun {_ _ _ _ _ _} hr hf => by
      change SuperalgebraCat.toElem (_ • _) ∈ SKM.SYM.elvCoefficientDegreeOver D sy 𝒜 cutoff _
      rw [SuperalgebraCat.toElem_smul]
      exact SKM.SYM.smul_mem_elvCoefficientDegreeOver cutoff hr hf)
    (fun {_ _ _ _ _ _} hr hf => CoefficientGrading.smul_mem_presentedPart_add hr hf)
    (fun _ _ _ _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl)

end OddMath.QuiverHecke
end

end

section

/-!
# The old cyclotomic ideal over a graded base ring

Let `R` be a commutative `K`-algebra graded by `𝒜`, and let the quiver Hecke presentation over
`R` be coefficient-graded homogeneous. For the grading `QuiverHecke.elvHomGradingOver` of the ELV
coefficient category over `R`, the first-position cyclotomic relation is homogeneous of degree
`2 d_j cutoff_j` (`ELV.relation_mem_degreeOver`), and every homogeneous component of an
element of the old two-sided cyclotomic ideal lies in the ideal
(`ELV.ideal_dproj_mem_over`).

The ideal is an `R`-span, while the degree projections are only `K`-linear: the step from the
generators to the span decomposes the scalars into homogeneous parts
(`BasisGrading.decompose_mem_span`). For `K = R` with the trivial grading these are
`ELV.relation_mem_degree` and `ELV.ideal_dproj_mem`.
-/

-- `letI` keeps the restricted-scalar instances available to instance search in these proofs.
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory StringDiagrams OddMath.Diagrams GradedSupercategory

namespace OddMath.QuiverHecke

universe u

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  {K : Type u} [CommRing K] {R : Type u} [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R) [GradedAlgebra 𝒜]
  (Sc : SKM.Scalars D R)
  (hP : CoefficientGrading.IsHomogeneous 𝒜 (gdeg D sy) (pres D Sc)) (cutoff : I → ℕ)

/-- A positional normal-form diagram has the degree of its layers, over a graded base. -/
theorem cl_mem_presentedPart {t t' : List I} (gs : List PG) (h : SChain t (pl t gs) t') :
    cl D Sc t t' gs h ∈ CoefficientGrading.presentedPart 𝒜 (gdeg D sy) (pres D Sc) (ob D t)
      (ob D t') ((pl t gs).map fun x => gdeg D sy x.2.1).sum :=
  CoefficientGrading.lin_mem_presentedPart
    (CoefficientGrading.of_mem_part' _ (degree_gdeg_mkD D sy _ _))

/-- Dot powers on a nonempty word have their symmetrizer degree, over a graded base. -/
theorem firstDotPower_mem_presentedPart (j : I) (v : List I) (n : ℕ) :
    firstDotPower D Sc (j :: v) n ∈ CoefficientGrading.presentedPart 𝒜 (gdeg D sy) (pres D Sc)
      (ob D (j :: v)) (ob D (j :: v)) (2 * sy.d j * n) := by
  have hd : ((pl (j :: v) ((List.replicate n 0).map PG.dot)).map
      fun x => gdeg D sy x.2.1).sum = 2 * sy.d j * n := by
    simp only [List.map_replicate]
    induction n with
    | zero => simp
    | succ n ih =>
      simp only [List.replicate_succ, pl_cons, PG.ld, PG.act, List.drop_zero,
        List.take_zero, List.singleton_append, List.map_cons, List.sum_cons]
      rw [ih]
      simp only [gdeg, Nat.cast_add, Nat.cast_one]
      ring
  have h := cl_mem_presentedPart D sy 𝒜 Sc (t := j :: v) (t' := j :: v)
    ((List.replicate n 0).map PG.dot)
    (by simpa only [tgt_map_dot] using sChain_pl (j :: v) ((List.replicate n 0).map PG.dot))
  rw [hd] at h
  exact h

/-- The degree-`n` part of a Hom module of the ELV coefficient category over `R`. -/
abbrev elvHomDegreeOver (v w : List I) (n : ℤ) :
    letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
    Submodule K (ELV.hom D Sc cutoff v w) :=
  letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
  GradedSupercategory.degree (R := K) (ELV.obj D Sc cutoff v) (ELV.obj D Sc cutoff w) n

/-- Homogeneous scalars of `R` raise degrees in the ELV coefficient category over `R`. -/
theorem smul_mem_elvHomDegreeOver {v w : List I} {e n : ℤ} {r : R}
    {y : ELV.hom D Sc cutoff v w} (hr : r ∈ 𝒜 e)
    (hy : y ∈ elvHomDegreeOver D sy 𝒜 Sc hP cutoff v w n) :
    r • y ∈ elvHomDegreeOver D sy 𝒜 Sc hP cutoff v w (e + n) := by
  letI := Linear.restrictScalars K R
    (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff))
  letI := Supercategory.restrictScalars K R
    (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff))
  have : ∀ A B : SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff),
      IsScalarTower K R (A ⟶ B) :=
    Linear.isScalarTower_restrictScalars K R _
  letI := elvCoefficientCategoryGradingOver D sy 𝒜 cutoff
  letI := Linear.restrictScalars K R (H D Sc)
  letI := Supercategory.restrictScalars K R (H D Sc)
  letI := quiverHeckeGradingOver D sy 𝒜 Sc hP
  exact BoxProdCoefficient.smul_mem_homDegree (𝒜 := 𝒜)
    (fun {_ _ _ _ _ _} hr hf => by
      change SuperalgebraCat.toElem (_ • _) ∈ SKM.SYM.elvCoefficientDegreeOver D sy 𝒜 cutoff _
      rw [SuperalgebraCat.toElem_smul]
      exact SKM.SYM.smul_mem_elvCoefficientDegreeOver cutoff hr hf) hr hy

/-- A coefficient and an affine diagram contribute additively to the degree over `R`. -/
theorem elvQuotientMap_source_mem_degreeOver {v w : List I} {a : SKM.SYM D R}
    {f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)} {r s : ℤ}
    (ha : a ∈ SKM.SYM.coefficientDegreePartOver D sy 𝒜 r)
    (hf : f ∈ CoefficientGrading.presentedPart 𝒜 (gdeg D sy) (pres D Sc) (ob D v) (ob D w) s) :
    elvQuotientMap D Sc cutoff _ _ (sourceCoefficientHom D Sc a f) ∈
      elvHomDegreeOver D sy 𝒜 Sc hP cutoff v w (r + s) := by
  rw [elvQuotientMap_source]
  letI := Linear.restrictScalars K R
    (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff))
  letI := Supercategory.restrictScalars K R
    (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff))
  have : ∀ A B : SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff),
      IsScalarTower K R (A ⟶ B) :=
    Linear.isScalarTower_restrictScalars K R _
  letI := elvCoefficientCategoryGradingOver D sy 𝒜 cutoff
  letI := Linear.restrictScalars K R (H D Sc)
  letI := Supercategory.restrictScalars K R (H D Sc)
  letI := quiverHeckeGradingOver D sy 𝒜 Sc hP
  have ha' : SKM.SYM.elvCoefficientQuotient D cutoff a ∈
      SKM.SYM.elvCoefficientDegreeOver D sy 𝒜 cutoff r :=
    Submodule.mem_map_of_mem (f := ((SKM.SYM.elvCoefficientQuotient D cutoff).restrictScalars
      K).toLinearMap) ha
  exact BoxProdCoefficient.tmulHom_mem_homDegree (X := ELV.obj D Sc cutoff v)
    (Y := ELV.obj D Sc cutoff w) ha' hf

/-- A coefficient polynomial with complementary coefficient degrees is homogeneous over `R`. -/
theorem deformedCyclotomic_mem_degreeOver (j : I) (v : List I) (N : ℕ)
    (c : Fin (N + 1) → SKM.SYM D R)
    (hcoeff : ∀ a, c a ∈ SKM.SYM.coefficientDegreePartOver D sy 𝒜
      (2 * sy.d j * ((N : ℤ) - a.val))) :
    (elvQuotientFunctor D Sc cutoff).map (deformedCyclotomic D Sc (j :: v) N c) ∈
      elvHomDegreeOver D sy 𝒜 Sc hP cutoff (j :: v) (j :: v) (2 * sy.d j * N) := by
  change elvQuotientMap D Sc cutoff _ _ _ ∈ _
  unfold deformedCyclotomic
  rw [map_sum]
  apply Submodule.sum_mem
  intro a _
  have h := elvQuotientMap_source_mem_degreeOver D sy 𝒜 Sc hP cutoff (hcoeff a)
    (firstDotPower_mem_presentedPart D sy 𝒜 Sc j v a.val)
  have he : 2 * sy.d j * ((N : ℤ) - a.val) + 2 * sy.d j * a.val = 2 * sy.d j * N := by ring
  rw [he] at h
  exact h

/-- **The first-position cyclotomic relation over a graded base** has degree
`2 d_j cutoff_j`. -/
theorem ELV.relation_mem_degreeOver (j : I) (v : List I) :
    ELV.relation D Sc cutoff j v ∈
      elvHomDegreeOver D sy 𝒜 Sc hP cutoff (j :: v) (j :: v) (2 * sy.d j * cutoff j) := by
  unfold ELV.relation
  split_ifs with hj
  · exact deformedCyclotomic_mem_degreeOver D sy 𝒜 Sc hP cutoff j v (cutoff j) _
      (SKM.SYM.elvMonicCoefficient_mem_coefficientDegreePartOver D sy 𝒜 ⟨j, hj⟩ (cutoff j))
  · have he : D.parity j = 0 :=
      (Supercategory.parity_eq_zero_or_one (D.parity j)).resolve_right hj
    exact deformedCyclotomic_mem_degreeOver D sy 𝒜 Sc hP cutoff j v (cutoff j) _
      (SKM.SYM.evenMonicCoefficient_mem_coefficientDegreePartOver D sy 𝒜 j he (cutoff j))

/-- **Homogeneity of the old cyclotomic ideal over a graded base.** Every homogeneous
component of an element of the two-sided old cyclotomic ideal lies in the ideal. -/
theorem ELV.ideal_dproj_mem_over {v w : List I} {f : ELV.hom D Sc cutoff v w}
    (hf : f ∈ ELV.ideal D Sc cutoff v w) (n : ℤ) :
    letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
    letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
    letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
    dproj K n f ∈ ELV.ideal D Sc cutoff v w := by
  letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
  let S : ∀ v w : List I, Set (ELV.hom D Sc cutoff v w) := fun v w => {f | ∃ j t,
    ∃ a : ELV.hom D Sc cutoff v (j :: t), ∃ b : ELV.hom D Sc cutoff (j :: t) w,
      a ≫ ELV.relation D Sc cutoff j t ≫ b = f}
  letI := degreeDecomposition K (ELV.obj D Sc cutoff v) (ELV.obj D Sc cutoff w)
  rw [dproj_apply]
  refine BasisGrading.decompose_mem_span 𝒜
    (GradedSupercategory.degree (R := K) (ELV.obj D Sc cutoff v) (ELV.obj D Sc cutoff w))
    (fun hr hy => smul_mem_elvHomDegreeOver D sy 𝒜 Sc hP cutoff hr hy) (S := S v w)
    ?_ hf n
  rintro g ⟨j, t, a, b, rfl⟩ m
  rw [← dproj_apply]
  refine induction_on_degree (R := K) a (by simp) (fun r a ha => ?_)
    (fun a a' ha ha' => ?_)
  · refine induction_on_degree (R := K) b (by simp) (fun s b hb => ?_)
      (fun b b' hb hb' => ?_)
    · have hg := comp_mem_degree ha
        (comp_mem_degree (ELV.relation_mem_degreeOver D sy 𝒜 Sc hP cutoff j t) hb)
      by_cases h : r + (2 * sy.d j * cutoff j + s) = m
      · rw [← h, dproj_of_mem hg]
        exact Submodule.subset_span ⟨j, t, a, b, rfl⟩
      · rw [dproj_of_mem_ne hg h]
        exact Submodule.zero_mem _
    · simpa only [Preadditive.comp_add, map_add] using Submodule.add_mem _ hb hb'
  · simpa only [Preadditive.add_comp, map_add] using Submodule.add_mem _ ha ha'

end OddMath.QuiverHecke
end

end

section

/-!
# Grading of the coefficient-truncated quotient over a graded base ring

Let `R` be a commutative `K`-algebra graded by `𝒜`, with a coefficient-graded homogeneous quiver
Hecke presentation over `R`. The coefficient truncation ideal is homogeneous for the grading
`QuiverHecke.elvHomGradingOver` (`ELV.truncatedIdeal_dproj_mem_over`), so the
coefficient-truncated quotient category is a graded supercategory over `K`
(`ELV.truncatedGradedSupercategoryOver`): the degree parts are the images of the degree parts
of the ELV coefficient category, and the degree projections descend as additive maps.

For `K = R` with the trivial grading this is `ELV.truncatedGradedSupercategory`.
-/

-- `letI` keeps the restricted-scalar instances available to instance search in these proofs.
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory StringDiagrams OddMath.Diagrams GradedSupercategory

namespace OddMath.QuiverHecke.ELV

universe u

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  {K : Type u} [CommRing K] {R : Type u} [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R) [GradedAlgebra 𝒜]
  (Sc : SKM.Scalars D R)
  (hP : CoefficientGrading.IsHomogeneous 𝒜 (gdeg D sy) (pres D Sc)) (cutoff : I → ℕ) (N : ℕ)

/-- A coefficient basis vector at a word identity has its coefficient degree, over a graded
base. -/
theorem coefficientIdentity_basis_degreeOver (t : List I) (a : SKM.SYM.CoefficientIndex D) :
    coefficientIdentity D Sc cutoff t (SKM.SYM.coefficientBasis D R a) ∈
      elvHomDegreeOver D sy 𝒜 Sc hP cutoff t t (SKM.SYM.coefficientDegree D sy a) := by
  letI := Linear.restrictScalars K R (H D Sc)
  letI := Supercategory.restrictScalars K R (H D Sc)
  letI := quiverHeckeGradingOver D sy 𝒜 Sc hP
  have ha := SKM.SYM.coefficientBasis_mem_over (sy := sy) (𝒜 := 𝒜) a
  have hi : (𝟙 ((pres D Sc).obj (ob D t))) ∈
      GradedSupercategory.degree (R := K) ((pres D Sc).obj (ob D t)) ((pres D Sc).obj (ob D t))
        0 :=
    GradedSupercategory.id_mem_degree _
  have h := elvQuotientMap_source_mem_degreeOver D sy 𝒜 Sc hP cutoff ha hi
  rw [elvQuotientMap_source, add_zero] at h
  exact h

/-- The coefficient truncation ideal is stable under the degree projections over `K`. -/
theorem coefficientHomIdeal_dproj_mem_over {v w : List I} {f : hom D Sc cutoff v w}
    (hf : f ∈ coefficientHomIdeal D Sc cutoff N v w) (n : ℤ) :
    letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
    letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
    letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
    dproj K n f ∈ coefficientHomIdeal D Sc cutoff N v w := by
  letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
  let S : Set (hom D Sc cutoff v w) := {f | ∃ t a, N ≤ SKM.SYM.coefficientWeight D a ∧
    ∃ l : hom D Sc cutoff v t, ∃ r : hom D Sc cutoff t w,
      l ≫ coefficientIdentity D Sc cutoff t (SKM.SYM.coefficientBasis D R a) ≫ r = f}
  letI := degreeDecomposition K (obj D Sc cutoff v) (obj D Sc cutoff w)
  rw [dproj_apply]
  refine BasisGrading.decompose_mem_span 𝒜
    (GradedSupercategory.degree (R := K) (obj D Sc cutoff v) (obj D Sc cutoff w))
    (fun hr hy => smul_mem_elvHomDegreeOver D sy 𝒜 Sc hP cutoff hr hy) (S := S)
    ?_ hf n
  rintro g ⟨t, c, hcw, a, b, rfl⟩ m
  rw [← dproj_apply]
  refine induction_on_degree (R := K) a (by simp) (fun r a ha => ?_)
    (fun a a' ha ha' => ?_)
  · refine induction_on_degree (R := K) b (by simp) (fun s b hb => ?_)
      (fun b b' hb hb' => ?_)
    · have hg := comp_mem_degree ha
        (comp_mem_degree (coefficientIdentity_basis_degreeOver D sy 𝒜 Sc hP cutoff t c) hb)
      by_cases h : r + (SKM.SYM.coefficientDegree D sy c + s) = m
      · rw [← h, dproj_of_mem hg]
        exact Submodule.subset_span ⟨t, c, hcw, a, b, rfl⟩
      · rw [dproj_of_mem_ne hg h]
        exact Submodule.zero_mem _
    · simpa only [Preadditive.comp_add, map_add] using Submodule.add_mem _ hb hb'
  · simpa only [Preadditive.add_comp, map_add] using Submodule.add_mem _ ha ha'

/-- The truncation ideal (old relations and coefficient truncation) is stable under the degree
projections over `K`. -/
theorem truncatedIdeal_dproj_mem_over {v w : List I} {f : hom D Sc cutoff v w}
    (hf : f ∈ truncatedIdeal D Sc cutoff N v w) (n : ℤ) :
    letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
    letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
    letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
    dproj K n f ∈ truncatedIdeal D Sc cutoff N v w := by
  letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
  obtain ⟨f, hf₁, g, hg, rfl⟩ := Submodule.mem_sup.mp hf
  rw [map_add]
  exact Submodule.mem_sup.mpr ⟨_, ideal_dproj_mem_over D sy 𝒜 Sc hP cutoff hf₁ n,
    _, coefficientHomIdeal_dproj_mem_over D sy 𝒜 Sc hP cutoff N hg n, rfl⟩

/-- The degree projection on the truncated quotient over a graded base, as an additive map. -/
def truncatedDprojOver (v w : List I) (n : ℤ) :
    TruncatedOld D Sc cutoff N v w →+ TruncatedOld D Sc cutoff N v w :=
  letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
  QuotientAddGroup.map (truncatedIdeal D Sc cutoff N v w).toAddSubgroup
    (truncatedIdeal D Sc cutoff N v w).toAddSubgroup (dproj K n).toAddMonoidHom
    (fun _ hf => truncatedIdeal_dproj_mem_over D sy 𝒜 Sc hP cutoff N hf n)

theorem truncatedDprojOver_mk (v w : List I) (n : ℤ) (f : hom D Sc cutoff v w) :
    truncatedDprojOver D sy 𝒜 Sc hP cutoff N v w n ((truncatedIdeal D Sc cutoff N v w).mkQ f) =
      (truncatedIdeal D Sc cutoff N v w).mkQ
        (letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
        letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
        letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
        dproj K n f) :=
  rfl

/-- The degree-`n` part of a Hom module of the truncated quotient over a graded base. -/
def truncatedDegreeOver (v w : TruncatedCategory D Sc cutoff N) (n : ℤ) :
    letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
    Submodule K (v ⟶ w) :=
  letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
  { carrier := {f | ∃ a ∈ elvHomDegreeOver D sy 𝒜 Sc hP cutoff v.word w.word n,
      (truncatedIdeal D Sc cutoff N v.word w.word).mkQ a = f}
    add_mem' := by
      rintro _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      exact ⟨a + b, add_mem ha hb, map_add _ a b⟩
    zero_mem' := ⟨0, zero_mem _, map_zero _⟩
    smul_mem' := by
      rintro c _ ⟨a, ha, rfl⟩
      refine ⟨algebraMap K R c • a, ?_, map_smul _ _ a⟩
      simpa using smul_mem_elvHomDegreeOver D sy 𝒜 Sc hP cutoff
        (SetLike.algebraMap_mem_graded 𝒜 c) ha }

theorem mkQ_mem_truncatedDegreeOver {v w : TruncatedCategory D Sc cutoff N} {n : ℤ}
    {a : hom D Sc cutoff v.word w.word}
    (ha : a ∈ elvHomDegreeOver D sy 𝒜 Sc hP cutoff v.word w.word n) :
    ((truncatedIdeal D Sc cutoff N v.word w.word).mkQ a : v ⟶ w) ∈
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N v w n :=
  ⟨a, ha, rfl⟩

/-- Homogeneous scalars of the base shift degrees in the truncated quotient. -/
theorem smul_mem_truncatedDegreeOver {v w : TruncatedCategory D Sc cutoff N} {e n : ℤ} {r : R}
    {f : v ⟶ w} (hr : r ∈ 𝒜 e) (hf : f ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N v w n) :
    r • f ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N v w (e + n) := by
  obtain ⟨a, ha, rfl⟩ := hf
  exact ⟨r • a, smul_mem_elvHomDegreeOver D sy 𝒜 Sc hP cutoff hr ha, map_smul _ r a⟩

theorem truncatedDprojOver_of_mem {v w : TruncatedCategory D Sc cutoff N} {m : ℤ} {f : v ⟶ w}
    (hf : f ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N v w m) (n : ℤ) :
    truncatedDprojOver D sy 𝒜 Sc hP cutoff N v.word w.word n f = if m = n then f else 0 := by
  letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
  obtain ⟨a, ha, rfl⟩ := hf
  rw [truncatedDprojOver_mk]
  split_ifs with h
  · subst n
    rw [dproj_of_mem ha]
  · rw [dproj_of_mem_ne ha h, map_zero]

/-- The degree parts of the truncated quotient over a graded base form an internal direct
sum. -/
theorem truncatedDegreeOver_internal (v w : TruncatedCategory D Sc cutoff N) :
    letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
    DirectSum.IsInternal (truncatedDegreeOver D sy 𝒜 Sc hP cutoff N v w) := by
  letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
  apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
  · rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
    intro s f hf he n hn
    have hh := congrArg (truncatedDprojOver D sy 𝒜 Sc hP cutoff N v.word w.word n) he
    rw [map_sum, map_zero] at hh
    have hsum : (∑ i ∈ s, truncatedDprojOver D sy 𝒜 Sc hP cutoff N v.word w.word n (f i)) =
        f n := by
      calc
        _ = ∑ i ∈ s, if i = n then f i else 0 :=
          Finset.sum_congr rfl
            (fun i hi => truncatedDprojOver_of_mem D sy 𝒜 Sc hP cutoff N (hf i hi) n)
        _ = f n := by simp [hn]
    exact hsum.symm.trans hh
  · classical
    refine Submodule.eq_top_iff'.2 fun f => ?_
    obtain ⟨a, rfl⟩ := (truncatedIdeal D Sc cutoff N v.word w.word).mkQ_surjective f
    letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
    letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
    letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
    letI := degreeDecomposition K (obj D Sc cutoff v.word) (obj D Sc cutoff w.word)
    rw [← DirectSum.sum_support_decompose
      (GradedSupercategory.degree (R := K) (obj D Sc cutoff v.word) (obj D Sc cutoff w.word)) a,
      map_sum]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.mem_iSup_of_mem i (mkQ_mem_truncatedDegreeOver D sy 𝒜 Sc hP cutoff N
        (DirectSum.decompose (GradedSupercategory.degree (R := K) (obj D Sc cutoff v.word)
          (obj D Sc cutoff w.word)) a i).2)

/-- **The coefficient-truncated quotient over a graded base is a graded supercategory over
`K`.** -/
@[instance_reducible]
def truncatedGradedSupercategoryOver :
    letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
    letI := Supercategory.restrictScalars K R (TruncatedCategory D Sc cutoff N)
    GradedSupercategory K (TruncatedCategory D Sc cutoff N) :=
  letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
  letI := Supercategory.restrictScalars K R (TruncatedCategory D Sc cutoff N)
  { degree := truncatedDegreeOver D sy 𝒜 Sc hP cutoff N
    isInternal_degree := truncatedDegreeOver_internal D sy 𝒜 Sc hP cutoff N
    proj_mem_degree := by
      rintro v w n _ p ⟨a, ha, rfl⟩
      letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
      letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
      letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
      rw [Supercategory.proj_restrictScalars K R (TruncatedCategory D Sc cutoff N),
        truncatedCategory_proj, truncatedProj_mk]
      refine mkQ_mem_truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ?_
      rw [← Supercategory.proj_restrictScalars K R (ELVCoefficientCategory D Sc cutoff)]
      exact proj_mem_degree p ha
    id_mem_degree := fun v => by
      letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
      letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
      letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
      exact mkQ_mem_truncatedDegreeOver D sy 𝒜 Sc hP cutoff N
        (id_mem_degree (R := K) (obj D Sc cutoff v.word))
    comp_mem_degree := by
      rintro v t w m n _ _ ⟨a, ha, rfl⟩ ⟨b, hb, rfl⟩
      letI := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
      letI := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
      letI := elvHomGradingOver D sy 𝒜 Sc hP cutoff
      exact mkQ_mem_truncatedDegreeOver D sy 𝒜 Sc hP cutoff N (comp_mem_degree ha hb) }

end OddMath.QuiverHecke.ELV
end

end

section

/-!
# Degree support of the truncated vacuum over a graded base ring

Over a commutative `K`-algebra `R` graded by `𝒜` in degrees `0, …, b`, the Hom modules out of
the empty word in the coefficient-truncated quotient lie in degrees `0, …, b + M N`, where `M`
bounds coefficient degree against coefficient weight
(`ELV.truncatedVacuum_support_of_boundOver`). The vacuum is spanned over `R` by the
coefficient basis vectors, and homogeneous scalars of `R` shift degrees by at most `b`
(`BasisGrading.mem_iSup_of_mem_span`).

For `K = R` with the trivial grading (`b = 0`) this is `ELV.truncatedVacuum_support_of_bound`.
-/

-- `letI` keeps the restricted-scalar instances available to instance search in these proofs.
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory StringDiagrams OddMath.Diagrams GradedSupercategory

namespace OddMath.QuiverHecke.ELV

universe u

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  {K : Type u} [CommRing K] {R : Type u} [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R) [GradedAlgebra 𝒜]
  (Sc : SKM.Scalars D R)
  (hP : CoefficientGrading.IsHomogeneous 𝒜 (gdeg D sy) (pres D Sc)) (cutoff : I → ℕ) (N : ℕ)

/-- A vacuum coefficient basis class lies in its coefficient degree, over a graded base. -/
theorem vacuumClass_basis_degreeOver (a : SKM.SYM.CoefficientIndex D) :
    (vacuumClassLinear D Sc cutoff N (SKM.SYM.coefficientBasis D R a) :
        (⟨[]⟩ : TruncatedCategory D Sc cutoff N) ⟶ ⟨[]⟩) ∈
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨[]⟩ ⟨[]⟩ (SKM.SYM.coefficientDegree D sy a) :=
  mkQ_mem_truncatedDegreeOver D sy 𝒜 Sc hP cutoff N
    (coefficientIdentity_basis_degreeOver D sy 𝒜 Sc hP cutoff [] a)

/-- **Vacuum support over a graded base.** If `𝒜` lives in degrees `0, …, b`, the truncated
Homs out of the empty word lie in degrees `0, …, b + M N`. -/
theorem truncatedVacuum_support_of_boundOver (b : ℤ)
    (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥) (M : ℤ) (hM : 0 ≤ M)
    (hbound : ∀ a, SKM.SYM.coefficientDegree D sy a ≤ M * SKM.SYM.coefficientWeight D a)
    (w : List I) (z : (⟨[]⟩ : TruncatedCategory D Sc cutoff N) ⟶ ⟨w⟩) :
    letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
    z ∈ ⨆ n ∈ Set.Icc (0 : ℤ) (b + M * N),
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨[]⟩ ⟨w⟩ n := by
  letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
  by_cases hw : w = []
  · subst w
    obtain ⟨f, rfl⟩ := (truncatedIdeal D Sc cutoff N [] []).mkQ_surjective z
    let S : Set ((⟨[]⟩ : TruncatedCategory D Sc cutoff N) ⟶ ⟨[]⟩) :=
      Set.range fun a => vacuumClassLinear D Sc cutoff N (SKM.SYM.coefficientBasis D R a)
    have hspan : (truncatedIdeal D Sc cutoff N [] []).mkQ f ∈ Submodule.span R S := by
      have hf := vacuum_hom_span D Sc cutoff f
      induction hf using Submodule.span_induction with
      | mem f hf =>
        obtain ⟨a, rfl⟩ := hf
        change vacuumClassLinear D Sc cutoff N a ∈ _
        have ha : a ∈ Submodule.span R (Set.range (SKM.SYM.coefficientBasis D R)) := by
          rw [Module.Basis.span_eq]; trivial
        induction ha using Submodule.span_induction with
        | mem a ha =>
          obtain ⟨c, rfl⟩ := ha
          exact Submodule.subset_span ⟨c, rfl⟩
        | zero => simpa only [map_zero] using Submodule.zero_mem _
        | add a a' _ _ ha ha' => simpa only [map_add] using Submodule.add_mem _ ha ha'
        | smul c a _ ha => simpa only [map_smul] using Submodule.smul_mem _ c ha
      | zero => simpa only [map_zero] using Submodule.zero_mem _
      | add a a' _ _ ha ha' => simpa only [map_add] using Submodule.add_mem _ ha ha'
      | smul c a _ ha => simpa only [map_smul] using Submodule.smul_mem _ c ha
    refine BasisGrading.mem_iSup_of_mem_span 𝒜
      (truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨[]⟩ ⟨[]⟩)
      (fun hr hy => smul_mem_truncatedDegreeOver D sy 𝒜 Sc hP cutoff N hr hy)
      (T := Set.Icc (0 : ℤ) (M * N)) h𝒜 ?_ ?_ hspan
    · rintro e ⟨he₀, he₁⟩ t ⟨ht₀, ht₁⟩
      exact ⟨by omega, by omega⟩
    · rintro g ⟨c, rfl⟩
      by_cases hc : N ≤ SKM.SYM.coefficientWeight D c
      · exact (congrArg (fun x => x ∈ _) (vacuumClass_basis_zero D Sc cutoff N c hc)).mpr
          (Submodule.zero_mem _)
      · have hcw : (SKM.SYM.coefficientWeight D c : ℤ) ≤ N := by
          exact_mod_cast (by omega : SKM.SYM.coefficientWeight D c ≤ N)
        have hn : SKM.SYM.coefficientDegree D sy c ∈ Set.Icc (0 : ℤ) (M * N) :=
          ⟨SKM.SYM.coefficientDegree_nonneg D sy c,
            (hbound c).trans (mul_le_mul_of_nonneg_left hcw hM)⟩
        exact Submodule.mem_iSup_of_mem (SKM.SYM.coefficientDegree D sy c)
          (Submodule.mem_iSup_of_mem hn (vacuumClass_basis_degreeOver D sy 𝒜 Sc hP cutoff N c))
  · obtain ⟨f, rfl⟩ := (truncatedIdeal D Sc cutoff N [] w).mkQ_surjective z
    rw [vacuum_hom_eq_zero D Sc cutoff hw f, map_zero]
    exact Submodule.zero_mem _

end OddMath.QuiverHecke.ELV
end

end
