import OddMath.QuiverHecke.CyclotomicAction.ProbeMixed
import OddMath.QuiverHecke.CyclotomicAction.GlobalWeightRouquier
import OddMath.QuiverHecke.CyclotomicAction.ContentMatrix
import OddMath.QuiverHecke.CyclotomicAction.VacuumGrading
import OddMath.QuiverHecke.CyclotomicAction.InductionGridMate
import OddMath.QuiverHecke.CyclotomicAction.ProbeScalarModules
import OddMath.QuiverHecke.CyclotomicAction.AppendContent
import OddMath.QuiverHecke.CyclotomicAction.CapInputMatrices
import OddMath.QuiverHecke.CyclotomicAction.ContentModule
import OddMath.QuiverHecke.CyclotomicAction.ModuleInduction
import OddMath.SKM.RouquierNormalizedHomAdjunction
import OddMath.QuiverHecke.CyclotomicAction.WeightedAppend
import OddMath.QuiverHecke.CyclotomicAction.InductionMixed
import OddMath.QuiverHecke.SwappedVacuum.InverseCapMoments
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Category.ModuleCat.Basic
import OddMath.QuiverHecke.CyclotomicAction.ContentAppend
import OddMath.Algebra.FiniteSuperspace
import OddMath.Algebra.MatrixInverseTransport

/-!
# Probe vacuum charts

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

/-! # The OLD probe at canonical multiset contents

`SwappedDetectingFamily` §2: exact multiset blocks use the actual old append
with its prescribed target index. Scalar evaluation is preserved by those
literal induction and restriction functors, without any coefficient-power
truncation or arbitrary-old-module dot invertibility assertion.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct
namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)
  (ν : List I) (i : I) (μ : List I) (h : (i :: ν).Perm μ)
local notation "cut" => probeCutoff D m
local notation "J" => oldContentAppendTo D Sc cut ν i μ h
local notation "A" => SKM.SYM.ELVCoefficientAlgebra (k := k) D cut
local notation "ev" => SKM.SYM.elvScalarEvaluation D cut (probeScalarValues D m) (probeScalarValues_vanish D m)

/-- The chosen append with a stored target retains every full coefficient. -/
theorem probeOldCoefficient_appendTo (v : OldContentCategory D Sc cut ν) (c : A) :
    (J).map (probeOldCoefficient D m Sc ν v c) =
      probeOldCoefficient D m Sc μ ((J).obj v) c :=
  probeOldCoefficient_append D m Sc ν i v c

/-- The actual retargeted append induction preserves scalar evaluation. -/
theorem probeOldAppendToInduced_evaluatesCoefficients
    (N : Superfunctor k (OldContentCategory D Sc cut ν) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc ν N) :
    ProbeEvaluatesCoefficients D m Sc μ (induced J N) := by
  intro t c
  let L := induced J N
  change L.toFunctor.map (probeOldCoefficient D m Sc μ t c) = ev c • 𝟙 (L.obj t)
  refine DirectSum.Decomposition.inductionOn (SKM.SYM.elvCoefficientParity D cut) ?_ ?_ ?_ c
  · rw [probeOldCoefficient_zero, L.toFunctor.map_zero, map_zero, zero_smul]
  · intro p c
    change postcompose J N.toFunctor (probeOldCoefficient D m Sc μ t c.val) = ev c.val • LinearMap.id
    apply hom_ext
    intro v g b
    rw [postcompose_tensor, probeOldCoefficient_slide D m Sc μ c.property]
    have hc : probeOldCoefficient D m Sc μ ((J).obj v) c.val =
        (J).map (probeOldCoefficient D m Sc ν v c.val) :=
      (probeOldCoefficient_appendTo D Sc m ν i μ h v c.val).symm
    rw [hc, balance, hN v c.val]
    change tensor J N.toFunctor v (twist k p g) (ev c.val • b) =
      ev c.val • tensor J N.toFunctor v g b
    rcases parity_eq_zero_or_one p with rfl | rfl
    · rw [twist_zero]
      simp only [tensor, TensorProduct.tmul_smul, map_smul]
    · have hc : ev c.val = 0 := SKM.SYM.elvScalarEvaluation_odd_zero D cut
        (probeScalarValues D m) (probeScalarValues_vanish D m) c.property
      simp only [hc, zero_smul, tensor, TensorProduct.tmul_zero, map_zero]
  · intro c d hc hd
    rw [probeOldCoefficient_add, L.toFunctor.map_add, hc, hd, map_add, add_smul]

/-- Restriction along the same retargeted append retains scalar evaluation. -/
theorem probeOldAppendToRestriction_evaluatesCoefficients
    (N : Superfunctor k (OldContentCategory D Sc cut μ) (SVec k))
    (hN : ProbeEvaluatesCoefficients D m Sc μ N) :
    ProbeEvaluatesCoefficients D m Sc ν ((restriction J).obj N) := by
  intro v c
  change N.toFunctor.map ((J).map (probeOldCoefficient D m Sc ν v c)) = _
  rw [probeOldCoefficient_appendTo]
  exact hN ((J).obj v) c

/-- The selected induction uses literal append with the specified target list. -/
def probeEvaluatedAppendTo :
    ProbeEvaluatedModules D Sc m ν ⥤ ProbeEvaluatedModules D Sc m μ where
  obj N := ⟨induced J N.obj, probeOldAppendToInduced_evaluatesCoefficients D Sc m ν i μ h N.obj N.property⟩
  map f := ⟨(induction J).map f.hom⟩
  map_id N := InducedCategory.hom_ext ((induction J).map_id N.obj)
  map_comp f g := InducedCategory.hom_ext ((induction J).map_comp f.hom g.hom)

/-- The selected restriction is induced by the identical append functor. -/
def probeEvaluatedRestrictTo :
    ProbeEvaluatedModules D Sc m μ ⥤ ProbeEvaluatedModules D Sc m ν where
  obj N := ⟨(restriction J).obj N.obj,
    probeOldAppendToRestriction_evaluatesCoefficients D Sc m ν i μ h N.obj N.property⟩
  map f := ⟨(restriction J).map f.hom⟩
  map_id N := InducedCategory.hom_ext ((restriction J).map_id N.obj)
  map_comp f g := InducedCategory.hom_ext ((restriction J).map_comp f.hom g.hom)

instance : (probeEvaluatedAppendTo D Sc m ν i μ h).Additive where
  map_add := InducedCategory.hom_ext ((induction J).map_add)
instance : (probeEvaluatedAppendTo D Sc m ν i μ h).Linear k where
  map_smul f r := InducedCategory.hom_ext ((induction J).map_smul r f.hom)
instance : IsSuperfunctor k (probeEvaluatedAppendTo D Sc m ν i μ h) where
  map_mem := by
    intro A₁ B₁ p f hf
    change f.hom ∈ parity (R := k) _ _ p at hf
    change (induction J).map f.hom ∈ parity (R := k) _ _ p
    exact map_mem _ hf
instance : (probeEvaluatedRestrictTo D Sc m ν i μ h).Additive where
  map_add := InducedCategory.hom_ext ((restriction J).map_add)
instance : (probeEvaluatedRestrictTo D Sc m ν i μ h).Linear k where
  map_smul f r := InducedCategory.hom_ext ((restriction J).map_smul r f.hom)
instance : IsSuperfunctor k (probeEvaluatedRestrictTo D Sc m ν i μ h) where
  map_mem := by
    intro A₁ B₁ p f hf
    change f.hom ∈ parity (R := k) _ _ p at hf
    change (restriction J).map f.hom ∈ parity (R := k) _ _ p
    exact map_mem _ hf

end OddMath.QuiverHecke

namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)

/-- Canonical multiset contents of the untruncated OLD scalar-evaluated probe. -/
abbrev ProbeCanonicalModules (β : Multiset I) := ProbeEvaluatedModules D Sc m β.toList

@[instance_reducible]
def probeCanonicalPiSupercategory (β : Multiset I) :
    PiSupercategory k (ProbeCanonicalModules D Sc m β) :=
  probeEvaluatedPiSupercategory D Sc m β.toList

end OddMath.QuiverHecke
end

end

section

/-! # The scalar-evaluated OLD probe at every weight

`SwappedDetectingFamily` §2: retain every multiset block of the original
weight group. Chosen old append induction acts at its unique predecessor,
with the zero evaluated module when no predecessor exists. Restriction
uses the same old append. No root-map injectivity or finiteness is assumed.
-/
noncomputable section
open scoped Classical
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke
open ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ)

/-- The zero functor on the actual OLD canonical content category. -/
abbrev probeOldZeroModuleFunctor (β : Multiset I) :
    OldContentCategory D Sc (probeCutoff D m) β.toList ⥤ SVec.{u} k where
  obj := fun _ => elvZeroSpace (k := k)
  map := fun _ => 0
  map_id := by intro v; apply SVec.hom_ext; intro x; exact Subsingleton.elim _ _
  map_comp := by intros; apply SVec.hom_ext; intro x; exact Subsingleton.elim _ _

instance (β : Multiset I) : (probeOldZeroModuleFunctor D Sc m β).Additive where
  map_add := by intros; apply SVec.hom_ext; intro x; exact Subsingleton.elim _ _
instance (β : Multiset I) : (probeOldZeroModuleFunctor D Sc m β).Linear k where
  map_smul := by intros; apply SVec.hom_ext; intro x; exact Subsingleton.elim _ _
instance (β : Multiset I) : IsSuperfunctor k (probeOldZeroModuleFunctor D Sc m β) where
  map_mem _ := Submodule.zero_mem _

/-- An absent predecessor contributes the genuine zero scalar-evaluated module. -/
abbrev probeOldZeroModule (β : Multiset I) : ProbeCanonicalModules D Sc m β :=
  ⟨⟨probeOldZeroModuleFunctor D Sc m β⟩, by
    intro v c
    apply SVec.hom_ext
    intro x
    exact Subsingleton.elim _ _⟩

theorem probeOldZeroModule_isZero (β : Multiset I) :
    Limits.IsZero (probeOldZeroModule D Sc m β) := by
  apply (Limits.IsZero.iff_id_eq_zero _).mpr
  apply InducedCategory.hom_ext
  apply Superfunctor.hom_ext
  intro p v
  apply SVec.hom_ext
  intro x
  exact Subsingleton.elim _ _

section ZeroFunctor
variable {C : Type*} [Category C] [Preadditive C] [Linear k C] [Supercategory k C]

def probeOldZeroFunctor (β : Multiset I) : C ⥤ ProbeCanonicalModules D Sc m β :=
  (Functor.const C).obj (probeOldZeroModule D Sc m β)

instance (β : Multiset I) : (probeOldZeroFunctor D Sc m (C := C) β).Additive where
  map_add := (probeOldZeroModule_isZero D Sc m β).eq_of_src _ _
instance (β : Multiset I) : (probeOldZeroFunctor D Sc m (C := C) β).Linear k where
  map_smul _ _ := (probeOldZeroModule_isZero D Sc m β).eq_of_src _ _
instance (β : Multiset I) : IsSuperfunctor k (probeOldZeroFunctor D Sc m (C := C) β) where
  map_mem {_ _ _ f} _ := by
    rw [(probeOldZeroModule_isZero D Sc m β).eq_of_src
      ((probeOldZeroFunctor D Sc m β).map f) 0]
    exact Submodule.zero_mem _
end ZeroFunctor

/-- All content blocks of one original weight; no quotient of the weight group. -/
abbrev ProbeOldWeightProduct (Λ x : X) :=
  ∀ β : WeightBlocks D Λ x, ProbeCanonicalModules D Sc m β.1

@[instance_reducible]
def probeOldWeightPi (Λ x : X) : PiSupercategory k (ProbeOldWeightProduct D Sc m Λ x) :=
  letI := fun β : WeightBlocks D Λ x => probeCanonicalPiSupercategory D Sc m β.1
  productPiSupercategory _

abbrev probeOldWeightSpace (Λ x : X) : PiSCat.{u, u, u + 1} k :=
  letI := probeOldWeightPi D Sc m Λ x
  PiSCat.of k (ProbeOldWeightProduct D Sc m Λ x)

section Weight
variable (i : I) (Λ : X) {x y : X} (h : x + D.α i = y)

/-- The selected append between actual OLD multiset representatives. -/
abbrev probeOldBlockAppend (β : WeightBlocks D Λ x) :=
  oldContentAppendTo D Sc (probeCutoff D m) β.1.toList i
    (blockSucc D Λ i h β).1.toList
    (by
      apply Multiset.coe_eq_coe.mp
      rw [Multiset.coe_toList]
      change {i} + (β.1.toList : Multiset I) = (blockSucc D Λ i h β).1
      rw [Multiset.coe_toList, blockSucc_val])

abbrev probeOldBlockInd (β : WeightBlocks D Λ x) :
    Superfunctor k (ProbeCanonicalModules D Sc m β.1)
      (ProbeCanonicalModules D Sc m (blockSucc D Λ i h β).1) :=
  ⟨probeEvaluatedAppendTo D Sc m β.1.toList i (blockSucc D Λ i h β).1.toList
    (by
      apply Multiset.coe_eq_coe.mp
      rw [Multiset.coe_toList]
      change {i} + (β.1.toList : Multiset I) = (blockSucc D Λ i h β).1
      rw [Multiset.coe_toList, blockSucc_val])⟩

abbrev probeOldBlockRes (β : WeightBlocks D Λ x) :
    Superfunctor k (ProbeCanonicalModules D Sc m (blockSucc D Λ i h β).1)
      (ProbeCanonicalModules D Sc m β.1) :=
  ⟨probeEvaluatedRestrictTo D Sc m β.1.toList i (blockSucc D Λ i h β).1.toList
    (by
      apply Multiset.coe_eq_coe.mp
      rw [Multiset.coe_toList]
      change {i} + (β.1.toList : Multiset I) = (blockSucc D Λ i h β).1
      rw [Multiset.coe_toList, blockSucc_val])⟩

def probeOldBlockEval (β : WeightBlocks D Λ x) :
    Superfunctor k (ProbeOldWeightProduct D Sc m Λ x)
      (ProbeCanonicalModules D Sc m β.1) := ⟨Pi.eval _ β⟩

private def probeOldInductionVia (δ : WeightBlocks D Λ y) (β : WeightBlocks D Λ x)
    (hβ : blockSucc D Λ i h β = δ) :
    Superfunctor k (ProbeOldWeightProduct D Sc m Λ x)
      (ProbeCanonicalModules D Sc m δ.1) := by
  subst δ
  exact (probeOldBlockEval D Sc m Λ β).comp (probeOldBlockInd D Sc m i Λ h β)

private theorem probeOldInductionVia_eq (δ : WeightBlocks D Λ y)
    (β β' : WeightBlocks D Λ x) (hβ : blockSucc D Λ i h β = δ)
    (hβ' : blockSucc D Λ i h β' = δ) :
    probeOldInductionVia D Sc m i Λ h δ β hβ =
      probeOldInductionVia D Sc m i Λ h δ β' hβ' := by
  obtain rfl := blockSucc_injective D Λ i h (hβ.trans hβ'.symm)
  rfl

def probeOldInductionComponent (δ : WeightBlocks D Λ y) :
    Superfunctor k (ProbeOldWeightProduct D Sc m Λ x)
      (ProbeCanonicalModules D Sc m δ.1) :=
  if hδ : ∃ β, blockSucc D Λ i h β = δ then
    probeOldInductionVia D Sc m i Λ h δ hδ.choose hδ.choose_spec
  else ⟨probeOldZeroFunctor D Sc m δ.1⟩

theorem probeOldInductionComponent_blockSucc (β : WeightBlocks D Λ x) :
    probeOldInductionComponent D Sc m i Λ h (blockSucc D Λ i h β) =
      (probeOldBlockEval D Sc m Λ β).comp (probeOldBlockInd D Sc m i Λ h β) := by
  unfold probeOldInductionComponent
  split
  · rename_i hc
    exact probeOldInductionVia_eq D Sc m i Λ h _ _ β hc.choose_spec rfl
  · rename_i hn
    exact absurd (⟨β, rfl⟩ : ∃ c, blockSucc D Λ i h c = blockSucc D Λ i h β) hn

theorem probeOldInductionComponent_isZero (δ : WeightBlocks D Λ y)
    (hδ : ¬ ∃ β, blockSucc D Λ i h β = δ)
    (M : ProbeOldWeightProduct D Sc m Λ x) :
    Limits.IsZero ((probeOldInductionComponent D Sc m i Λ h δ).obj M) := by
  unfold probeOldInductionComponent
  split
  · exact absurd ‹_› hδ
  · exact probeOldZeroModule_isZero D Sc m δ.1

def probeOldEFunctor : ProbeOldWeightProduct D Sc m Λ x ⥤
    ProbeOldWeightProduct D Sc m Λ y :=
  Functor.pi' fun δ => (probeOldInductionComponent D Sc m i Λ h δ).toFunctor

instance : (probeOldEFunctor D Sc m i Λ h).Additive where
  map_add := funext fun δ => (probeOldInductionComponent D Sc m i Λ h δ).toFunctor.map_add
instance : (probeOldEFunctor D Sc m i Λ h).Linear k where
  map_smul f r := funext fun δ =>
    (probeOldInductionComponent D Sc m i Λ h δ).toFunctor.map_smul r f
instance : IsSuperfunctor k (probeOldEFunctor D Sc m i Λ h) where
  map_mem hf δ := IsSuperfunctor.map_mem
    (F := (probeOldInductionComponent D Sc m i Λ h δ).toFunctor) hf

def probeOldE : probeOldWeightSpace D Sc m Λ x ⟶ probeOldWeightSpace D Sc m Λ y :=
  ⟨probeOldEFunctor D Sc m i Λ h⟩

def probeOldF : probeOldWeightSpace D Sc m Λ y ⟶ probeOldWeightSpace D Sc m Λ x :=
  ⟨productFunctor (fun δ : WeightBlocks D Λ y => ProbeCanonicalModules D Sc m δ.1)
    (blockSucc D Λ i h) (fun β : WeightBlocks D Λ x => ProbeCanonicalModules D Sc m β.1)
    (fun β => (probeOldBlockRes D Sc m i Λ h β).toFunctor)⟩

theorem probeOldInductionComponent_obj_blockSucc (β : WeightBlocks D Λ x)
    (M : ProbeOldWeightProduct D Sc m Λ x) :
    (probeOldInductionComponent D Sc m i Λ h (blockSucc D Λ i h β)).obj M =
      (probeOldBlockInd D Sc m i Λ h β).obj (M β) := by
  rw [probeOldInductionComponent_blockSucc]
  rfl

theorem probeOldInductionComponent_map_blockSucc (β : WeightBlocks D Λ x)
    {M M' : ProbeOldWeightProduct D Sc m Λ x} (f : M ⟶ M') :
    (probeOldInductionComponent D Sc m i Λ h (blockSucc D Λ i h β)).map f =
      eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M) ≫
        (probeOldBlockInd D Sc m i Λ h β).map (f β) ≫
          eqToHom (probeOldInductionComponent_obj_blockSucc D Sc m i Λ h β M').symm :=
  superfunctor_map_of_eq (probeOldInductionComponent_blockSucc D Sc m i Λ h β) f

end Weight
end OddMath.QuiverHecke
end

end

section

/-! # Coefficient extraction from the prescribed unit-matrix inverse

Research issue #345, toward the normalized vacuum bubbles in
`docs/Nondegeneracy/SwappedVacuumNonpositiveBubbles.md`, §§2–4.
The inverse rows of the actual ordinary-unit/dotted-unit matrix give the
coefficient-extraction window on every old supermodule. The rows retain
the prescribed parity-shifted source coordinates; no independent
coefficient-extraction functional or basis hypothesis is assumed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor.TensorMatrixCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (M : Superfunctor k (OldCategory D Sc cutoff) (SVec k))

/-- A selected coefficient row of the prescribed inverse. Its target is the
literal shifted source summand, including the mate summand at `none`. -/
def moduleUnitCoefficientRow (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (a : Option (Fin (contentUnitCount D cutoff i (t.word : Multiset I)))) :
    mateTargetSpace D Sc cutoff i M t ⟶
      (unitMatrixFamily D Sc cutoff i M
        (contentUnitCount D cutoff i (t.word : Multiset I)) a).obj t :=
  (LinearMap.proj a).comp ((moduleUnitMatrixIso D Sc cutoff M i t hh).inv)

/-- The inverse row extracts its literal source coordinate after the whole
prescribed matrix, without changing or rescaling any entry. -/
theorem moduleUnitCoefficientRow_component (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (a : Option (Fin (contentUnitCount D cutoff i (t.word : Multiset I))))
    (z : unitMatrixSourceSpace D Sc cutoff i M
      (contentUnitCount D cutoff i (t.word : Multiset I)) t) :
    moduleUnitCoefficientRow D Sc cutoff M i t hh a
      (unitMatrixComponent D Sc cutoff i M
        (contentUnitCount D cutoff i (t.word : Multiset I)) t z) = z a := by
  have h := congrArg (fun f : unitMatrixSourceSpace D Sc cutoff i M
      (contentUnitCount D cutoff i (t.word : Multiset I)) t ⟶
        unitMatrixSourceSpace D Sc cutoff i M
          (contentUnitCount D cutoff i (t.word : Multiset I)) t => f z)
    (moduleUnitMatrixIso D Sc cutoff M i t hh).hom_inv_id
  rw [moduleUnitMatrixIso_hom] at h
  have h' : (moduleUnitMatrixIso D Sc cutoff M i t hh).inv
      (unitMatrixComponent D Sc cutoff i M
        (contentUnitCount D cutoff i (t.word : Multiset I)) t z) = z := by
    simpa only [SVec.comp_apply, SVec.id_apply] using h
  exact congrFun h' a

private theorem assembled_single {ι : Type} [Fintype ι] [DecidableEq ι]
    (V : ι → SVec k) (W : SVec k) (f : ∀ a, V a ⟶ W) (a : ι) (z : V a) :
    OddMath.FiniteSuperspace.assembleColumns V W f (Pi.single a z) = f a z := by
  change (∑ b, f b ((Pi.single a z : (b : ι) → V b) b)) = _
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    rw [Pi.single_eq_of_ne hb]
    exact map_zero _
  · simp

private theorem unitMatrixComponent_single (i : I) (m : ℕ)
    (t : OldCategory D Sc cutoff) (a : Option (Fin m))
    (z : (unitMatrixFamily D Sc cutoff i M m a).obj t) :
    unitMatrixComponent D Sc cutoff i M m t (Pi.single a z) =
      (unitMatrixEntry D Sc cutoff i M m a).total t z := by
  classical
  exact assembled_single (fun a => (unitMatrixFamily D Sc cutoff i M m a).obj t)
    (mateTargetSpace D Sc cutoff i M t)
    (fun a => (unitMatrixEntry D Sc cutoff i M m a).total t) a z

/-- Each inverse coefficient row is a left inverse to its prescribed
dotted-unit column (or the first mate column). -/
theorem moduleUnitCoefficientRow_entry (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (a : Option (Fin (contentUnitCount D cutoff i (t.word : Multiset I))))
    (z : (unitMatrixFamily D Sc cutoff i M
      (contentUnitCount D cutoff i (t.word : Multiset I)) a).obj t) :
    moduleUnitCoefficientRow D Sc cutoff M i t hh a
      ((unitMatrixEntry D Sc cutoff i M
        (contentUnitCount D cutoff i (t.word : Multiset I)) a).total t z) = z := by
  classical
  have h := moduleUnitCoefficientRow_component D Sc cutoff M i t hh a (Pi.single a z)
  rw [unitMatrixComponent_single] at h
  simpa only [Pi.single_eq_same] using h

/-- Distinct inverse rows kill each prescribed shifted unit/mate column. -/
theorem moduleUnitCoefficientRow_entry_ne (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (a b : Option (Fin (contentUnitCount D cutoff i (t.word : Multiset I))))
    (hab : a ≠ b)
    (z : (unitMatrixFamily D Sc cutoff i M
      (contentUnitCount D cutoff i (t.word : Multiset I)) b).obj t) :
    moduleUnitCoefficientRow D Sc cutoff M i t hh a
      ((unitMatrixEntry D Sc cutoff i M
        (contentUnitCount D cutoff i (t.word : Multiset I)) b).total t z) = 0 := by
  classical
  have h := moduleUnitCoefficientRow_component D Sc cutoff M i t hh a (Pi.single b z)
  rw [unitMatrixComponent_single] at h
  simpa only [Pi.single_eq_of_ne hab] using h

/-- The extraction row is even in its prescribed shifted coordinates. -/
theorem moduleUnitCoefficientRow_even (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (a : Option (Fin (contentUnitCount D cutoff i (t.word : Multiset I)))) :
    moduleUnitCoefficientRow D Sc cutoff M i t hh a ∈ parity (R := k)
      (mateTargetSpace D Sc cutoff i M t)
      ((unitMatrixFamily D Sc cutoff i M
        (contentUnitCount D cutoff i (t.word : Multiset I)) a).obj t) 0 := by
  apply SVec.mem_parityHom_of_apply_mem
  intro q z hz
  rw [add_zero]
  have h := SVec.apply_mem_part
    (moduleUnitMatrixIso_inv_even D Sc cutoff M i t hh) hz
  rw [add_zero] at h
  change (moduleUnitMatrixIso D Sc cutoff M i t hh).inv z ∈
    (OddMath.FiniteSuperspace.product fun a => (unitMatrixFamily D Sc cutoff i M
      (contentUnitCount D cutoff i (t.word : Multiset I)) a).obj t).part q at h
  exact (OddMath.FiniteSuperspace.mem_product_part _ q _).mp h a

local instance unitCoefficientRowsPi :
    PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory

/-- Removing the selected source shift gives a coefficient functional on
the original module component. The shift is the prescribed r-th-dot shift. -/
def moduleUnitCoefficient (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (t.word : Multiset I))) :
    mateTargetSpace D Sc cutoff i M t →ₗ[k] M.obj t :=
  (moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
    (r.val • D.parity i)).iso M) t).toLinearMap.comp
      (moduleUnitCoefficientRow D Sc cutoff M i t hh (some r))

private theorem homogeneous_total_mem
    {F G : Superfunctor k (OldCategory D Sc cutoff) (SVec k)}
    {f : F ⟶ G} {p : ZMod 2} (hf : f ∈ parity (R := k) F G p)
    (t : OldCategory D Sc cutoff) :
    f.total t ∈ parity (R := k) (F.obj t) (G.obj t) p := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · have h : f.total t = f.app 0 t := by
      rw [SuperNatTrans.total,
        Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide), add_zero]
    rw [h]
    exact f.app_mem 0 t
  · have h : f.total t = f.app 1 t := by
      rw [SuperNatTrans.total,
        Superfunctor.app_eq_zero_of_mem hf (q := 0) (by decide), zero_add]
    rw [h]
    exact f.app_mem 1 t

private theorem homogeneous_total_eq_app
    {F G : Superfunctor k (OldCategory D Sc cutoff) (SVec k)}
    {f : F ⟶ G} {p : ZMod 2} (hf : f ∈ parity (R := k) F G p)
    (t : OldCategory D Sc cutoff) : f.total t = f.app p t := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SuperNatTrans.total,
      Superfunctor.app_eq_zero_of_mem hf (q := 1) (by decide), add_zero]
  · rw [SuperNatTrans.total,
      Superfunctor.app_eq_zero_of_mem hf (q := 0) (by decide), zero_add]

/-- In original module coordinates the r-th coefficient functional has
the prescribed parity r*p. In particular the top vacuum row has parity
(N-1)*p; odd coefficients may not be moved through it unsigned. -/
theorem moduleUnitCoefficient_mem (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (t.word : Multiset I))) :
    moduleUnitCoefficient D Sc cutoff M i t hh r ∈ parity (R := k)
      (mateTargetSpace D Sc cutoff i M t) (M.obj t) (r.val • D.parity i) := by
  have he := homogeneous_total_mem D Sc cutoff
    ((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).hom_mem M) t
  change moduleUnitCoefficientRow D Sc cutoff M i t hh (some r) ≫
    (((SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M).hom.total t) ∈ _
  simpa only [zero_add] using comp_mem
    (moduleUnitCoefficientRow_even D Sc cutoff M i t hh (some r)) he

/-- The functional extracts the r-th literal ordinary unit/dot column,
after cancelling the canonical homogeneous comparison on its source. -/
theorem moduleUnitCoefficient_column (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (t.word : Multiset I))) (z : M.obj t) :
    moduleUnitCoefficient D Sc cutoff M i t hh r
      ((moduleUnitColumn D Sc cutoff i M r.val).total t z) = z := by
  let e := moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
    (r.val • D.parity i)).iso M) t
  let row : mateTargetSpace D Sc cutoff i M t →ₗ[k]
      (((SKM.homParityShift (k := k) (r.val • D.parity i)).obj M).obj t) :=
    moduleUnitCoefficientRow D Sc cutoff M i t hh (some r)
  let col := (moduleUnitColumn D Sc cutoff i M r.val).total t
  have hcolumn : (unitMatrixEntry D Sc cutoff i M
      (contentUnitCount D cutoff i (t.word : Multiset I)) (some r)).total t (e.symm z) = col z :=
    (unitMatrixEntry_some_total D Sc cutoff i M t _ r (e.symm z)).trans
      (congrArg col (e.apply_symm_apply z))
  have hentry := moduleUnitCoefficientRow_entry D Sc cutoff M i t hh (some r) (e.symm z)
  have hrow : row (col z) = e.symm z :=
    (congrArg row hcolumn).symm.trans hentry
  change e (row (col z)) = z
  exact (congrArg e hrow).trans (e.apply_symm_apply z)

/-- Every other low dotted-unit column is killed in the original module
coordinates. Together with the preceding equality this supplies the full
coefficient-extraction window, rather than assuming it. -/
theorem moduleUnitCoefficient_column_ne (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (r s : Fin (contentUnitCount D cutoff i (t.word : Multiset I))) (hrs : r ≠ s)
    (z : M.obj t) :
    moduleUnitCoefficient D Sc cutoff M i t hh r
      ((moduleUnitColumn D Sc cutoff i M s.val).total t z) = 0 := by
  let e := moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
    (s.val • D.parity i)).iso M) t
  let er := moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k)
    (r.val • D.parity i)).iso M) t
  let row : mateTargetSpace D Sc cutoff i M t →ₗ[k]
      (((SKM.homParityShift (k := k) (r.val • D.parity i)).obj M).obj t) :=
    moduleUnitCoefficientRow D Sc cutoff M i t hh (some r)
  let col := (moduleUnitColumn D Sc cutoff i M s.val).total t
  have hcolumn : (unitMatrixEntry D Sc cutoff i M
      (contentUnitCount D cutoff i (t.word : Multiset I)) (some s)).total t (e.symm z) = col z :=
    (unitMatrixEntry_some_total D Sc cutoff i M t _ s (e.symm z)).trans
      (congrArg col (e.apply_symm_apply z))
  have hentry := moduleUnitCoefficientRow_entry_ne D Sc cutoff M i t hh (some r) (some s)
    (by simpa only [ne_eq, Option.some.injEq] using hrs) (e.symm z)
  have hrow : row (col z) = 0 := (congrArg row hcolumn).symm.trans hentry
  change er (row (col z)) = 0
  exact (congrArg er hrow).trans (map_zero er)

/-- The coefficient-extraction window on the chosen signed induction dot
and ordinary adjunction unit, with no unit-column abstraction remaining. -/
theorem moduleUnitCoefficient_dot_window (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (t.word : Multiset I)))
    (a : ℕ) (ha : a < contentUnitCount D cutoff i (t.word : Multiset I)) (z : M.obj t) :
    moduleUnitCoefficient D Sc cutoff M i t hh r
      (((inductionDot D Sc cutoff i M ((append D Sc cutoff i).obj t)) ^ a)
        ((((BalancedInduction.adjunction (append D Sc cutoff i)).unit.app M).total t) z)) =
      if a = r.val then z else 0 := by
  have hcol := LinearMap.congr_fun (moduleUnitColumn_total D Sc cutoff i M t a) z
  change (moduleUnitColumn D Sc cutoff i M a).total t z =
    (((inductionDot D Sc cutoff i M ((append D Sc cutoff i).obj t)) ^ a)
      ((((BalancedInduction.adjunction (append D Sc cutoff i)).unit.app M).total t) z)) at hcol
  rw [← hcol]
  by_cases h : a = r.val
  · rw [ite_eq_left h, h]
    exact moduleUnitCoefficient_column D Sc cutoff M i t hh r z
  · rw [ite_eq_right h]
    exact moduleUnitCoefficient_column_ne D Sc cutoff M i t hh r ⟨a, ha⟩
      (by intro e; exact h (congrArg Fin.val e).symm) z

/-- Homogeneous endomorphisms of the output object satisfy the exact
supernatural coefficient rule. At the vacuum this is the full
exterior-coefficient superlinearity of the extraction functional. -/
theorem moduleUnitCoefficient_end_naturality (i : I) (t : OldCategory D Sc cutoff)
    (hh : 0 ≤ contentCrossingHeight D cutoff i (t.word : Multiset I))
    (r : Fin (contentUnitCount D cutoff i (t.word : Multiset I)))
    {q : ZMod 2} (f : t ⟶ t) (hf : f ∈ parity (R := k) t t q) :
    (moduleUnitCoefficient D Sc cutoff M i t hh r).comp
        (SVec.toLinearMap (((BalancedInduction.restriction (append D Sc cutoff i)).obj
          ((BalancedInduction.induction (append D Sc cutoff i)).obj M)).map f)) =
      koszulSign (r.val • D.parity i) q •
        ((SVec.toLinearMap (M.map f)).comp
          (moduleUnitCoefficient D Sc cutoff M i t hh r)) := by
  let m := contentUnitCount D cutoff i (t.word : Multiset I)
  let S := unitMatrixSourceModule D Sc cutoff M i m
  let T := (BalancedInduction.restriction (append D Sc cutoff i)).obj
    ((BalancedInduction.induction (append D Sc cutoff i)).obj M)
  let e := moduleUnitMatrixIso D Sc cutoff M i t hh
  let es := (SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).iso M
  let pr : S.obj t ⟶ (unitMatrixFamily D Sc cutoff i M m (some r)).obj t := LinearMap.proj (some r)
  have hn : S.map f ≫ e.hom = e.hom ≫ T.map f := by
    dsimp only [e]
    rw [moduleUnitMatrixIso_hom]
    exact (unitMatrixNatTrans D Sc cutoff M i m).naturality f
  have hi : T.map f ≫ e.inv = e.inv ≫ S.map f := by
    have h := congrArg (fun g => e.inv ≫ g ≫ e.inv) hn
    simpa only [Category.assoc, Iso.hom_inv_id, Iso.inv_hom_id_assoc,
      Category.comp_id] using h.symm
  have hp : S.map f ≫ pr = pr ≫ (unitMatrixFamily D Sc cutoff i M m (some r)).map f := by
    apply LinearMap.ext
    intro z
    rfl
  have hs : (unitMatrixFamily D Sc cutoff i M m (some r)).map f ≫ es.hom.total t =
      koszulSign (r.val • D.parity i) q • (es.hom.total t ≫ M.map f) := by
    have hmem := (SKM.homParityShiftDatum (k := k) (r.val • D.parity i)).hom_mem M
    rw [homogeneous_total_eq_app D Sc cutoff hmem t]
    exact es.hom.naturality (r.val • D.parity i) f hf
  change T.map f ≫ e.inv ≫ pr ≫ es.hom.total t =
    koszulSign (r.val • D.parity i) q • (e.inv ≫ pr ≫ es.hom.total t ≫ M.map f)
  rw [← Category.assoc (T.map f) e.inv, hi, Category.assoc,
    ← Category.assoc (S.map f) pr, hp, Category.assoc, hs]
  simp only [Preadditive.comp_zsmul]

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor.TensorMatrixCoordinates

namespace OddMath.QuiverHecke.ELV.VacuumCoefficient
open CyclotomicCrossingTensor CyclotomicCrossingTensor.TensorMatrixCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The old empty-word representable retains the full coefficient algebra. -/
def coefficientModule : Superfunctor k (OldCategory D Sc cutoff) (SVec k) :=
  oldRepresentable D Sc cutoff (⟨[]⟩ : OldCategory D Sc cutoff)

@[simp] theorem count (i : I) :
    contentUnitCount D cutoff i (([] : List I) : Multiset I) = cutoff i := by
  simp [contentUnitCount, contentCrossingHeight]

private theorem height (i : I) :
    0 ≤ contentCrossingHeight D cutoff i (([] : List I) : Multiset I) := by
  simp [contentCrossingHeight]

private def topSlot (i : I) (hN : 0 < cutoff i) :
    Fin (contentUnitCount D cutoff i (([] : List I) : Multiset I)) :=
  ⟨cutoff i - 1, by rw [count]; omega⟩

/-- The normalized top coefficient functional on the actual old induction
of the empty-word representable, in its original module coordinates. -/
def functional (i : I) (hN : 0 < cutoff i) :
    mateTargetSpace D Sc cutoff i (coefficientModule D Sc cutoff)
      (⟨[]⟩ : OldCategory D Sc cutoff) →ₗ[k]
        (coefficientModule D Sc cutoff).obj (⟨[]⟩ : OldCategory D Sc cutoff) :=
  moduleUnitCoefficient D Sc cutoff (coefficientModule D Sc cutoff) i ⟨[]⟩
    (height D cutoff i) (topSlot D cutoff i hN)

theorem functional_mem (i : I) (hN : 0 < cutoff i) :
    functional D Sc cutoff i hN ∈ parity (R := k)
      (mateTargetSpace D Sc cutoff i (coefficientModule D Sc cutoff) ⟨[]⟩)
      ((coefficientModule D Sc cutoff).obj ⟨[]⟩) ((cutoff i - 1) • D.parity i) :=
  moduleUnitCoefficient_mem D Sc cutoff (coefficientModule D Sc cutoff) i ⟨[]⟩
    (height D cutoff i) (topSlot D cutoff i hN)

/-- The literal signed-dot/ordinary-unit extraction window required by
the inverse-cap polynomial calculation. All its inputs are constructed. -/
theorem functional_dot_window (i : I) (hN : 0 < cutoff i)
    (a : ℕ) (ha : a < cutoff i)
    (z : (coefficientModule D Sc cutoff).obj (⟨[]⟩ : OldCategory D Sc cutoff)) :
    functional D Sc cutoff i hN
      (((inductionDot D Sc cutoff i (coefficientModule D Sc cutoff)
          ((append D Sc cutoff i).obj ⟨[]⟩)) ^ a)
        ((((BalancedInduction.adjunction (append D Sc cutoff i)).unit.app
          (coefficientModule D Sc cutoff)).total ⟨[]⟩) z)) =
      if a + 1 = cutoff i then z else 0 := by
  have he : (a = cutoff i - 1) ↔ a + 1 = cutoff i := by omega
  have h := moduleUnitCoefficient_dot_window D Sc cutoff (coefficientModule D Sc cutoff) i
    ⟨[]⟩ (height D cutoff i) (topSlot D cutoff i hN) a (by simpa only [count] using ha) z
  simpa only [functional, topSlot, he] using h

end OddMath.QuiverHecke.ELV.VacuumCoefficient
end

end

section

/-! # The nonzero empty vector of the regular probe

The probe vacuum T₀ in `SwappedActionAssembly.md`, F2, is the genuine
height-zero regular module. Its empty word-idempotent vector is nonzero
by the original affine empty-word PBW coordinate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.CyclotomicAction
namespace OddMath.QuiverHecke
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k)

variable [Fintype I] (m : I → ℕ)

/-- The original empty object in the old scalar-probe source category. -/
def probeOldVacuumObject : ELV.OldContentCategory D Sc (probeCutoff D m) [] :=
  ⟨⟨[]⟩, List.Perm.refl _⟩

/-- The literal regular height-zero probe, with its existing old Hom action. -/
abbrev probeOldVacuumRegular :=
  probeOldModule D m Sc [] (SuperBimodule.regular
    (heightParity D Sc (probePolynomial (k := k) (probeDotExponent D) m)
      (probePolynomial_parity D m) 0))

/-- The actual empty word idempotent, as a vector of its fixed submodule. -/
def probeOldVacuumVector :
    (probeOldVacuumRegular D Sc m).obj (probeOldVacuumObject D Sc m) :=
  ⟨probeOldWordIdempotent D m Sc [] (probeOldVacuumObject D Sc m), by
    change probeOldWordIdempotent D m Sc [] (probeOldVacuumObject D Sc m) *
      probeOldWordIdempotent D m Sc [] (probeOldVacuumObject D Sc m) =
        probeOldWordIdempotent D m Sc [] (probeOldVacuumObject D Sc m)
    change Hn.wordIdempotent (vacuumWord (I := I)) * Hn.wordIdempotent (vacuumWord (I := I)) =
      Hn.wordIdempotent (vacuumWord (I := I))
    exact Hn.wordIdempotent_sq _⟩

end OddMath.QuiverHecke
end

end

section

/-! # Prescribed cap rows with their canonical parity targets

DeformedMatrixComparison (2), (5) uses the actual dot-power/counit module
rows, followed by the canonical target parity coordinate. This module keeps
the given module parity actions and transports that coordinate through the
selected scalar comparison; no rescaling of a dotted cap is introduced.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u

section ShiftedRows
variable {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
local instance shiftedCapRowsModulePi : PiSupercategory k (Superfunctor k A (SVec k)) :=
  supermodulePiSupercategory

/-- The prescribed dot/counit row with its actual canonical shifted target. -/
def shiftedCapDotRow (N : Superfunctor k A (SVec k)) (n : ℕ) :
    (induction J).obj ((restriction J).obj N) ⟶
      (SKM.homParityShift (k := k) (n • p)).obj N :=
  capDotRow J hα N n ≫ ((SKM.homParityShiftDatum (k := k) (n • p)).iso N).inv

theorem shiftedCapDotRow_mem (N : Superfunctor k A (SVec k)) (n : ℕ) :
    shiftedCapDotRow J hα N n ∈ parity (R := k) _ _ 0 := by
  simpa only [shiftedCapDotRow, SKM.zmod2_add_self] using
    comp_mem (capDotRow_mem J hα N n)
      ((SKM.homParityShiftDatum (k := k) (n • p)).inv_mem N)

/-- Raw component of the given shifted module row, with its dictionaries fixed
before specializing a category or module. -/
def shiftedCapDotLinear (N : Superfunctor k A (SVec k)) (n : ℕ) (w : A) :
    Obj J ((restriction J).obj N).toFunctor w →ₗ[k]
      ((SKM.homParityShift (k := k) (n • p)).obj N).obj w :=
  SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (n • p)).iso N).inv.total w) ∘ₗ
    capDotLinear J hα N n w

theorem shiftedCapDotRow_total (N : Superfunctor k A (SVec k)) (n : ℕ) (w : A) :
    SVec.toLinearMap ((shiftedCapDotRow J hα N n).total w) =
      shiftedCapDotLinear J hα N n w := by
  rw [shiftedCapDotRow, Superfunctor.comp_total, SVec.toLinearMap_comp, capDotRow_total]
  rfl

end ShiftedRows

section Coordinates
variable {k A B : Type u} [CommRing k] [Category.{u} A] [Category.{u} B]
  [Preadditive A] [Linear k A] [Supercategory k A]
  [Preadditive B] [Linear k B] [Supercategory k B]
  (Q : A ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  (M : Superfunctor k B (SVec k)) (N : Superfunctor k A (SVec k))
  (e : (restriction Q).obj M ≅ N)
local instance shiftedCapCoordinateSourcePi : PiSupercategory k (Superfunctor k A (SVec k)) :=
  supermodulePiSupercategory
local instance shiftedCapCoordinateTargetPi : PiSupercategory k (Superfunctor k B (SVec k)) :=
  supermodulePiSupercategory

end Coordinates

section Comparison
variable {k C A D B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} D] [Preadditive D] [Linear k D] [Supercategory k D]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (T : D ⥤ B) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  (Q : A ⥤ B) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  {β : ∀ s, T.obj s ⟶ T.obj s} (hβ : IsSupernatural k p β)
  (M : Superfunctor k B (SVec k)) (N : Superfunctor k A (SVec k))
  (e : (restriction Q).obj M ≅ N)
local instance shiftedCapComparisonSourcePi : PiSupercategory k (Superfunctor k A (SVec k)) := supermodulePiSupercategory
local instance shiftedCapComparisonTargetPi : PiSupercategory k (Superfunctor k B (SVec k)) := supermodulePiSupercategory

end Comparison
end OddMath.QuiverHecke.ELV.BalancedInduction

namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I)
  (N : Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc (i :: ν) N)
local notation "J" => ELV.oldContentAppend D Sc (probeCutoff D m) ν i
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "U" => probeOldOrdinaryFunctor D Sc m (i :: ν)
local notation "O" => probeOrdinaryModuleSuperfunctor D Sc m (i :: ν) N hN
local notation "R" => Functor.obj (restriction J) N
local notation "hR" => probeOldRestriction_evaluatesCoefficients D Sc m ν i N hN
local notation "c" => eqToIso (probeOrdinaryRestrictionModule_eq D Sc m ν i N hN)
local notation "e" => eqToIso (probeOrdinaryModuleSuperfunctor_restrict D Sc m (i :: ν) N hN)
local instance scalarShiftedCapOldPi : PiSupercategory k
    (Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) (SVec k)) :=
  supermodulePiSupercategory
local instance scalarShiftedCapOrdinaryPi : PiSupercategory k
    (Superfunctor k (OrdinaryContentCategory D Sc
      (probePolynomial (k := k) (probeDotExponent D) m) (i :: ν)) (SVec k)) :=
  supermodulePiSupercategory

end OddMath.QuiverHecke

namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
local instance capMatrixEntryComparisonPi : PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Prescribed unit columns with their canonical parity sources

DeformedMatrixComparison (1), (4) uses the given unit/dot columns without
column rescaling. The existing canonical source parity coordinate is kept
as a module map, then transported through the scalar restriction bridge.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u

section ShiftedColumns
variable {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
local instance shiftedUnitColumnsModulePi : PiSupercategory k (Superfunctor k C (SVec k)) := supermodulePiSupercategory

/-- The actual unit/dot column with its canonical shifted source. -/
def shiftedUnitDotColumn (M : Superfunctor k C (SVec k)) (n : ℕ) :
    (SKM.homParityShift (k := k) (n • p)).obj M ⟶
      (restriction J).obj ((induction J).obj M) :=
  ((SKM.homParityShiftDatum (k := k) (n • p)).iso M).hom ≫ unitDotColumn J hα M n

theorem shiftedUnitDotColumn_mem (M : Superfunctor k C (SVec k)) (n : ℕ) :
    shiftedUnitDotColumn J hα M n ∈ parity (R := k) _ _ 0 := by
  simpa only [shiftedUnitDotColumn, SKM.zmod2_add_self] using comp_mem
    ((SKM.homParityShiftDatum (k := k) (n • p)).hom_mem M) (unitDotColumn_mem J hα M n)

/-- Literal component of the actual shifted column. -/
def shiftedUnitDotLinear (M : Superfunctor k C (SVec k)) (n : ℕ) (w : C) :
    ((SKM.homParityShift (k := k) (n • p)).obj M).obj w →ₗ[k] Obj J M.toFunctor (J.obj w) :=
  unitDotLinear J hα M n w ∘ₗ
    SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (n • p)).iso M).hom.total w)

theorem shiftedUnitDotColumn_total (M : Superfunctor k C (SVec k)) (n : ℕ) (w : C) :
    SVec.toLinearMap ((shiftedUnitDotColumn J hα M n).total w) =
      shiftedUnitDotLinear J hα M n w := by
  rw [shiftedUnitDotColumn, Superfunctor.comp_total, SVec.toLinearMap_comp, unitDotColumn_total]
  rfl

/-- Evaluate a given unit/dot column before specializing its coend. -/
theorem unitDotLinear_apply (M : Superfunctor k C (SVec k)) (n : ℕ) (w : C) (b : M.obj w) :
    unitDotLinear J hα M n w b = ((transformLinear hα M (J.obj w)) ^ n) (unit J M.toFunctor w b) := rfl

/-- The canonical reflexive endpoint transport changes no unit/dot column. -/
theorem endpointUnitDotLinear_refl_apply (M : Superfunctor k C (SVec k))
    (n : ℕ) (w : C) (b : M.obj w) :
    endpointUnitDotLinear J hα M n w (J.obj w) rfl b =
      ((transformLinear hα M (J.obj w)) ^ n) (unit J M.toFunctor w b) := by
  simp only [endpointUnitDotLinear, eqToHom_refl, postcompose_id, LinearMap.comp_apply,
    LinearMap.id_apply]

private theorem unitDotPowerTransport (M : Superfunctor k C (SVec k)) (w : C)
    {W : Type u} [AddCommMonoid W] [Module k W]
    (c : Obj J M.toFunctor (J.obj w) →ₗ[k] W) (g : Module.End k W)
    (v : M.obj w →ₗ[k] W)
    (hD : c ∘ₗ transformLinear hα M (J.obj w) = g ∘ₗ c)
    (hU : c ∘ₗ unit J M.toFunctor w = v) (n : ℕ) :
    c ∘ₗ unitDotLinear J hα M n w = (g ^ n) ∘ₗ v := by
  ext b
  have hp := intertwine_pow_apply c (transformLinear hα M (J.obj w)) g
    (fun x => LinearMap.congr_fun hD x) n (unit J M.toFunctor w b)
  exact hp.trans (congrArg (g ^ n) (LinearMap.congr_fun hU b))

private theorem endpointUnitDotLinear_refl (M : Superfunctor k C (SVec k))
    (n : ℕ) (w : C) : endpointUnitDotLinear J hα M n w (J.obj w) rfl =
      ((transformLinear hα M (J.obj w)) ^ n) ∘ₗ unit J M.toFunctor w := by
  ext b
  exact endpointUnitDotLinear_refl_apply J hα M n w b

end ShiftedColumns

section Coordinates
variable {k C D : Type u} [CommRing k] [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (Q : C ⥤ D) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  (M : Superfunctor k D (SVec k)) (N : Superfunctor k C (SVec k))
  (e : (restriction Q).obj M ≅ N)
local instance shiftedUnitCoordinateSourcePi : PiSupercategory k (Superfunctor k C (SVec k)) := supermodulePiSupercategory
local instance shiftedUnitCoordinateTargetPi : PiSupercategory k (Superfunctor k D (SVec k)) := supermodulePiSupercategory

end Coordinates

section Comparison
variable {k C A D B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} D] [Preadditive D] [Linear k D] [Supercategory k D]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (T : D ⥤ B) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  (Q : C ⥤ D) [Q.Additive] [Q.Linear k] [IsSuperfunctor k Q]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  {β : ∀ s, T.obj s ⟶ T.obj s} (hβ : IsSupernatural k p β)
  (M : Superfunctor k D (SVec k)) (N : Superfunctor k C (SVec k))
  (e : (restriction Q).obj M ≅ N)
local instance shiftedUnitComparisonSourcePi : PiSupercategory k (Superfunctor k C (SVec k)) := supermodulePiSupercategory
local instance shiftedUnitComparisonTargetPi : PiSupercategory k (Superfunctor k D (SVec k)) := supermodulePiSupercategory

end Comparison

end OddMath.QuiverHecke.ELV.BalancedInduction

namespace OddMath.QuiverHecke
open ELV ELV.BalancedInduction
universe u
private def unitDotCoefficient
    {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive A] [Linear k A] [Supercategory k A]
    (J : C ⥤ A) {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s}
    (s : C) (t : A) (g : J.obj s ⟶ t) : J.obj s ⟶ t := α s ≫ twist k p g

private theorem unitCoendHom_ext
    {k C A V : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
    [Preadditive A] [Linear k A] [AddCommMonoid V] [Module k V]
    (J : C ⥤ A) (M : C ⥤ SVec k) {w : A} {f g : Obj J M w →ₗ[k] V}
    (h : ∀ s (a : J.obj s ⟶ w) (b : M.obj s), f (tensor J M s a b) = g (tensor J M s a b)) :
    f = g := by
  classical
  apply LinearMap.cancel_right (Submodule.mkQ_surjective (relations J M w)) |>.mp
  apply DirectSum.linearMap_ext
  intro s
  apply TensorProduct.ext
  ext a b
  exact h s a b

private theorem unitTensorSource_congr
    {k A B : Type u} [CommRing k] [Category.{u} A] [Category.{u} B]
    [Preadditive B] [Linear k B] (K : A ⥤ B) (M : A ⥤ SVec k)
    (w : B) (v v' : A) (e : v = v') (g : K.obj v ⟶ w) (g' : K.obj v' ⟶ w)
    (b : M.obj v) (b' : M.obj v') (hg : HEq g g') (hb : HEq b b') :
    tensor K M v g b = tensor K M v' g' b' := by
  cases e
  cases hg
  cases hb
  rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)
  (N : Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc ν N) (i : I)
local notation "J" => ELV.oldContentAppend D Sc (probeCutoff D m) ν i
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "Q" => probeOldOrdinaryFunctor D Sc m ν
local notation "U" => probeOldOrdinaryFunctor D Sc m (i :: ν)
local notation "O" => probeOrdinaryModuleSuperfunctor D Sc m ν N hN

/-- The original selected append map intertwines the given signed dots. -/
theorem probeAppendComparisonLinear_dot
    (w : ELV.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :
    probeAppendComparisonLinear D Sc m ν N hN i w ∘ₗ
        probeOldContentInductionDot D Sc m ν i N w =
      transformLinear (probeOrdinaryAppendDot_supernatural D Sc m ν i) O ((U).obj w) ∘ₗ
        probeAppendComparisonLinear D Sc m ν N hN i w := by
  apply unitCoendHom_ext J N.toFunctor
  intro s g b
  have ho := probeOldContentInductionDot_tensor D Sc m ν i N s w g b
  have hq := probeAppendOrdinaryModuleIso_hom_tensor D Sc m ν N hN i s w
    (probeOldContentAppendDot D Sc m ν i s ≫ twist k (D.parity i) g) b
  have hl := (congrArg (probeAppendComparisonLinear D Sc m ν N hN i w) ho).trans hq
  have hs := probeAppendOrdinaryModuleIso_hom_tensor D Sc m ν N hN i s w g b
  have ht := transformLinear_tensor (probeOrdinaryAppendDot_supernatural D Sc m ν i) O
    ((U).obj w) ((Q).obj s) ((U).map g) b
  have hr := (congrArg (transformLinear (probeOrdinaryAppendDot_supernatural D Sc m ν i)
    O ((U).obj w)) hs).trans ht
  let aNew := unitDotCoefficient (k := k) T (p := D.parity i)
    (α := probeOrdinaryAppendDot D Sc m ν i) ((Q).obj s) ((U).obj w) ((U).map g)
  have ha : HEq ((U).map (probeOldContentAppendDot D Sc m ν i s ≫
      twist k (D.parity i) g)) aNew := by
    apply heq_of_eq
    dsimp only [aNew, unitDotCoefficient, probeOldContentAppendDot]
    rw [(U).map_comp, map_twist, probeOrdinaryAppendDot_old D Sc m ν i s]
    rfl
  have he := unitTensorSource_congr T (O).toFunctor ((U).obj w) ((Q).obj s) ((Q).obj s)
    rfl _ aNew b b ha HEq.rfl
  exact hl.trans (he.trans hr.symm)

/-- The selected append chart transports every actual unit/dot column, with
its canonical output-object identification. -/
theorem probeAppendComparisonLinear_unitDotColumn
    (w : ELV.OldContentCategory D Sc (probeCutoff D m) ν) (n : ℕ) :
    probeAppendComparisonLinear D Sc m ν N hN i ((J).obj w) ∘ₗ
        unitDotLinear J (probeOldContentAppendDot_supernatural D Sc m ν i) N n w =
      endpointUnitDotLinear T (probeOrdinaryAppendDot_supernatural D Sc m ν i) O n
        ((Q).obj w) ((U).obj ((J).obj w)) rfl := by
  have hU : probeAppendComparisonLinear D Sc m ν N hN i ((J).obj w) ∘ₗ
      unit J N.toFunctor w = unit T (O).toFunctor ((Q).obj w) := by
    ext b
    exact probeAppendOrdinaryModuleIso_hom_unit D Sc m ν N hN i w b
  have h := unitDotPowerTransport J (probeOldContentAppendDot_supernatural D Sc m ν i) N w
    (probeAppendComparisonLinear D Sc m ν N hN i ((J).obj w))
    (transformLinear (probeOrdinaryAppendDot_supernatural D Sc m ν i) O ((U).obj ((J).obj w)))
    (unit T (O).toFunctor ((Q).obj w))
    (probeAppendComparisonLinear_dot D Sc m ν N hN i ((J).obj w)) hU n
  have he := endpointUnitDotLinear_refl T (probeOrdinaryAppendDot_supernatural D Sc m ν i)
    O n ((Q).obj w)
  exact h.trans he.symm

local notation "e" => eqToIso (probeOrdinaryModuleSuperfunctor_restrict D Sc m ν N hN)
local instance scalarShiftedUnitOldPi : PiSupercategory k
    (Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k)) :=
  supermodulePiSupercategory
local instance scalarShiftedUnitOrdinaryPi : PiSupercategory k
    (Superfunctor k (OrdinaryContentCategory D Sc
      (probePolynomial (k := k) (probeDotExponent D) m) ν) (SVec k)) :=
  supermodulePiSupercategory

end OddMath.QuiverHecke

namespace OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
local instance unitMatrixEntryComparisonPi : PiSupercategory k (Superfunctor k (OldCategory D Sc cutoff) (SVec k)) :=
  supermodulePiSupercategory

end OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
end

end

section

/-! # Canonical parity coordinates for the prescribed finite matrix charts

DeformedMatrixComparison (4), (5) compares finite families of actual shifted
module values. The point chart below first removes the given source parity
coordinate, applies the selected unshifted chart, and inserts the given
target parity coordinate. The module categories and evaluation objects may
be different; their full parity actions are retained.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
variable {k C D : Type u} [CommRing k] [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (M : Superfunctor k C (SVec k)) (N : Superfunctor k D (SVec k))
  (w : C) (v : D) (e : M.obj w ≃ₗ[k] N.obj v)
local instance parityMatrixSourcePi : PiSupercategory k (Superfunctor k C (SVec k)) := supermodulePiSupercategory
local instance parityMatrixTargetPi : PiSupercategory k (Superfunctor k D (SVec k)) := supermodulePiSupercategory

/-- The selected value chart conjugated by the existing module parity coordinates. -/
def shiftedModuleValueLinearEquiv (q : ZMod 2) :
    ((SKM.homParityShift (k := k) q).obj M).obj w ≃ₗ[k]
      ((SKM.homParityShift (k := k) q).obj N).obj v :=
  (moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) q).iso M) w).trans
    (e.trans (moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) q).iso N) v).symm)

/-- Removing the target coordinate recovers exactly the chosen plain chart. -/
theorem shiftedModuleValueLinearEquiv_hom_coordinate (q : ZMod 2)
    (b : ((SKM.homParityShift (k := k) q).obj M).obj w) :
    ((SKM.homParityShiftDatum (k := k) q).iso N).hom.total v
        (shiftedModuleValueLinearEquiv M N w v e q b) =
      e (((SKM.homParityShiftDatum (k := k) q).iso M).hom.total w b) := by
  exact (moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) q).iso N) v).apply_symm_apply _

/-- Inserting the source coordinate commutes with the same chosen plain chart. -/
theorem shiftedModuleValueLinearEquiv_inv_coordinate (q : ZMod 2) (b : M.obj w) :
    shiftedModuleValueLinearEquiv M N w v e q
        (((SKM.homParityShiftDatum (k := k) q).iso M).inv.total w b) =
      ((SKM.homParityShiftDatum (k := k) q).iso N).inv.total v (e b) := by
  exact congrArg (fun x =>
    (moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) q).iso N) v).symm (e x))
      ((moduleIsoLinearEquiv ((SKM.homParityShiftDatum (k := k) q).iso M) w).apply_symm_apply b)

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Selected scalar charts for the prescribed finite matrices

DeformedMatrixComparison (4), (5) requires genuine invertible charts on the
source and target of each matrix. These are the selected scalar append
isomorphisms, including the induced restriction equality in the E/F source.
The charts are independent of the matrix's invertibility.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.ELV OddMath.QuiverHecke.ELV.BalancedInduction
namespace OddMath.QuiverHecke
universe u

section AppendCharts
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I)
  (R : Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) ν) (SVec k))
  (hR : ProbeEvaluatesCoefficients D m Sc ν R)
  (M : Superfunctor k (OrdinaryContentCategory D Sc
    (probePolynomial (k := k) (probeDotExponent D) m) ν) (SVec k))
  (c : probeOrdinaryModuleSuperfunctor D Sc m ν R hR ≅ M) (i : I)
local notation "J" => ELV.oldContentAppend D Sc (probeCutoff D m) ν i
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "U" => probeOldOrdinaryFunctor D Sc m (i :: ν)
local notation "O" => probeOrdinaryModuleSuperfunctor D Sc m ν R hR

/-- The original chosen append isomorphism on its literal old/ordinary coends. -/
def probeAppendLinearEquiv (w : ELV.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) :
    Obj J R.toFunctor w ≃ₗ[k] Obj T (O).toFunctor ((U).obj w) :=
  moduleIsoLinearEquiv (probeAppendOrdinaryModuleIso D Sc m ν R hR i) ((U).obj w)

end AppendCharts

section MatrixCharts
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (ν : List I) (i : I)
  (N : Superfunctor k (ELV.OldContentCategory D Sc (probeCutoff D m) (i :: ν)) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc (i :: ν) N)
local notation "J" => ELV.oldContentAppend D Sc (probeCutoff D m) ν i
local notation "K" => ELV.oldContentAppend D Sc (probeCutoff D m) (i :: ν) i
local notation "T" => probeOrdinaryAppend D Sc m ν i
local notation "U" => probeOldOrdinaryFunctor D Sc m (i :: ν)
local notation "O" => probeOrdinaryModuleSuperfunctor D Sc m (i :: ν) N hN
local notation "R" => Functor.obj (restriction J) N
local notation "hR" => probeOldRestriction_evaluatesCoefficients D Sc m ν i N hN
local notation "c" => eqToIso (probeOrdinaryRestrictionModule_eq D Sc m ν i N hN)

end MatrixCharts
end OddMath.QuiverHecke
end

end

section

/-! # The signed probe polynomial at vacuum content

The probe numerator used in `SwappedVacuumBubbles.md`, (5), and
`SwappedVacuumNonpositiveBubbles.md`, (8)--(9), comes from the literal
first-dot relation on the one-letter probe block. The source content here
is empty; no same-exponent last-dot assertion at arbitrary content is used.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke
universe u v
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) [Fintype I] (m : I → ℕ)

/-- At vacuum append the literal ordinary dot is the first dot, so its
original cyclotomic probe polynomial vanishes. -/
theorem probeOrdinaryVacuumDot_polynomial (i : I)
    (v : OrdinaryContentCategory D Sc (probePolynomial (k := k) (probeDotExponent D) m) []) :
    ((End.of (probeOrdinaryAppendDot D Sc m [] i v)) ^ probeDotExponent D i - 1) ^ m i = 0 := by
  obtain ⟨word, hw⟩ := v
  have hh : word = [] := List.perm_nil.mp hw
  subst word
  let s : Word I (0 + 1) := ⟨[i], rfl⟩
  let a := probePolynomial (k := k) (probeDotExponent D) m
  change (((End.of ((cycHom D Sc a [i] [i]).mkQ (dotE D Sc [i] 0)) :
    End (⟨[i], List.Perm.refl _⟩ : OrdinaryContentCategory D Sc a [i])) ^
      probeDotExponent D i - 1) ^ m i) = 0
  apply ordinaryWordEndCornerMap_injective D Sc a [i] s (List.Perm.refl _)
  rw [map_pow, map_sub, map_pow, map_one, map_zero, ordinaryWordEndCornerMap_mk]
  have h := cyclotomicWordEnd_generator D Sc a s
  simp only [a, s, probePolynomial, map_pow, map_sub, Polynomial.aeval_X, map_one] at h
  change ((cyclotomicWordEnd D Sc a s (dotE D Sc [i] 0) ^ probeDotExponent D i - 1) ^ m i) = 0 at h
  exact h

/-- The signed dot on the actual vacuum-source ordinary probe coend
satisfies the plus-one polynomial at every target and every input module. -/
theorem probeOrdinaryVacuumInductionDot_odd (i : I) (hi : D.parity i = 1)
    (M : Superfunctor k
      (OrdinaryContentCategory D Sc (probePolynomial (k := k) (probeDotExponent D) m) []) (SVec k))
    (w : OrdinaryContentCategory D Sc (probePolynomial (k := k) (probeDotExponent D) m) [i]) :
    (ELV.BalancedInduction.transformLinear
      (probeOrdinaryAppendDot_supernatural D Sc m [] i) M w ^ 2 + 1) ^ m i = 0 := by
  let J := probeOrdinaryAppend D Sc m [] i
  let a : ∀ v, End (J.obj v) := fun v => probeOrdinaryAppendDot D Sc m [] i v
  have ha : IsSupernatural k (D.parity i) a := probeOrdinaryAppendDot_supernatural D Sc m [] i
  have hn : ∀ v, (a v ^ 2 - 1) ^ m i = 0 := by
    intro v
    have h := probeOrdinaryVacuumDot_polynomial D Sc m i v
    have he : probeDotExponent D i = 2 := by rw [probeDotExponent, ite_eq_left hi]
    rw [he] at h
    exact h
  exact ELV.BalancedInduction.transformLinear_odd_probe_polynomial
    (J := J) (a := a) ha hi (m i) hn M w

end OddMath.QuiverHecke
end

end

section

/-! # An occupied vacuum probe append unit

The positive-level probe in `SwappedVacuumBubbles.md`, §1, is tested on
its canonical nonzero empty vector. The existing inverse unit matrix
splits the append unit; no new polynomial quotient presentation is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.ELV OddMath.QuiverHecke.ELV.BalancedInduction
open OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor
open OddMath.QuiverHecke.ELV.CyclotomicCrossingTensor.TensorMatrixCoordinates
namespace OddMath.QuiverHecke
universe u

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

variable [Fintype I] (m : I → ℕ)

omit [Fintype I] in
private theorem probeCutoff_pos (i : I) (hi : 0 < m i) : 0 < probeCutoff D m i := by
  change 0 < probeDotExponent D i * m i
  apply Nat.mul_pos _ hi
  unfold probeDotExponent
  split_ifs <;> decide

/-- The actual regular probe vacuum satisfies the required scalar-evaluation property. -/
theorem probeOldVacuumRegular_evaluates :
    ProbeEvaluatesCoefficients D m Sc [] (probeOldVacuumRegular D Sc m) :=
  probeOldModule_evaluatesCoefficients D m Sc [] _

end OddMath.QuiverHecke
end

end

section

/-! # Scalar following E/F and value charts on arbitrary output content

The missing-colour case of DeformedMatrixComparison (4) has no predecessor
content. These are the selected invertible following E/F and value charts
for any output content, with every prescribed unscaled unit/dot column.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open OddMath.QuiverHecke.ELV OddMath.QuiverHecke.ELV.BalancedInduction
namespace OddMath.QuiverHecke
universe u
section Generic
variable {k C A B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (K : A ⥤ B) [K.Additive] [K.Linear k] [IsSuperfunctor k K]
private theorem matrixUnit_endpoint_refl {p : ZMod 2}
    {β : ∀ s, K.obj s ⟶ K.obj s} (hβ : IsSupernatural k p β)
    (N : Superfunctor k A (SVec k)) (n : ℕ) (w : A) :
    endpointUnitDotLinear K hβ N n w (K.obj w) rfl = unitDotLinear K hβ N n w := by
  apply LinearMap.ext
  intro b
  exact (endpointUnitDotLinear_refl_apply K hβ N n w b).trans
    (unitDotLinear_apply K hβ N n w b).symm

end Generic
private theorem matrixUnit_plain_reencode
    {k V W Y : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid Y] [Module k Y]
    (c c₀ : W →ₗ[k] Y) (f : V →ₗ[k] W) (g g₀ : V →ₗ[k] Y) (v : V →ₗ[k] V)
    (hc : c = c₀) (hg : g₀ = g) (hv : ∀ b, v b = b) (h : c₀ ∘ₗ f = g₀) :
    c ∘ₗ f = g ∘ₗ v := by
  rw [hc]
  apply LinearMap.ext
  intro b
  exact (LinearMap.congr_fun h b).trans
    ((LinearMap.congr_fun hg b).trans (congrArg g (hv b)).symm)

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (m : I → ℕ) (γ : List I)
  (N : Superfunctor k (OldContentCategory D Sc (probeCutoff D m) γ) (SVec k))
  (hN : ProbeEvaluatesCoefficients D m Sc γ N)
local notation "U" => probeOldOrdinaryFunctor D Sc m γ
local notation "O" => probeOrdinaryModuleSuperfunctor D Sc m γ N hN
local notation "e" => eqToIso (probeOrdinaryModuleSuperfunctor_restrict D Sc m γ N hN)

/-- The scalar value chart on arbitrary output content. -/
def probeOutputValueLinearEquiv (w : OldContentCategory D Sc (probeCutoff D m) γ) :
    N.obj w ≃ₗ[k] (O).obj ((U).obj w) := (moduleIsoLinearEquiv e w).symm

theorem probeOutputValueLinearEquiv_symm_apply
    (w : OldContentCategory D Sc (probeCutoff D m) γ) (b : (O).obj ((U).obj w)) :
    (probeOutputValueLinearEquiv D Sc m γ N hN w).symm b = b := by
  change SVec.toLinearMap ((e).hom.total w) b = b
  simp only [SuperNatTrans.total, probeRestrictionEqToIso_hom_app,
    ↓reduceIte, one_ne_zero, add_zero, SVec.toLinearMap]
  rfl

theorem probeOutputValueLinearEquiv_apply
    (w : OldContentCategory D Sc (probeCutoff D m) γ) (b : N.obj w) :
    probeOutputValueLinearEquiv D Sc m γ N hN w b = b := by
  have h := (probeOutputValueLinearEquiv D Sc m γ N hN w).apply_symm_apply b
  have hv := probeOutputValueLinearEquiv_symm_apply D Sc m γ N hN w b
  exact (congrArg (probeOutputValueLinearEquiv D Sc m γ N hN w) hv).symm.trans h

variable (i : I)
local notation "K" => oldContentAppend D Sc (probeCutoff D m) γ i
local notation "S" => probeOrdinaryAppend D Sc m γ i

/-- The following F/E chart uses the same selected append isomorphism. -/
abbrev probeOutputFELinearEquiv (w : OldContentCategory D Sc (probeCutoff D m) γ) :=
  probeAppendLinearEquiv D Sc m γ N hN i ((K).obj w)

theorem probeOutputFELinearEquiv_hom (w : OldContentCategory D Sc (probeCutoff D m) γ) :
    (probeOutputFELinearEquiv D Sc m γ N hN i w).toLinearMap =
      probeAppendComparisonLinear D Sc m γ N hN i ((K).obj w) := rfl

/-- Every unit/dot column uses the selected scalar following and value charts,
without requiring any occurrence of i in the output content. -/
theorem probeOutputFELinearEquiv_unitDot
    (w : OldContentCategory D Sc (probeCutoff D m) γ) (n : ℕ) :
    (probeOutputFELinearEquiv D Sc m γ N hN i w).toLinearMap ∘ₗ
        unitDotLinear K (probeOldContentAppendDot_supernatural D Sc m γ i) N n w =
      unitDotLinear S (probeOrdinaryAppendDot_supernatural D Sc m γ i) O n ((U).obj w) ∘ₗ
        (probeOutputValueLinearEquiv D Sc m γ N hN w).toLinearMap := by
  have h := probeAppendComparisonLinear_unitDotColumn D Sc m γ N hN i w n
  have hEnd := matrixUnit_endpoint_refl S (probeOrdinaryAppendDot_supernatural D Sc m γ i)
    O n ((U).obj w)
  exact matrixUnit_plain_reencode _ _ _ _ _ _
    (probeOutputFELinearEquiv_hom D Sc m γ N hN i w) hEnd
    (probeOutputValueLinearEquiv_apply D Sc m γ N hN w) h

end OddMath.QuiverHecke
end

end

section

/-! # Canonical parity decoration of actual finite matrix squares

DeformedMatrixComparison (4), (5) attaches the canonical source or target
parity coordinate to independently proved plain matrix entries. The linear
kernels are stated on abstract modules before a concrete coend is inserted.
Actual scalar and weighted consumers use the selected module coordinates.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u

section GenericCoordinates
variable {k A B : Type u} [CommRing k]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (M : Superfunctor k A (SVec k)) (N : Superfunctor k B (SVec k))
  (w : A) (v : B) (e : M.obj w ≃ₗ[k] N.obj v)
local instance paritySquareSourcePi : PiSupercategory k (Superfunctor k A (SVec k)) :=
  supermodulePiSupercategory
local instance paritySquareTargetPi : PiSupercategory k (Superfunctor k B (SVec k)) :=
  supermodulePiSupercategory

theorem shiftedModuleValueLinearEquiv_source_square (q : ZMod 2) :
    SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) q).iso N).hom.total v) ∘ₗ
        (shiftedModuleValueLinearEquiv M N w v e q).toLinearMap =
      e.toLinearMap ∘ₗ SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) q).iso M).hom.total w) := by
  apply LinearMap.ext
  intro b
  exact shiftedModuleValueLinearEquiv_hom_coordinate M N w v e q b

theorem shiftedModuleValueLinearEquiv_target_square (q : ZMod 2) :
    (shiftedModuleValueLinearEquiv M N w v e q).toLinearMap ∘ₗ
        SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) q).iso M).inv.total w) =
      SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) q).iso N).inv.total v) ∘ₗ e.toLinearMap := by
  apply LinearMap.ext
  intro b
  exact shiftedModuleValueLinearEquiv_inv_coordinate M N w v e q b

end GenericCoordinates

theorem linearColumn_parity_square
    {k V W X Y A B : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid X] [Module k X] [AddCommMonoid Y] [Module k Y]
    [AddCommMonoid A] [Module k A] [AddCommMonoid B] [Module k B]
    (c : W →ₗ[k] Y) (f : V →ₗ[k] W) (g : X →ₗ[k] Y) (d : V →ₗ[k] X)
    (z : A →ₗ[k] V) (z' : B →ₗ[k] X) (s : A →ₗ[k] B)
    (o : A →ₗ[k] W) (n : B →ₗ[k] Y)
    (h : c ∘ₗ f = g ∘ₗ d) (hz : z' ∘ₗ s = d ∘ₗ z)
    (ho : o = f ∘ₗ z) (hn : n = g ∘ₗ z') : c ∘ₗ o = n ∘ₗ s := by
  rw [ho, hn]
  apply LinearMap.ext
  intro b
  exact (LinearMap.congr_fun h (z b)).trans (congrArg g (LinearMap.congr_fun hz b).symm)

theorem linearRow_parity_square
    {k V W X Y A B : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid X] [Module k X] [AddCommMonoid Y] [Module k Y]
    [AddCommMonoid A] [Module k A] [AddCommMonoid B] [Module k B]
    (c : W →ₗ[k] Y) (f : V →ₗ[k] W) (g : X →ₗ[k] Y) (d : V →ₗ[k] X)
    (z : W →ₗ[k] A) (z' : Y →ₗ[k] B) (s : A →ₗ[k] B)
    (o : V →ₗ[k] A) (n : X →ₗ[k] B)
    (h : c ∘ₗ f = g ∘ₗ d) (hz : s ∘ₗ z = z' ∘ₗ c)
    (ho : o = z ∘ₗ f) (hn : n = z' ∘ₗ g) : s ∘ₗ o = n ∘ₗ d := by
  rw [ho, hn]
  apply LinearMap.ext
  intro b
  exact (LinearMap.congr_fun hz (f b)).trans (congrArg z' (LinearMap.congr_fun h b))

theorem linearSquare_reencode
    {k V W X Y : Type u} [CommRing k]
    [AddCommMonoid V] [Module k V] [AddCommMonoid W] [Module k W]
    [AddCommMonoid X] [Module k X] [AddCommMonoid Y] [Module k Y]
    (c c₀ : W →ₗ[k] Y) (f f₀ : V →ₗ[k] W) (g g₀ : X →ₗ[k] Y) (d d₀ : V →ₗ[k] X)
    (hc : c = c₀) (hf : f = f₀) (hg : g = g₀) (hd : d = d₀)
    (h : c₀ ∘ₗ f₀ = g₀ ∘ₗ d₀) : c ∘ₗ f = g ∘ₗ d := by
  rw [hc, hf, hg, hd]
  exact h

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Finite matrices of the prescribed shifted unit columns

The missing-colour case of Brundan--Ellis (1.13) has only the finite unit
columns. Canonical parity coordinates turn the unshifted unit-column chart
square into its actual finite column square, before specializing categories
or induced module carriers.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
section Families
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
local instance unitColumnFamilyPi : PiSupercategory k (Superfunctor k C (SVec k)) :=
  supermodulePiSupercategory

/-- The finite canonical shifted value family, with no principal E/F slot. -/
def unitColumnSourceSpace (p : ZMod 2) (M : Superfunctor k C (SVec k))
    (m : ℕ) (w : C) : SVec k :=
  OddMath.FiniteSuperspace.product fun r : Fin m =>
    ((SKM.homParityShift (k := k) (r.val • p)).obj M).obj w
end Families

section Columns
variable {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  (M : Superfunctor k C (SVec k))
local instance unitColumnComponentPi : PiSupercategory k (Superfunctor k C (SVec k)) :=
  supermodulePiSupercategory

/-- The literal finite assembly of the given canonically shifted unit columns. -/
def unitColumnMatrix (m : ℕ) (w : C) :
    unitColumnSourceSpace p M m w ⟶ ((restriction J).obj ((induction J).obj M)).obj w :=
  OddMath.FiniteSuperspace.assembleColumns
    (fun r : Fin m => ((SKM.homParityShift (k := k) (r.val • p)).obj M).obj w)
    (((restriction J).obj ((induction J).obj M)).obj w)
    (fun r => (shiftedUnitDotColumn J hα M r.val).total w)

private theorem unitColumn_total (n : ℕ) (w : C) :
    SVec.toLinearMap ((shiftedUnitDotColumn J hα M n).total w) =
      unitDotLinear J hα M n w ∘ₗ
        SVec.toLinearMap (((SKM.homParityShiftDatum (k := k) (n • p)).iso M).hom.total w) :=
  shiftedUnitDotColumn_total J hα M n w

end Columns

section Coordinates
variable {k C D : Type u} [CommRing k] [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (M : Superfunctor k C (SVec k)) (N : Superfunctor k D (SVec k))
  (w : C) (v : D) (e : M.obj w ≃ₗ[k] N.obj v)
local instance unitColumnCoordinateSourcePi : PiSupercategory k (Superfunctor k C (SVec k)) :=
  supermodulePiSupercategory
local instance unitColumnCoordinateTargetPi : PiSupercategory k (Superfunctor k D (SVec k)) :=
  supermodulePiSupercategory

/-- The whole finite family chart uses the given plain value equivalence
inside each pair of canonical source/target parity coordinates. -/
def unitColumnFamilyEquiv (p : ZMod 2) (m : ℕ) :
    unitColumnSourceSpace p M m w ≃ₗ[k] unitColumnSourceSpace p N m v :=
  LinearEquiv.piCongrRight fun r : Fin m =>
    shiftedModuleValueLinearEquiv M N w v e (r.val • p)

end Coordinates

private theorem unitColumns_square
    {k : Type u} [CommRing k] {ι : Type} [Fintype ι]
    (V W : ι → SVec k) (X Y : SVec k) (e : ∀ a, V a ≃ₗ[k] W a)
    (c : X →ₗ[k] Y) (f : ∀ a, V a ⟶ X) (g : ∀ a, W a ⟶ Y)
    (h : ∀ a, c ∘ₗ SVec.toLinearMap (f a) = SVec.toLinearMap (g a) ∘ₗ (e a).toLinearMap) :
    c ∘ₗ SVec.toLinearMap (OddMath.FiniteSuperspace.assembleColumns V X f) =
      SVec.toLinearMap (OddMath.FiniteSuperspace.assembleColumns W Y g) ∘ₗ
        (LinearEquiv.piCongrRight e).toLinearMap := by
  apply LinearMap.ext
  intro x
  change c (∑ a, f a (x a)) = ∑ a, g a (e a (x a))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact LinearMap.congr_fun (h a) (x a)

section Comparison
variable {k C A D B : Type u} [CommRing k]
  [Category.{u} C] [Preadditive C] [Linear k C] [Supercategory k C]
  [Category.{u} A] [Preadditive A] [Linear k A] [Supercategory k A]
  [Category.{u} D] [Preadditive D] [Linear k D] [Supercategory k D]
  [Category.{u} B] [Preadditive B] [Linear k B] [Supercategory k B]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  (T : D ⥤ B) [T.Additive] [T.Linear k] [IsSuperfunctor k T]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)
  {β : ∀ s, T.obj s ⟶ T.obj s} (hβ : IsSupernatural k p β)
  (M : Superfunctor k C (SVec k)) (N : Superfunctor k D (SVec k))
  (w : C) (v : D) (e : M.obj w ≃ₗ[k] N.obj v)
  (c : Obj J M.toFunctor (J.obj w) →ₗ[k] Obj T N.toFunctor (T.obj v))
local instance unitColumnSquareSourcePi : PiSupercategory k (Superfunctor k C (SVec k)) :=
  supermodulePiSupercategory
local instance unitColumnSquareTargetPi : PiSupercategory k (Superfunctor k D (SVec k)) :=
  supermodulePiSupercategory

/-- Canonical parity coordinates and finite sums transport the actual unit
matrix whenever its unshifted dotted columns commute with the given charts. -/
theorem unitColumnMatrix_square
    (h : ∀ n, c ∘ₗ unitDotLinear J hα M n w = unitDotLinear T hβ N n v ∘ₗ e.toLinearMap)
    (m : ℕ) :
    c ∘ₗ SVec.toLinearMap (unitColumnMatrix J hα M m w) =
      SVec.toLinearMap (unitColumnMatrix T hβ N m v) ∘ₗ
        (unitColumnFamilyEquiv M N w v e p m).toLinearMap := by
  apply unitColumns_square
    (fun r : Fin m => ((SKM.homParityShift (k := k) (r.val • p)).obj M).obj w)
    (fun r : Fin m => ((SKM.homParityShift (k := k) (r.val • p)).obj N).obj v)
    (((restriction J).obj ((induction J).obj M)).obj w)
    (((restriction T).obj ((induction T).obj N)).obj v)
    (fun r => shiftedModuleValueLinearEquiv M N w v e (r.val • p))
    c (fun r => (shiftedUnitDotColumn J hα M r.val).total w)
    (fun r => (shiftedUnitDotColumn T hβ N r.val).total v)
  intro r
  exact linearColumn_parity_square _ _ _ _ _ _ _ _ _ (h r.val)
    (shiftedModuleValueLinearEquiv_source_square M N w v e (r.val • p))
    (unitColumn_total J hα M r.val w) (unitColumn_total T hβ N r.val v)
end Comparison
end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Canonical unshifted coefficient rows of inverse unit matrices

The normalized left cap in DeformedMatrixComparison is a specified inverse
unit-matrix coordinate, followed by its original canonical source unshift.
The common-chart comparison below transports that exact row. The ordinary
right counit is a different field and is not substituted for it.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u
section Rows
variable {k C : Type u} [CommRing k] [Category.{u} C]
  [Preadditive C] [Linear k C] [Supercategory k C]
  (M : Superfunctor k C (SVec k)) (w : C) (p : ZMod 2) (m : ℕ)
local instance unitInverseRowPi : PiSupercategory k (Superfunctor k C (SVec k)) :=
  supermodulePiSupercategory

/-- Project to precisely the r-th shifted value slot and remove its given shift. -/
def unitColumnUnshift (r : Fin m) : unitColumnSourceSpace p M m w ⟶ M.obj w :=
  SVec.ofHom (SVec.toLinearMap
    (((SKM.homParityShiftDatum (k := k) (r.val • p)).iso M).hom.total w) ∘ₗ LinearMap.proj r)

theorem unitColumnUnshift_apply (r : Fin m) (x : unitColumnSourceSpace p M m w) :
    unitColumnUnshift M w p m r x =
      ((SKM.homParityShiftDatum (k := k) (r.val • p)).iso M).hom.total w (x r) := rfl

/-- A specified inverse coefficient row, with exactly its canonical unshift. -/
def unitColumnInverseRow {W : SVec k} (e : unitColumnSourceSpace p M m w ≅ W) (r : Fin m) :
    W ⟶ M.obj w := e.inv ≫ unitColumnUnshift M w p m r

theorem unitColumnInverseRow_apply {W : SVec k} (e : unitColumnSourceSpace p M m w ≅ W)
    (r : Fin m) (x : W) :
    unitColumnInverseRow M w p m e r x =
      ((SKM.homParityShiftDatum (k := k) (r.val • p)).iso M).hom.total w (e.inv x r) := rfl

private theorem unitColumnInverseRow_linear {W : SVec k}
    (e : unitColumnSourceSpace p M m w ≅ W) (r : Fin m) :
    SVec.toLinearMap (unitColumnInverseRow M w p m e r) =
      SVec.toLinearMap (unitColumnUnshift M w p m r) ∘ₗ SVec.toLinearMap e.inv :=
  SVec.toLinearMap_comp e.inv (unitColumnUnshift M w p m r)
end Rows

section Coordinates
variable {k C D : Type u} [CommRing k] [Category.{u} C] [Category.{u} D]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive D] [Linear k D] [Supercategory k D]
  (M : Superfunctor k C (SVec k)) (N : Superfunctor k D (SVec k))
  (w : C) (v : D) (e : M.obj w ≃ₗ[k] N.obj v) (p : ZMod 2) (m : ℕ)

/-- The actual coordinate product intertwines the original unshifts. -/
theorem unitColumnUnshift_coordinate (r : Fin m) :
    SVec.toLinearMap (unitColumnUnshift N v p m r) ∘ₗ
        (unitColumnFamilyEquiv M N w v e p m).toLinearMap =
      e.toLinearMap ∘ₗ SVec.toLinearMap (unitColumnUnshift M w p m r) := by
  apply LinearMap.ext
  intro x
  exact shiftedModuleValueLinearEquiv_hom_coordinate M N w v e (r.val • p) (x r)
end Coordinates

section CommonComparison
variable {k C₀ C₁ C₂ : Type u} [CommRing k]
  [Category.{u} C₀] [Preadditive C₀] [Linear k C₀] [Supercategory k C₀]
  [Category.{u} C₁] [Preadditive C₁] [Linear k C₁] [Supercategory k C₁]
  [Category.{u} C₂] [Preadditive C₂] [Linear k C₂] [Supercategory k C₂]
  (M₀ : Superfunctor k C₀ (SVec k)) (M₁ : Superfunctor k C₁ (SVec k))
  (M₂ : Superfunctor k C₂ (SVec k)) (w₀ : C₀) (w₁ : C₁) (w₂ : C₂)
  (d : M₀.obj w₀ ≃ₗ[k] M₁.obj w₁) (d' : M₀.obj w₀ ≃ₗ[k] M₂.obj w₂)
  (p : ZMod 2) (m : ℕ) {B W W' : SVec k}
  (b : B ≃ₗ[k] W) (t : B ≃ₗ[k] W')
  (e : unitColumnSourceSpace p M₁ m w₁ ≅ W)
  (f : unitColumnSourceSpace p M₂ m w₂ ≅ W')
  (r : unitColumnSourceSpace p M₀ m w₀ →ₗ[k] B)

/-- Two proved forward matrix squares transport the specified inverse row
and its full canonical unshift. These hypotheses are supplied by the chosen
content and scalar matrix comparisons in the concrete left-cap application. -/
theorem unitColumnInverseRow_compare_common
    (hOld : b.toLinearMap ∘ₗ r = SVec.toLinearMap e.hom ∘ₗ
      (unitColumnFamilyEquiv M₀ M₁ w₀ w₁ d p m).toLinearMap)
    (hNew : t.toLinearMap ∘ₗ r = SVec.toLinearMap f.hom ∘ₗ
      (unitColumnFamilyEquiv M₀ M₂ w₀ w₂ d' p m).toLinearMap) (a : Fin m) :
    (d.symm.trans d').toLinearMap ∘ₗ SVec.toLinearMap (unitColumnInverseRow M₁ w₁ p m e a) =
      SVec.toLinearMap (unitColumnInverseRow M₂ w₂ p m f a) ∘ₗ (b.symm.trans t).toLinearMap := by
  have hMatrix := OddMath.FiniteSuperspace.commonChart_square
    (unitColumnFamilyEquiv M₀ M₁ w₀ w₁ d p m) b
    (unitColumnFamilyEquiv M₀ M₂ w₀ w₂ d' p m) t e f r hOld hNew
  have hCoordinate := OddMath.FiniteSuperspace.commonCoordinate_square
    (unitColumnFamilyEquiv M₀ M₁ w₀ w₁ d p m)
    (unitColumnFamilyEquiv M₀ M₂ w₀ w₂ d' p m) d d'
    (SVec.toLinearMap (unitColumnUnshift M₀ w₀ p m a))
    (SVec.toLinearMap (unitColumnUnshift M₁ w₁ p m a))
    (SVec.toLinearMap (unitColumnUnshift M₂ w₂ p m a))
    (unitColumnUnshift_coordinate M₀ M₁ w₀ w₁ d p m a)
    (unitColumnUnshift_coordinate M₀ M₂ w₀ w₂ d' p m a)
  have h := OddMath.FiniteSuperspace.inverse_row_square e f
    (unitColumnFamilyEquiv M₀ M₁ w₀ w₁ d p m |>.symm.trans
      (unitColumnFamilyEquiv M₀ M₂ w₀ w₂ d' p m)).toLinearMap
    (b.symm.trans t).toLinearMap (d.symm.trans d').toLinearMap
    (SVec.toLinearMap (unitColumnUnshift M₁ w₁ p m a))
    (SVec.toLinearMap (unitColumnUnshift M₂ w₂ p m a)) hMatrix hCoordinate
  simpa only [unitColumnInverseRow_linear] using h
end CommonComparison
end OddMath.QuiverHecke.ELV.BalancedInduction
end

end

section

/-! # Dotted-unit fields in native module component coordinates

The normalization window in `SwappedVacuumNonpositiveBubbles.md`, §2,
uses powers of the actual module dot and the given ordinary unit. We keep
the native F/E superspace throughout total evaluation, before specializing
the regular probe. This also transports its probe polynomial to that
same component endomorphism.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELV.BalancedInduction
universe u

private theorem total_add
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    (M : Superfunctor k C (SVec k)) (f g : End M) (w : C) :
    (f + g).total w = f.total w + g.total w := by
  change (f.app 0 w + g.app 0 w) + (f.app 1 w + g.app 1 w) =
    (f.app 0 w + f.app 1 w) + (g.app 0 w + g.app 1 w)
  abel

private theorem homogeneous_total_mem
    {k C : Type u} [CommRing k] [Category.{u} C]
    [Preadditive C] [Linear k C] [Supercategory k C]
    {F G : Superfunctor k C (SVec k)} {f : F ⟶ G} {p : ZMod 2}
    (hf : f ∈ parity (R := k) _ _ p) (w : C) :
    f.total w ∈ parity (R := k) (F.obj w) (G.obj w) p := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (by decide : (1 : ZMod 2) ≠ 0) w,
      add_zero]
    exact f.app_mem 0 w
  · rw [SuperNatTrans.total, Superfunctor.app_eq_zero_of_mem hf (by decide : (0 : ZMod 2) ≠ 1) w,
      zero_add]
    exact f.app_mem 1 w

variable {k C A : Type u} [CommRing k] [Category.{u} C] [Category.{u} A]
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive A] [Linear k A] [Supercategory k A]
  (J : C ⥤ A) [J.Additive] [J.Linear k] [IsSuperfunctor k J]
  {p : ZMod 2} {α : ∀ s, J.obj s ⟶ J.obj s} (hα : IsSupernatural k p α)

/-- The given module dot after the actual restriction functor. -/
def restrictedDotEnd (M : Superfunctor k C (SVec k)) :
    End ((restriction J).obj ((induction J).obj M)) :=
  (restriction J).mapEnd ((induction J).obj M) (dotEnd J hα M)

/-- Its component is an endomorphism of the native F/E superspace. -/
def restrictedDotComponent (M : Superfunctor k C (SVec k)) (w : C) :
    End (((restriction J).obj ((induction J).obj M)).obj w) :=
  (restrictedDotEnd J hα M).total w

/-- The given dotted-unit column is the actual unit followed by powers of
this native module dot, before taking components. -/
theorem unitDotColumn_eq_restrictedDotEnd (M : Superfunctor k C (SVec k)) (n : ℕ) :
    unitDotColumn J hα M n =
      (adjunction J).unit.app M ≫ restrictedDotEnd J hα M ^ n := by
  unfold unitDotColumn restrictedDotEnd
  congr 1
  exact map_pow ((restriction J).mapEnd ((induction J).obj M)) (dotEnd J hα M) n

end OddMath.QuiverHecke.ELV.BalancedInduction
end

end
