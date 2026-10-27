/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.ScalarChangePresentation
import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Tensor base change of SKM presented Hom modules

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Definition 1.5, (1.7)–(1.14), and Definition 2.2; the presentation comparison
in `GroundRingDescent.md`, §7, item 2. The inverse evaluates each target raw
diagram as the tensor of its source class. Every target relation, including
signed interchange and arbitrary horizontal and vertical contexts, is killed.
No flatness, injectivity, finite-colour or nondegeneracy hypothesis is used.
The original datum and weight group are unchanged.
-/

noncomputable section

namespace OddMath.SKM.ScalarChange

open CategoryTheory StringDiagrams Presentation
open scoped TensorProduct

universe u v w w'

variable {R : Type w} {S : Type w'} [CommRing R] [CommRing S] (f : R →+* S)
  {I : Type u} {X : Type v} [AddCommGroup X] (D : Datum I X) (Sc : Scalars D R)

/-- Extend the diagramwise tensor evaluation linearly over the target ring. -/
def tensorLin (a b : Obj (sig D)) :
    letI := f.toAlgebra
    LinDiagram S a b →ₗ[S]
    S ⊗[R] ((pres D Sc).obj a ⟶ (pres D Sc).obj b) :=
  letI := f.toAlgebra
  Finsupp.linearCombination S (fun g : a ⟶ b => 1 ⊗ₜ[R] (pres D Sc).diag g)

@[simp] theorem tensorLin_single {a b : Obj (sig D)} (g : a ⟶ b) (s : S) :
    letI := f.toAlgebra
    tensorLin f D Sc a b (Finsupp.single g s) = s ⊗ₜ[R] (pres D Sc).diag g := by
  let := f.toAlgebra
  change Finsupp.linearCombination S _ (Finsupp.single g s) = _
  rw [Finsupp.linearCombination_single, TensorProduct.smul_tmul', smul_eq_mul, mul_one]

@[simp] theorem tensorLin_of {a b : Obj (sig D)} (g : a ⟶ b) :
    letI := f.toAlgebra
    tensorLin f D Sc a b (LinDiagram.of g) = 1 ⊗ₜ[R] (pres D Sc).diag g :=
  letI := f.toAlgebra
  tensorLin_single f D Sc g 1

/-- The balancing relation identifies source coefficients with their images under `f`. -/
theorem tensorLin_coeff {a b : Obj (sig D)} (x : LinDiagram R a b) :
    letI := f.toAlgebra
    tensorLin f D Sc a b (coeff f x) = 1 ⊗ₜ[R] (pres D Sc).lin x := by
  let := f.toAlgebra
  induction x using Finsupp.induction_linear with
  | zero => rw [coeff_zero, map_zero, lin_zero, TensorProduct.tmul_zero]
  | add x y hx hy =>
    rw [coeff_add, map_add, hx, hy, lin_add, TensorProduct.tmul_add]
  | single g r =>
    rw [coeff_single, tensorLin_single, lin_single, ← TensorProduct.smul_tmul]
    change f r ⊗ₜ[R] (pres D Sc).diag g = (f r * 1) ⊗ₜ[R] (pres D Sc).diag g
    rw [mul_one]

/-- The forward comparison is the scalar extension of the proved semilinear Hom map. -/
def fromTensor (a b : Obj (sig D)) :
    letI := f.toAlgebra
    S ⊗[R] ((pres D Sc).obj a ⟶ (pres D Sc).obj b) →ₗ[S]
      ((pres D (scalars D f Sc)).obj a ⟶ (pres D (scalars D f Sc)).obj b) := by
  let := f.toAlgebra
  let H := (pres D (scalars D f Sc)).obj a ⟶ (pres D (scalars D f Sc)).obj b
  letI : Module R H := Module.compHom H f
  letI : IsScalarTower R S H := ⟨fun r s x => mul_smul (f r) s x⟩
  let m : ((pres D Sc).obj a ⟶ (pres D Sc).obj b) →ₗ[R] H :=
    { toFun := homMap f D Sc a b
      map_add' := (homMap f D Sc a b).map_add
      map_smul' := (homMap f D Sc a b).map_smulₛₗ }
  exact m.liftBaseChange S

@[simp] theorem fromTensor_tmul {a b : Obj (sig D)} (s : S)
    (x : (pres D Sc).obj a ⟶ (pres D Sc).obj b) :
    letI := f.toAlgebra
    fromTensor f D Sc a b (s ⊗ₜ[R] x) = s • homMap f D Sc a b x := by
  let := f.toAlgebra
  rfl

private theorem source_whisk_witness (r : (pres D Sc).AllRel)
    (x : LinDiagram S r.dom r.cod) (hx : coeff f r.rel = x)
    (l : Obj (sig D)) (v : List (sig D).Colour) (h : r.dom.WhiskerOK l v) :
    ∃ z : LinDiagram R (r.dom.whisker l v) (r.cod.whisker l v),
      z ∈ (pres D Sc).ideal _ _ ∧ coeff f z = LinDiagram.whisker x l v h := by
  refine ⟨LinDiagram.whisker r.rel l v h, (pres D Sc).whisker_rel_mem_ideal r l v h, ?_⟩
  exact (coeff_whisker f r.rel l v h).trans (congrArg (fun z => LinDiagram.whisker z l v h) hx)

/-- Every whiskered target relation has a source relation witness with identical labels. -/
theorem exists_source_whiskRel (r : (pres D (scalars D f Sc)).AllRel)
    (l : Obj (sig D)) (v : List (sig D).Colour) (h : r.dom.WhiskerOK l v) :
    ∃ z : LinDiagram R (r.dom.whisker l v) (r.cod.whisker l v),
      z ∈ (pres D Sc).ideal _ _ ∧ coeff f z = LinDiagram.whisker r.rel l v h := by
  cases r with
  | user r =>
    exact source_whisk_witness f D Sc (.user r) _ (coeff_relation f D Sc r) l v h
  | interchange x hx =>
    exact source_whisk_witness f D Sc (.interchange x hx) _ (coeff_interchange f x hx) l v h

private theorem tensorLin_context_of_zero {a b s t : Obj (sig D)}
    (x : LinDiagram R s t) (hx : x ∈ (pres D Sc).ideal s t) (pre : a ⟶ s) (post : t ⟶ b) :
    letI := f.toAlgebra
    tensorLin f D Sc a b (LinDiagram.of pre ≫ coeff f x ≫ LinDiagram.of post) = 0 := by
  let := f.toAlgebra
  have hz : (pres D Sc).lin (LinDiagram.of pre ≫ x ≫ LinDiagram.of post) = 0 := by
    rw [← lin_zero (pres D Sc), lin_eq_iff, sub_zero]
    exact (pres D Sc).comp_mem_ideal _ ((pres D Sc).mem_ideal_comp hx _)
  have he : coeff f (LinDiagram.of pre ≫ x ≫ LinDiagram.of post) =
      LinDiagram.of pre ≫ coeff f x ≫ LinDiagram.of post := by
    rw [coeff_comp, coeff_comp, coeff_of, coeff_of]
  rw [← he, tensorLin_coeff, hz, TensorProduct.tmul_zero]

private theorem tensorLin_context_zero {a b s t : Obj (sig D)}
    (x : LinDiagram R s t) (hx : x ∈ (pres D Sc).ideal s t)
    (pre : LinDiagram S a s) (post : LinDiagram S t b) :
    letI := f.toAlgebra
    tensorLin f D Sc a b (pre ≫ coeff f x ≫ post) = 0 := by
  let := f.toAlgebra
  induction pre using Finsupp.induction_linear with
  | zero => rw [Limits.zero_comp, map_zero]
  | add p q hp hq =>
    rw [Preadditive.add_comp, map_add, hp, hq, add_zero]
  | single p r =>
    let d : a ⟶ s := p
    change tensorLin f D Sc a b ((Finsupp.single d r : LinDiagram S a s) ≫ coeff f x ≫ post) = 0
    have hr : (Finsupp.single d r : LinDiagram S a s) = r • LinDiagram.of d :=
      (Finsupp.smul_single_one d r).symm
    rw [hr, Linear.smul_comp, map_smul]
    suffices hz : tensorLin f D Sc a b (LinDiagram.of d ≫ coeff f x ≫ post) = 0 by
      rw [hz, smul_zero]
    induction post using Finsupp.induction_linear with
    | zero => rw [Limits.comp_zero, Limits.comp_zero, map_zero]
    | add p' q' hp hq =>
      rw [Preadditive.comp_add, Preadditive.comp_add, map_add, hp, hq, add_zero]
    | single q c =>
      let e : t ⟶ b := q
      change tensorLin f D Sc a b (LinDiagram.of d ≫ coeff f x ≫
        (Finsupp.single e c : LinDiagram S t b)) = 0
      have hc : (Finsupp.single e c : LinDiagram S t b) = c • LinDiagram.of e :=
        (Finsupp.smul_single_one e c).symm
      rw [hc, Linear.comp_smul, Linear.comp_smul, map_smul,
        tensorLin_context_of_zero f D Sc x hx, smul_zero]

/-- Evaluation kills the entire target ideal, not just the defining relations. -/
theorem tensorLin_mem_ideal {a b : Obj (sig D)} {x : LinDiagram S a b}
    (hx : x ∈ (pres D (scalars D f Sc)).ideal a b) :
    letI := f.toAlgebra
    tensorLin f D Sc a b x = 0 := by
  let := f.toAlgebra
  have h : (pres D (scalars D f Sc)).ideal a b ≤ LinearMap.ker (tensorLin f D Sc a b) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨r, l, v, hw, pre, post⟩
    obtain ⟨z, hz, he⟩ := exists_source_whiskRel f D Sc r l v hw
    change tensorLin f D Sc _ _ (pre ≫ LinDiagram.whisker r.rel l v hw ≫ post) = 0
    rw [← he]
    exact tensorLin_context_zero f D Sc z hz pre post
  exact h hx

/-- Descend the target diagram evaluation to the presented Hom quotient. -/
def toTensor (a b : Obj (sig D)) :
    letI := f.toAlgebra
    ((pres D (scalars D f Sc)).obj a ⟶ (pres D (scalars D f Sc)).obj b) →ₗ[S]
      S ⊗[R] ((pres D Sc).obj a ⟶ (pres D Sc).obj b) :=
  letI := f.toAlgebra
  { toFun x := Quot.lift (tensorLin f D Sc a b) (fun y z h => by
      have h' : (pres D (scalars D f Sc)).homRel y z := by
        rwa [HomRel.compClosure_eq_self] at h
      apply sub_eq_zero.mp
      rw [← map_sub]
      exact tensorLin_mem_ideal f D Sc h') x
    map_add' x y := by
      obtain ⟨x, rfl⟩ := (pres D (scalars D f Sc)).lin_surjective x
      obtain ⟨y, rfl⟩ := (pres D (scalars D f Sc)).lin_surjective y
      rw [← lin_add]
      exact (tensorLin f D Sc a b).map_add x y
    map_smul' r x := by
      obtain ⟨x, rfl⟩ := (pres D (scalars D f Sc)).lin_surjective x
      rw [← lin_smul]
      exact (tensorLin f D Sc a b).map_smul r x }

@[simp] theorem toTensor_lin {a b : Obj (sig D)} (x : LinDiagram S a b) :
    letI := f.toAlgebra
    toTensor f D Sc a b ((pres D (scalars D f Sc)).lin x) = tensorLin f D Sc a b x := by
  let := f.toAlgebra
  rfl

@[simp] theorem toTensor_diag {a b : Obj (sig D)} (g : a ⟶ b) :
    letI := f.toAlgebra
    toTensor f D Sc a b ((pres D (scalars D f Sc)).diag g) =
      1 ⊗ₜ[R] (pres D Sc).diag g :=
  letI := f.toAlgebra
  tensorLin_of f D Sc g

/-- The inverse evaluated on any source Hom class is its canonical tensor. -/
@[simp] theorem toTensor_homMap {a b : Obj (sig D)}
    (x : (pres D Sc).obj a ⟶ (pres D Sc).obj b) :
    letI := f.toAlgebra
    toTensor f D Sc a b (homMap f D Sc a b x) = 1 ⊗ₜ[R] x := by
  let := f.toAlgebra
  obtain ⟨x, rfl⟩ := (pres D Sc).lin_surjective x
  rw [homMap_lin, toTensor_lin, tensorLin_coeff]

theorem toTensor_fromTensor {a b : Obj (sig D)}
    (x : letI := f.toAlgebra; S ⊗[R] ((pres D Sc).obj a ⟶ (pres D Sc).obj b)) :
    letI := f.toAlgebra
    toTensor f D Sc a b (fromTensor f D Sc a b x) = x := by
  let := f.toAlgebra
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul s x =>
    rw [fromTensor_tmul, map_smul, toTensor_homMap,
      TensorProduct.smul_tmul', smul_eq_mul, mul_one]

theorem fromTensor_toTensor {a b : Obj (sig D)}
    (x : (pres D (scalars D f Sc)).obj a ⟶ (pres D (scalars D f Sc)).obj b) :
    letI := f.toAlgebra
    fromTensor f D Sc a b (toTensor f D Sc a b x) = x := by
  let := f.toAlgebra
  induction x using (pres D (scalars D f Sc)).hom_induction with
  | diag g => rw [toTensor_diag, fromTensor_tmul, homMap_diag, one_smul]
  | zero => rw [map_zero, map_zero]
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | smul r x hx => rw [map_smul, map_smul, hx]

/-- Tensor base change for the SKM presented Hom, over arbitrary commutative
rings along the specified ring map. This is independent of nondegeneracy. -/
def homBaseChange (a b : Obj (sig D)) :
    letI := f.toAlgebra
    S ⊗[R] ((pres D Sc).obj a ⟶ (pres D Sc).obj b) ≃ₗ[S]
      ((pres D (scalars D f Sc)).obj a ⟶ (pres D (scalars D f Sc)).obj b) :=
  letI := f.toAlgebra
  { fromTensor f D Sc a b with
    invFun := toTensor f D Sc a b
    left_inv := toTensor_fromTensor f D Sc
    right_inv := fromTensor_toTensor f D Sc }

@[simp] theorem homBaseChange_tmul {a b : Obj (sig D)} (s : S)
    (x : (pres D Sc).obj a ⟶ (pres D Sc).obj b) :
    letI := f.toAlgebra
    homBaseChange f D Sc a b (s ⊗ₜ[R] x) = s • homMap f D Sc a b x :=
  letI := f.toAlgebra
  fromTensor_tmul f D Sc s x

@[simp] theorem homBaseChange_symm_diag {a b : Obj (sig D)} (g : a ⟶ b) :
    letI := f.toAlgebra
    (homBaseChange f D Sc a b).symm ((pres D (scalars D f Sc)).diag g) =
      1 ⊗ₜ[R] (pres D Sc).diag g :=
  letI := f.toAlgebra
  toTensor_diag f D Sc g

/-- This includes every inverse-entry generator and the zero convention for invalid lists. -/
@[simp] theorem toTensor_cl (μ : X) (s t : List (Letter I)) (ls : List (LayerData I)) :
    letI := f.toAlgebra
    toTensor f D Sc _ _ (cl D (scalars D f Sc) μ s t ls) =
      1 ⊗ₜ[R] cl D Sc μ s t ls := by
  let := f.toAlgebra
  rw [← homMap_cl f D Sc, toTensor_homMap]

/-- Normalized left cups use the prescribed transported units, without a new gauge. -/
@[simp] theorem toTensor_etaP (cs : CScalars Sc) (i : I) (μ : X) :
    letI := f.toAlgebra
    toTensor f D Sc _ _ (etaP (cScalars D f cs) i μ) = 1 ⊗ₜ[R] etaP cs i μ := by
  let := f.toAlgebra
  rw [← homMap_etaP f D Sc, toTensor_homMap]

/-- The inverse-unit normalization in left caps is retained as well. -/
@[simp] theorem toTensor_epsP (cs : CScalars Sc) (i : I) (μ : X) :
    letI := f.toAlgebra
    toTensor f D Sc _ _ (epsP (cScalars D f cs) i μ) = 1 ⊗ₜ[R] epsP cs i μ := by
  let := f.toAlgebra
  rw [← homMap_epsP f D Sc, toTensor_homMap]

end OddMath.SKM.ScalarChange
