import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Category.ModuleCat.Basic
import OddMath.Algebra.MatrixInverseTransport
import OddMath.QuiverHecke.CyclotomicAction.InductionMixed.InductionPolynomialSigns
import OddMath.QuiverHecke.CyclotomicAction.ProbeMixed.ProbeAppendTensors
import OddMath.QuiverHecke.SwappedVacuum.InverseCapMoments
import OddMath.SKM.RouquierNormalizedHomAdjunction

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
