/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVProbeContentReindex

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
open ELVOld ELVOld.BalancedInduction
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
open ELVOld ELVOld.BalancedInduction
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
