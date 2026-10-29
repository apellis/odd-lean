/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVQPContext
/-!
# Signed QP product over the full ELV coefficient algebra

The all-word identity of `DeformedGlobalQP.md` §3 follows by reverse-word induction.
Polynomial factors preserve the defining relation span; right-context descent and
typed empty-context transport connect the three recursions to the induction.
The existing `qpProduct` is unchanged, including each repeated-even factor `−1`.
No restriction on colours, coefficients, or cutoffs is imposed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem affineUnit_id (v : List I) :
    affineUnit D Sc cutoff v v (𝟙 ((pres D Sc).obj (ob D v))) =
      𝟙 (obj D Sc cutoff v) := rfl

def relationPreserving (i : I) (v : List I) :
    Subalgebra k (End ((pres D Sc).obj (ob D (i :: v)))) where
  carrier := {f | ∀ (w : List I) (h : hom D Sc cutoff (i :: v) w),
    h ∈ relations D Sc cutoff i v w →
    affineUnit D Sc cutoff _ _ f ≫ h ∈ relations D Sc cutoff i v w}
  mul_mem' hf hg w h hh := by
    rw [End.mul_def, affineUnit_comp, Category.assoc]
    exact hg w _ (hf w h hh)
  add_mem' hf hg w h hh := by
    rw [map_add, Preadditive.add_comp]
    exact Submodule.add_mem _ (hf w h hh) (hg w h hh)
  algebraMap_mem' c w h hh := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, Linear.smul_comp]
    rw [End.one_def, affineUnit_id, Category.id_comp]
    exact Submodule.smul_mem _ c hh

theorem affineUnit_dot (v : List I) (b : ℕ) :
    affineUnit D Sc cutoff v v (dotE D Sc v b) = sourceDotPower D Sc cutoff v b 1 := by
  change (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] dotE D Sc v b =
    (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] (dotE D Sc v b ^ 1)
  rw [pow_one]

theorem dot_mem_relationPreserving (i : I) (v : List I) (b : ℕ) :
    dotE D Sc (i :: v) b ∈ relationPreserving D Sc cutoff i v := by
  intro w h hh
  rw [affineUnit_dot]
  cases b with
  | zero => exact movingDot_relations D Sc cutoff i hh
  | succ b =>
    have hz : projection D Sc cutoff i v w h = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hh
    have he := congrArg (oldSourceTarget D Sc cutoff i v w (sourceDotPower D Sc cutoff v b 1)) hz
    rw [map_zero] at he
    change projection D Sc cutoff i v w
      (insert D Sc cutoff i v v (sourceDotPower D Sc cutoff v b 1) ≫ h) = 0 at he
    rw [insert_sourceDotPower] at he
    exact (Submodule.Quotient.mk_eq_zero _).mp he

theorem qpFactor_mem_relationPreserving (i : I) (v : List I) (x : I) (b : ℕ) :
    qpFactor D Sc i v x b ∈ relationPreserving D Sc cutoff i v := by
  let A := relationPreserving D Sc cutoff i v
  have h0 := dot_mem_relationPreserving D Sc cutoff i v 0
  have hb := dot_mem_relationPreserving D Sc cutoff i v (b + 1)
  unfold qpFactor
  split_ifs
  · exact A.pow_mem (A.sub_mem hb h0) 2
  · exact A.neg_mem A.one_mem
  · unfold qPoly
    split_ifs
    · exact A.smul_mem A.one_mem _
    · exact A.add_mem (A.sum_mem fun p _ => A.sum_mem fun q _ =>
        A.smul_mem (A.mul_mem (A.pow_mem h0 p) (A.pow_mem hb q)) _)
        (A.add_mem (A.smul_mem (A.pow_mem h0 _) _) (A.smul_mem (A.pow_mem hb _) _))

theorem projection_precomp_eq (i : I) (v w : List I)
    (a : End ((pres D Sc).obj (ob D (i :: v))))
    (ha : a ∈ relationPreserving D Sc cutoff i v)
    (f g : hom D Sc cutoff (i :: v) w)
    (he : projection D Sc cutoff i v w f = projection D Sc cutoff i v w g) :
    projection D Sc cutoff i v w (affineUnit D Sc cutoff _ _ a ≫ f) =
      projection D Sc cutoff i v w (affineUnit D Sc cutoff _ _ a ≫ g) := by
  have he' : f - g ∈ relations D Sc cutoff i v w := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    change projection D Sc cutoff i v w (f - g) = 0
    rw [map_sub, he, sub_self]
  have hz := (Submodule.Quotient.mk_eq_zero _).mpr (ha w (f - g) he')
  change projection D Sc cutoff i v w (affineUnit D Sc cutoff _ _ a ≫ (f - g)) = 0 at hz
  rw [Preadditive.comp_sub, map_sub, sub_eq_zero] at hz
  exact hz

private theorem affineRightContext_nil (v w : List I)
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) :
    affineRightContext D Sc [] v w f =
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) (List.append_nil v)) ≫
        f ≫ eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) (List.append_nil w)).symm := by
  have ht : f ▷ (𝟙_ (pres D Sc).Presented) =
      (ρ_ ((pres D Sc).obj (ob D v))).hom ≫ f ≫
        (ρ_ ((pres D Sc).obj (ob D w))).inv := by
    rw [← Category.assoc, ← MonoidalSupercategory.rightUnitor_naturality (R := k)]
    simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
  exact ht
private theorem qpEval_apply_empty_aux (i : I) (μ σ z : List I)
    (h : hom D Sc cutoff ((i :: μ) ++ σ) z)
    (f : End ((pres D Sc).obj (ob D (i :: μ)))) :
    qpEval D Sc cutoff i μ σ z h f =
    projection D Sc cutoff i (μ ++ σ) z
      (rightContext D Sc cutoff σ (i :: μ) (i :: μ)
        (affineUnit D Sc cutoff _ _ f) ≫ (relation D Sc cutoff i (μ ++ σ) ≫ h)) := rfl

private theorem rightContext_affineUnit_aux (σ v w : List I)
    (f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)) :
    rightContext D Sc cutoff σ v w (affineUnit D Sc cutoff v w f) =
    affineUnit D Sc cutoff (v ++ σ) (w ++ σ) (affineRightContext D Sc σ v w f) := rfl

private theorem projection_transport_aux (i : I) (μ ν : List I) (e : ν = μ)
    (f g : End ((pres D Sc).obj (ob D (i :: μ))))
    (he : projection D Sc cutoff i ν (i :: μ)
      (affineUnit D Sc cutoff (i :: ν) (i :: ν)
        (eqToHom (congrArg (fun t => (pres D Sc).obj (ob D (i :: t))) e) ≫ f ≫
          eqToHom (congrArg (fun t => (pres D Sc).obj (ob D (i :: t))) e).symm) ≫
        (relation D Sc cutoff i ν ≫
          eqToHom (congrArg (fun t => obj D Sc cutoff (i :: t)) e))) =
      projection D Sc cutoff i ν (i :: μ)
      (affineUnit D Sc cutoff (i :: ν) (i :: ν)
        (eqToHom (congrArg (fun t => (pres D Sc).obj (ob D (i :: t))) e) ≫ g ≫
          eqToHom (congrArg (fun t => (pres D Sc).obj (ob D (i :: t))) e).symm) ≫
        (relation D Sc cutoff i ν ≫
          eqToHom (congrArg (fun t => obj D Sc cutoff (i :: t)) e)))) :
    projection D Sc cutoff i μ (i :: μ)
      (affineUnit D Sc cutoff (i :: μ) (i :: μ) f ≫ relation D Sc cutoff i μ) =
    projection D Sc cutoff i μ (i :: μ)
      (affineUnit D Sc cutoff (i :: μ) (i :: μ) g ≫ relation D Sc cutoff i μ) := by
  subst ν
  simpa only [eqToHom_refl, Category.id_comp, Category.comp_id] using he

private theorem projection_eq_of_qpEval_eq (i : I) (μ : List I)
    (f g : End ((pres D Sc).obj (ob D (i :: μ))))
    (he : ∀ σ z (h : hom D Sc cutoff ((i :: μ) ++ σ) z),
      qpEval D Sc cutoff i μ σ z h f = qpEval D Sc cutoff i μ σ z h g) :
    projection D Sc cutoff i μ (i :: μ)
      (affineUnit D Sc cutoff _ _ f ≫ relation D Sc cutoff i μ) =
    projection D Sc cutoff i μ (i :: μ)
      (affineUnit D Sc cutoff _ _ g ≫ relation D Sc cutoff i μ) := by
  have hh := he [] (i :: μ)
    (eqToHom (congrArg (obj D Sc cutoff) (List.append_nil (i :: μ))))
  rw [qpEval_apply_empty_aux, qpEval_apply_empty_aux,
    rightContext_affineUnit_aux, rightContext_affineUnit_aux,
    affineRightContext_nil, affineRightContext_nil] at hh
  exact projection_transport_aux D Sc cutoff i μ (μ ++ []) (List.append_nil μ) f g hh
/-- Extend an equality after the first-position relation by an arbitrary word.
No quotient-target transports and no restrictions on coefficients are necessary. -/
theorem projection_affine_whiskerRight_eq (i : I) (μ τ : List I)
    (f g : End ((pres D Sc).obj (ob D (i :: μ))))
    (hfg : projection D Sc cutoff i μ (i :: μ)
        (affineUnit D Sc cutoff _ _ f ≫ relation D Sc cutoff i μ) =
      projection D Sc cutoff i μ (i :: μ)
        (affineUnit D Sc cutoff _ _ g ≫ relation D Sc cutoff i μ)) :
    projection D Sc cutoff i (μ ++ τ) (i :: (μ ++ τ))
        (affineUnit D Sc cutoff _ _ (f ▷ (pres D Sc).obj (ob D τ)) ≫
          relation D Sc cutoff i (μ ++ τ)) =
      projection D Sc cutoff i (μ ++ τ) (i :: (μ ++ τ))
        (affineUnit D Sc cutoff _ _ (g ▷ (pres D Sc).obj (ob D τ)) ≫
          relation D Sc cutoff i (μ ++ τ)) := by
  have he := congrArg (targetRightContext D Sc cutoff τ i μ (i :: μ)) hfg
  simp only [targetRightContext_projection, rightContext_comp,
    rightContext_relation] at he
  exact he

/-- The no-spectator induction hypothesis implies the required equality in every
larger spectator context, with arbitrary full-coefficient continuation. -/
theorem qpEval_whiskerRight_of_projection_eq (i : I) (μ τ σ z : List I)
    (f g : End ((pres D Sc).obj (ob D (i :: μ))))
    (hfg : projection D Sc cutoff i μ (i :: μ)
        (affineUnit D Sc cutoff _ _ f ≫ relation D Sc cutoff i μ) =
      projection D Sc cutoff i μ (i :: μ)
        (affineUnit D Sc cutoff _ _ g ≫ relation D Sc cutoff i μ))
    (h : hom D Sc cutoff ((i :: (μ ++ τ)) ++ σ) z) :
    qpEval D Sc cutoff i (μ ++ τ) σ z h
        (f ▷ (pres D Sc).obj (ob D τ)) =
      qpEval D Sc cutoff i (μ ++ τ) σ z h
        (g ▷ (pres D Sc).obj (ob D τ)) := by
  exact qpEval_of_projection_eq D Sc cutoff i (μ ++ τ) σ z _ _
    (projection_affine_whiskerRight_eq D Sc cutoff i μ τ f g hfg) h

/-- Raw projected all-word identity, before adjoining spectators. -/
theorem qp_projection_product (i : I) (μ : List I) :
    projection D Sc cutoff i μ (i :: μ)
      (affineUnit D Sc cutoff _ _ (moveHom D Sc i [] μ ≫ lastToFirstHom D Sc i μ) ≫
        relation D Sc cutoff i μ) =
    projection D Sc cutoff i μ (i :: μ)
      (affineUnit D Sc cutoff _ _ (qpProduct D Sc i μ) ≫ relation D Sc cutoff i μ) := by
  induction μ using List.reverseRecOn with
  | nil =>
    apply projection_eq_of_qpEval_eq
    exact fun σ z h => qp_nil D Sc cutoff i σ z h
  | append_singleton μ x ih =>
    have he := projection_affine_whiskerRight_eq D Sc cutoff i μ [x] _ _ ih
    have hf := projection_precomp_eq D Sc cutoff i (μ ++ [x]) (i :: (μ ++ [x]))
      (qpFactor D Sc i (μ ++ [x]) x μ.length)
      (qpFactor_mem_relationPreserving D Sc cutoff i (μ ++ [x]) x μ.length) _ _ he
    rw [← Category.assoc, ← Category.assoc, ← affineUnit_comp, ← affineUnit_comp] at hf
    rw [qpProduct_append, End.mul_def]
    refine Eq.trans ?_ hf
    apply projection_eq_of_qpEval_eq
    intro σ z h
    rw [MonoidalSupercategory.comp_whiskerRight (R := k)]
    by_cases hx : x = i
    · subst x
      rcases parity_eq_zero_or_one (D.parity i) with hi | hi
      · have hr := qp_repeated_even D Sc cutoff i hi μ σ z h
        rw [qpFactor, ite_eq_left rfl, ite_eq_right (by simp [hi]), End.one_def,
          Preadditive.neg_comp, Category.id_comp, map_neg]
        exact hr
      · have hr := qp_repeated_odd D Sc cutoff i hi μ σ z h
        simpa only [qpFactor, ite_eq_left rfl, hi, ite_eq_left,
          MonoidalSupercategory.comp_whiskerRight, moveWhisker, Category.assoc] using hr
    · have hr := qp_distinct D Sc cutoff i x (Ne.symm hx) μ σ z h
      rw [MonoidalSupercategory.comp_whiskerRight (R := k)] at hr
      simpa only [qpFactor, ite_eq_right hx] using hr

/-- The signed QP product identity with arbitrary spectators and full ELV coefficients. -/
theorem qp_product (i : I) (μ σ z : List I)
    (h : hom D Sc cutoff ((i :: μ) ++ σ) z) :
    qpEval D Sc cutoff i μ σ z h
      (moveHom D Sc i [] μ ≫ lastToFirstHom D Sc i μ) =
    qpEval D Sc cutoff i μ σ z h (qpProduct D Sc i μ) :=
  qpEval_of_projection_eq D Sc cutoff i μ σ z _ _ (qp_projection_product D Sc cutoff i μ) h

end OddMath.QuiverHecke.ELVOld
