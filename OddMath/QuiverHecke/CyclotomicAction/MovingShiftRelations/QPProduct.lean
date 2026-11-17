import OddMath.QuiverHecke.CyclotomicAction.MovingShiftRelations.MovingShift

/-!
# Moving shift relations

Part of the categorical action of the quiver Hecke 2-supercategory on deformed
cyclotomic quotients. Each section below was a separate file; its docstring describes it.
-/

section

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
namespace OddMath.QuiverHecke.ELV
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

end OddMath.QuiverHecke.ELV
end

end

section

/-!
# Signed moving-power coordinates

Every unsigned moving dot power descends through the old cyclotomic relations.
Its coordinate action shifts the moving exponent and applies the total-parity
involution to the old coefficient. The exact coordinate and support bound are
inputs to signed polynomial regularity; no parity-zero restriction is imposed.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem movingPower_succ_comp (i : I) (v : List I) (d : ℕ) :
    movingPower D Sc cutoff i v (d + 1) =
      movingPower D Sc cutoff i v 1 ≫ movingPower D Sc cutoff i v d := by
  change affineUnit D Sc cutoff _ _ (dotE D Sc (i :: v) 0 ^ (d + 1) : End _) =
    affineUnit D Sc cutoff _ _ (dotE D Sc (i :: v) 0 ^ 1 : End _) ≫
      affineUnit D Sc cutoff _ _ (dotE D Sc (i :: v) 0 ^ d : End _)
  rw [pow_succ, End.mul_def, affineUnit_comp, pow_one]

theorem movingPower_insert_twist (i : I) {v t : List I} (d : ℕ)
    (r : hom D Sc cutoff v t) :
    movingPower D Sc cutoff i v d ≫ insert D Sc cutoff i v t r =
      insert D Sc cutoff i v t (twist k (d • D.parity i) r) ≫
        movingPower D Sc cutoff i t d := by
  induction d with
  | zero =>
    change (𝟙 (obj D Sc cutoff (i :: v))) ≫ insert D Sc cutoff i v t r =
      insert D Sc cutoff i v t (twist k (0 • D.parity i) r) ≫ 𝟙 _
    simp
  | succ d ih =>
    rw [movingPower_succ_comp, Category.assoc, ih, ← Category.assoc,
      movingDot_insert, Category.assoc, ← movingPower_succ_comp]
    rw [← twist_add, succ_nsmul, add_comm]

/-- Every moving power preserves the old cyclotomic relations. -/
theorem movingPower_relations_twist (i : I) {v w : List I} (d : ℕ)
    {h : hom D Sc cutoff (i :: v) w} (hh : h ∈ relations D Sc cutoff i v w) :
    movingPower D Sc cutoff i v d ≫ h ∈ relations D Sc cutoff i v w := by
  induction hh using Submodule.span_induction with
  | mem h hh =>
    obtain ⟨t, r, hr, f, rfl⟩ := hh
    rw [← Category.assoc, movingPower_insert_twist, Category.assoc]
    exact Submodule.subset_span ⟨t, _, twist_ideal D Sc cutoff _ hr, _, rfl⟩
  | zero => simp only [Limits.comp_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [Preadditive.comp_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [Linear.comp_smul]; exact Submodule.smul_mem _ c ha

/-- Unsigned moving powers on the quotient, without a parity restriction. -/
def signedMovingPowerTarget (i : I) (v w : List I) (d : ℕ) :
    Target D Sc cutoff i v w →ₗ[k] Target D Sc cutoff i v w :=
  (relations D Sc cutoff i v w).mapQ (relations D Sc cutoff i v w)
    (Linear.leftComp k _ (movingPower D Sc cutoff i v d))
    (fun _ hh => movingPower_relations_twist D Sc cutoff i d hh)

@[simp] theorem signedMovingPowerTarget_projection (i : I) (v w : List I) (d : ℕ)
    (h : hom D Sc cutoff (i :: v) w) :
    signedMovingPowerTarget D Sc cutoff i v w d (projection D Sc cutoff i v w h) =
      projection D Sc cutoff i v w (movingPower D Sc cutoff i v d ≫ h) := rfl

private theorem movingPower_tail_shift {i : I} {v w : List I}
    (x : PrependIdx i v w) (d : ℕ) :
    movingPower D Sc cutoff i x.oldTarget d ≫
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x :
        hom D Sc cutoff (i :: x.oldTarget) w) =
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
        prependTail D Sc (x.shift d) : hom D Sc cutoff (i :: x.oldTarget) w) := by
  change affineUnit D Sc cutoff _ _ _ ≫ affineUnit D Sc cutoff _ _ _ =
    affineUnit D Sc cutoff _ _ _
  rw [← affineUnit_comp, prependTail_shift]

/-- The signed coefficient shift for the unsigned moving operator. -/
theorem signedMovingPower_pair_shift (p : ZMod 2) {i : I} {v w : List I}
    (x : PrependIdx i v w) (d : ℕ) (b : Old D Sc cutoff v x.oldTarget) :
    signedMovingPowerTarget D Sc cutoff i v w d
      (pair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x) b) =
      pair D Sc cutoff p i
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
          prependTail D Sc (x.shift d))
        (oldTwist D Sc cutoff (d • D.parity i) v x.oldTarget b) := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v x.oldTarget).mkQ_surjective b
  let h : hom D Sc cutoff (i :: x.oldTarget) w :=
    (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc x
  let h' : hom D Sc cutoff (i :: x.oldTarget) w :=
    (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] prependTail D Sc (x.shift d)
  change projection D Sc cutoff i v w
    (movingPower D Sc cutoff i v d ≫ (insert D Sc cutoff i v x.oldTarget (twist k p r) ≫ h)) =
    projection D Sc cutoff i v w
      (insert D Sc cutoff i v x.oldTarget (twist k p (twist k (d • D.parity i) r)) ≫ h')
  apply congrArg (projection D Sc cutoff i v w)
  calc
    _ = (movingPower D Sc cutoff i v d ≫
        insert D Sc cutoff i v x.oldTarget (twist k p r)) ≫ h :=
      (Category.assoc _ _ _).symm
    _ = (insert D Sc cutoff i v x.oldTarget (twist k (d • D.parity i) (twist k p r)) ≫
        movingPower D Sc cutoff i x.oldTarget d) ≫ h :=
      congrArg (fun a => a ≫ h) (movingPower_insert_twist D Sc cutoff i d _)
    _ = insert D Sc cutoff i v x.oldTarget (twist k (d • D.parity i) (twist k p r)) ≫
        (movingPower D Sc cutoff i x.oldTarget d ≫ h) := Category.assoc _ _ _
    _ = insert D Sc cutoff i v x.oldTarget (twist k (d • D.parity i) (twist k p r)) ≫ h' :=
      congrArg (fun a => insert D Sc cutoff i v x.oldTarget
        (twist k (d • D.parity i) (twist k p r)) ≫ a) (movingPower_tail_shift D Sc cutoff x d)
    _ = _ := by rw [← twist_add, ← twist_add, add_comm p]

/-- Simultaneous coordinates detect the shifted coefficient for every finite coordinate vector. -/
theorem signedMovingPower_coordinate_shift (p : ZMod 2) {i : I} {v w : List I}
    (q : PrependIdx.Tail i v w) (d : ℕ)
    (f : PrependOldCoordinates D Sc cutoff i v w) :
    prependOldCoordinate D Sc cutoff p (q.representative.shift d)
      (signedMovingPowerTarget D Sc cutoff i v w d
        (prependOldReconstruct D Sc cutoff p i v w f)) = oldTwist D Sc cutoff (d • D.parity i) v q.representative.oldTarget (f q) := by
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero, DFinsupp.zero_apply]
  | add f g hf hg => simp only [map_add, hf, hg, DirectSum.add_apply, map_add]
  | of t b =>
    change prependOldCoordinate D Sc cutoff p (q.representative.shift d)
      (signedMovingPowerTarget D Sc cutoff i v w d
        (prependOldReconstruct D Sc cutoff p i v w (DirectSum.lof k _ _ t b))) = _
    rw [prependOldReconstruct, DirectSum.toModule_lof, signedMovingPower_pair_shift]
    by_cases ht : t = q
    · subst t
      erw [prependOldCoordinate_pair, DirectSum.of_eq_same]
    · erw [prependOldCoordinate_pair_off]
      · rw [DirectSum.of_eq_of_ne _ _ _ (Ne.symm ht), map_zero]
      · intro he
        apply ht
        apply Subtype.ext
        have hk : q.representative.tailKey = t.representative.tailKey := by
          apply Prod.ext
          · have hn := congrArg Prod.fst he
            change d + q.representative.1.1 = d + t.representative.1.1 at hn
            exact Nat.add_left_cancel hn
          · have hs := congrArg Prod.snd he
            exact hs
        exact t.representative_tailKey.symm.trans (hk.symm.trans q.representative_tailKey)

/-- Exact shifted coordinate of an arbitrary quotient element. -/
theorem signedMovingPower_coordinate (p : ZMod 2) {i : I} {v w : List I}
    (q : PrependIdx.Tail i v w) (d : ℕ) (z : Target D Sc cutoff i v w) :
    prependOldCoordinate D Sc cutoff p (q.representative.shift d)
      (signedMovingPowerTarget D Sc cutoff i v w d z) =
      oldTwist D Sc cutoff (d • D.parity i) v q.representative.oldTarget
        (prependOldCoordinateEquiv D Sc cutoff p i v w z q) := by
  simpa only [prependOldReconstruct_coordinateEquiv] using
    signedMovingPower_coordinate_shift D Sc cutoff p q d
      (prependOldCoordinateEquiv D Sc cutoff p i v w z)

end OddMath.QuiverHecke.ELV
end

end

section

/-!
# Regularity of the moving cyclotomic relation

The explicit odd ELV and even monic coefficients express the moving relation
as its top unsigned moving power plus lower powers with old coefficient actions.
At a maximal moving-support coordinate the lower terms vanish. The top term
is the total-parity involution of the original coefficient, hence detects it.
This proves cancellation in the old-only quotient over arbitrary commutative
rings, including zero cutoffs, without flatness or nonvanishing hypotheses.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELV
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem movingPower_oldSource_above (p : ZMod 2) {i : I} {v w : List I}
    (x : PrependIdx i v w) (d : ℕ) (c : hom D Sc cutoff v v)
    (f : PrependOldCoordinates D Sc cutoff i v w)
    (h : ∀ q ∈ f.support, d + q.1.1 < x.1.1) :
    prependOldCoordinate D Sc cutoff p x
      (signedMovingPowerTarget D Sc cutoff i v w d
        (oldSourceTarget D Sc cutoff i v w c
          (prependOldReconstruct D Sc cutoff p i v w f))) = 0 := by
  have hf : f = ∑ q ∈ f.support, DirectSum.lof k _ _ q (f q) :=
    (DFinsupp.sum_single (f := f)).symm
  rw [hf, map_sum, map_sum, map_sum, map_sum]
  apply Finset.sum_eq_zero
  intro q hq
  rw [prependOldReconstruct, DirectSum.toModule_lof, oldSourceTarget_pair,
    signedMovingPower_pair_shift]
  apply prependOldCoordinate_pair_off
  intro he
  have hn := congrArg Prod.fst he
  have hk := congrArg Prod.fst q.representative_tailKey
  have hh := h q hq
  change x.1.1 = d + q.representative.1.1 at hn
  change q.representative.1.1 = q.1.1 at hk
  omega

theorem movingPower_comp_coefficient (i : I) (v : List I) (d : ℕ)
    (a : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) :
    movingPower D Sc cutoff i v d ≫
      insert D Sc cutoff i v v (a ⊗ₜ[k] 𝟙 ((pres D Sc).obj (ob D v))) =
      (a ⊗ₜ[k] (dotE D Sc (i :: v) 0 ^ d : End _)) := by
  rw [insert_tmul]
  have hi : affineInsert D Sc i v v (𝟙 _) = 𝟙 _ :=
    MonoidalSupercategory.whiskerLeft_id (R := k)
      ((pres D Sc).obj (ob D [i])) ((pres D Sc).obj (ob D v))
  rw [hi]
  change BoxProd.tmulHom (X := obj D Sc cutoff (i :: v))
    (Y := obj D Sc cutoff (i :: v)) (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) _ ≫
      BoxProd.tmulHom (X := obj D Sc cutoff (i :: v))
        (Y := obj D Sc cutoff (i :: v)) a (𝟙 _) = _
  rw [BoxProd.tmulHom_comp_tmulHom
    (X := obj D Sc cutoff (i :: v)) (Y := obj D Sc cutoff (i :: v))
    (Z := obj D Sc cutoff (i :: v))
    (show (1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ∈
      SKM.SYM.elvCoefficientParity D cutoff 0 from SetLike.GradedOne.one_mem)
    _ a (id_mem (R := k) _)]
  simp only [koszulSign_zero_left, one_smul, Category.comp_id]
  change (a * 1) ⊗ₜ[k] _ = _
  rw [mul_one]

theorem deformedCyclotomic_expansion (i : I) (v : List I) (N : ℕ)
    (c : Fin (N + 1) → SKM.SYM D k) :
    (elvQuotientFunctor D Sc cutoff).map (deformedCyclotomic D Sc (i :: v) N c) =
      ∑ j : Fin (N + 1), movingPower D Sc cutoff i v j.val ≫
        insert D Sc cutoff i v v
          (SKM.SYM.elvCoefficientQuotient D cutoff (c j) ⊗ₜ[k] 𝟙 ((pres D Sc).obj (ob D v))) := by
  change elvQuotientMap D Sc cutoff _ _ (deformedCyclotomic D Sc (i :: v) N c) = _
  unfold deformedCyclotomic
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [elvQuotientMap_source, movingPower_comp_coefficient]
  congr 1
  simp only [firstDotPower, dotE_pow, List.map_replicate]

theorem oldSourceTarget_projection (i : I) (v w : List I) (c : hom D Sc cutoff v v)
    (h : hom D Sc cutoff (i :: v) w) :
    oldSourceTarget D Sc cutoff i v w c (projection D Sc cutoff i v w h) =
      projection D Sc cutoff i v w (insert D Sc cutoff i v v c ≫ h) := rfl

theorem oldSourceTarget_id (i : I) (v w : List I) (z : Target D Sc cutoff i v w) :
    oldSourceTarget D Sc cutoff i v w (𝟙 _) z = z := by
  obtain ⟨h, rfl⟩ := projection_surjective D Sc cutoff i v w z
  change projection D Sc cutoff i v w (insert D Sc cutoff i v v (𝟙 _) ≫ h) = _
  rw [insert_id, Category.id_comp]

/-- Finite moving support proves cancellation for a polynomial whose top coefficient is one. -/
theorem monic_moving_sum_regular (i : I) (v w : List I) (N : ℕ)
    (c : Fin (N + 1) → hom D Sc cutoff v v) (hc : c (Fin.last N) = 𝟙 _)
    (z : Target D Sc cutoff i v w)
    (hz : (∑ j : Fin (N + 1), signedMovingPowerTarget D Sc cutoff i v w j.val
      (oldSourceTarget D Sc cutoff i v w (c j) z)) = 0) : z = 0 := by
  let f := prependOldCoordinateEquiv D Sc cutoff 0 i v w z
  suffices hf : f = 0 by
    exact (prependOldCoordinateEquiv D Sc cutoff 0 i v w).injective
      (hf.trans (map_zero _).symm)
  by_contra hn
  obtain ⟨q, hq, hmax⟩ := f.support.exists_max_image (fun q => q.1.1)
    (Finset.nonempty_iff_ne_empty.mpr (fun he => hn (DFinsupp.support_eq_empty.mp he)))
  rw [Fin.sum_univ_castSucc, hc, oldSourceTarget_id] at hz
  have he := congrArg (prependOldCoordinate D Sc cutoff 0 (q.representative.shift N)) hz
  rw [map_add, map_sum, map_zero] at he
  have hl : (∑ j : Fin N, prependOldCoordinate D Sc cutoff 0 (q.representative.shift N)
      (signedMovingPowerTarget D Sc cutoff i v w j.val
        (oldSourceTarget D Sc cutoff i v w (c j.castSucc) z))) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hb : ∀ t ∈ f.support, j.val + t.1.1 < (q.representative.shift N).1.1 := by
      intro t ht
      have hm := hmax t ht
      have hk := congrArg Prod.fst q.representative_tailKey
      change q.representative.1.1 = q.1.1 at hk
      change j.val + t.1.1 < N + q.representative.1.1
      have hj := j.isLt
      omega
    simpa only [f, prependOldReconstruct_coordinateEquiv] using
      movingPower_oldSource_above D Sc cutoff 0 (q.representative.shift N)
        j.val (c j.castSucc) f hb
  change (∑ j : Fin N, prependOldCoordinate D Sc cutoff 0 (q.representative.shift N)
      (signedMovingPowerTarget D Sc cutoff i v w j.val
        (oldSourceTarget D Sc cutoff i v w (c j.castSucc) z))) +
      prependOldCoordinate D Sc cutoff 0 (q.representative.shift N)
        (signedMovingPowerTarget D Sc cutoff i v w N z) = 0 at he
  rw [hl, zero_add, signedMovingPower_coordinate] at he
  have hh := congrArg (oldTwist D Sc cutoff (N • D.parity i) v q.representative.oldTarget) he
  rw [oldTwist_twice, map_zero] at hh
  exact (DFinsupp.mem_support_iff.mp hq) hh

/-- Cancellation for the explicit coefficient-valued monic polynomial. -/
theorem projection_deformedCyclotomic_regular (i : I) (v w : List I) (N : ℕ)
    (c : Fin (N + 1) → SKM.SYM D k) (hc : c (Fin.last N) = 1)
    (h : hom D Sc cutoff (i :: v) w)
    (hh : projection D Sc cutoff i v w
      ((elvQuotientFunctor D Sc cutoff).map (deformedCyclotomic D Sc (i :: v) N c) ≫ h) = 0) :
    projection D Sc cutoff i v w h = 0 := by
  apply monic_moving_sum_regular D Sc cutoff i v w N
    (fun j => SKM.SYM.elvCoefficientQuotient D cutoff (c j) ⊗ₜ[k] 𝟙 ((pres D Sc).obj (ob D v)))
  · rw [hc, map_one]
    rfl
  · rw [deformedCyclotomic_expansion, Preadditive.sum_comp, map_sum] at hh
    simpa only [oldSourceTarget_projection, signedMovingPowerTarget_projection, Category.assoc] using hh

/-- The moving cyclotomic relation is regular on the old-only quotient over every commutative ring. -/
theorem projection_relation_regular (i : I) (v w : List I)
    (h : hom D Sc cutoff (i :: v) w)
    (hh : projection D Sc cutoff i v w (relation D Sc cutoff i v ≫ h) = 0) :
    projection D Sc cutoff i v w h = 0 := by
  unfold relation at hh
  split_ifs at hh with hi
  · exact projection_deformedCyclotomic_regular D Sc cutoff i v w (cutoff i)
      (SKM.SYM.elvMonicCoefficient D k ⟨i, hi⟩ (cutoff i))
      (SKM.SYM.elvMonicCoefficient_top D k ⟨i, hi⟩ (cutoff i)) h hh
  · exact projection_deformedCyclotomic_regular D Sc cutoff i v w (cutoff i)
      (SKM.SYM.evenMonicCoefficient D k i (cutoff i))
      (SKM.SYM.evenMonicCoefficient_top D k i (cutoff i)) h hh

end OddMath.QuiverHecke.ELV
end

end
