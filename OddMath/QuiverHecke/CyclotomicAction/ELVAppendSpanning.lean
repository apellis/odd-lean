/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVMovingReduction
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendDescent
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendBalance

/-!
# Append moving-power reduction with an old Hom continuation

A supporting slice for finite append-shuffle spanning in the all-content
reservoir argument. The bounded powers are placed at the source, before the
old Hom. Thus the old endomorphisms supplied by the monic recurrence compose
with that Hom without commuting exterior coefficients.

The finite supremum of ranges below is a finite submodule sum; its indices are
crossing skeletons and powers strictly below the concrete monic degree.
-/

noncomputable section
open CategoryTheory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I L k : Type u} [AddCommGroup L] [CommRing k]
  (D : SKM.Datum I L) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The source-positioned moving power, in the full coefficient category. -/
def appendSourcePower (i : I) (v : List I) (n : ℕ) :
    End (obj D Sc cutoff (v ++ [i])) :=
  (affineUnitEndHom D Sc cutoff (v ++ [i])
    (dotE D Sc (v ++ [i]) v.length)) ^ n

/-- Bounded powers followed by an arbitrary smaller old Hom and a fixed tail. -/
def boundedAppendContinuationSpan (N : ℕ) (i : I) (v t w : List I)
    (h : hom D Sc cutoff (t ++ [i]) w) :
    Submodule k (TruncatedOld D Sc cutoff N (v ++ [i]) w) :=
  Submodule.span k {z | ∃ j < (monicELVEndpointProduct D Sc cutoff i v).natDegree,
    ∃ r : hom D Sc cutoff v t,
      z = (truncatedIdeal D Sc cutoff N (v ++ [i]) w).mkQ
        (appendSourcePower D Sc cutoff i v j ≫
          rightContext D Sc cutoff [i] v t r ≫ h)}

/-- The concrete monic recurrence reduces powers even with an arbitrary old Hom
and continuation attached. This is not a generator-interface hypothesis. -/
theorem appendSourcePower_comp_mem_bounded (N : ℕ) (i : I)
    (v t w : List I) (n : ℕ) (r : hom D Sc cutoff v t)
    (h : hom D Sc cutoff (t ++ [i]) w) :
    (truncatedIdeal D Sc cutoff N (v ++ [i]) w).mkQ
      (appendSourcePower D Sc cutoff i v n ≫
        rightContext D Sc cutoff [i] v t r ≫ h) ∈
      boundedAppendContinuationSpan D Sc cutoff N i v t w h := by
  let F : Old D Sc cutoff (v ++ [i]) (v ++ [i]) →ₗ[k]
      TruncatedOld D Sc cutoff N (v ++ [i]) w :=
    (ideal D Sc cutoff (v ++ [i]) (v ++ [i])).liftQ
      (((truncatedIdeal D Sc cutoff N (v ++ [i]) w).mkQ).comp
        (Linear.rightComp k _ (rightContext D Sc cutoff [i] v t r ≫ h)))
      (by
        intro a ha
        exact (Submodule.Quotient.mk_eq_zero _).mpr
          (Submodule.mem_sup_left (ideal_comp D Sc cutoff ha _)))
  have hpow : (ideal D Sc cutoff (v ++ [i]) (v ++ [i])).mkQ
      (appendSourcePower D Sc cutoff i v n) ∈ _ :=
    movingDot_pow_mem_bounded_old_span D Sc cutoff i v n
  change F ((ideal D Sc cutoff (v ++ [i]) (v ++ [i])).mkQ
    (appendSourcePower D Sc cutoff i v n)) ∈ _
  generalize he : (ideal D Sc cutoff (v ++ [i]) (v ++ [i])).mkQ
    (appendSourcePower D Sc cutoff i v n) = z at *
  clear he
  induction hpow using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨a, j, hj, rfl⟩ := hz
    apply Submodule.subset_span
    refine ⟨j, hj, a ≫ r, ?_⟩
    change (truncatedIdeal D Sc cutoff N (v ++ [i]) w).mkQ
      ((rightContextEndHom D Sc cutoff i v a * appendSourcePower D Sc cutoff i v j) ≫
        (rightContext D Sc cutoff [i] v t r ≫ h)) = _
    simp only [End.mul_def, rightContextEndHom_apply, rightContext_comp, Category.assoc]
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | smul c a _ ha => simpa only [map_smul] using Submodule.smul_mem _ c ha

/-- The old Hom in each bounded continuation genuinely factors through its
coefficient-truncated quotient. -/
def appendBoundedOldMap (N : ℕ) (i : I) (v t w : List I) (j : ℕ)
    (h : hom D Sc cutoff (t ++ [i]) w) :
    TruncatedOld D Sc cutoff N v t →ₗ[k]
      TruncatedOld D Sc cutoff N (v ++ [i]) w :=
  (truncatedIdeal D Sc cutoff N v t).liftQ
    (((truncatedIdeal D Sc cutoff N (v ++ [i]) w).mkQ).comp
      ((Linear.leftComp k _ (appendSourcePower D Sc cutoff i v j)).comp
        ((Linear.rightComp k _ h).comp (rightContext D Sc cutoff [i] v t))))
    (by
      intro r hr
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (comp_truncatedIdeal D Sc cutoff N _
          (truncatedIdeal_comp D Sc cutoff N
            (truncatedIdeal_rightContext D Sc cutoff N [i] hr) h)))

@[simp] theorem appendBoundedOldMap_mk (N : ℕ) (i : I)
    (v t w : List I) (j : ℕ) (h : hom D Sc cutoff (t ++ [i]) w)
    (r : hom D Sc cutoff v t) :
    appendBoundedOldMap D Sc cutoff N i v t w j h
      ((truncatedIdeal D Sc cutoff N v t).mkQ r) =
      (truncatedIdeal D Sc cutoff N (v ++ [i]) w).mkQ
        (appendSourcePower D Sc cutoff i v j ≫
          rightContext D Sc cutoff [i] v t r ≫ h) := rfl

/-- A deliberately redundant finite indexing set for crossing-only append
continuations. Keeping the old permutation avoids any finite-colour assumption
or choice of representatives for possibly empty old Hom spaces. -/
def AppendCrossingSkeleton (i : I) (v w : List I) :=
  {p : Equiv.Perm (Fin v.length) × AppendShuffle (appendLen v i) //
    tgt (v ++ [i]) (cw (appendCrossingWord (appendLen v i) p)) = w}

instance appendCrossingSkeleton_finite (i : I) (v w : List I) :
    Finite (AppendCrossingSkeleton i v w) := by
  unfold AppendCrossingSkeleton
  infer_instance

/-- Realize a skeleton by an existing append index with zero moving and old dots. -/
def AppendCrossingSkeleton.index {i : I} {v w : List I}
    (q : AppendCrossingSkeleton i v w) : AppendIdx i v w :=
  ⟨(0, [], q.val), by simp, by simp, q.property⟩

/-- Every existing append basis term supplies one of the finite crossing skeletons. -/
def appendCrossingSkeleton {i : I} {v w : List I}
    (x : AppendIdx i v w) : AppendCrossingSkeleton i v w :=
  ⟨x.val.2.2, x.property.2.2⟩

@[simp] theorem appendCrossingSkeleton_oldTarget {i : I} {v w : List I}
    (x : AppendIdx i v w) :
    (appendCrossingSkeleton x).index.oldTarget = x.oldTarget := rfl

open StringDiagrams Supercategory MonoidalCategory
open scoped TensorProduct

theorem appendSourcePower_whisker (i : I) (v : List I) (n : ℕ) :
    appendSourcePower D Sc cutoff i v n =
      affineUnit D Sc cutoff (v ++ [i]) (v ++ [i]) ((pres D Sc).obj (ob D v) ◁ (dotE D Sc [i] 0 ^ n)) := by
  have he : (pres D Sc).obj (ob D v) ◁ (dotE D Sc [i] 0 ^ n) =
      dotE D Sc (v ++ [i]) v.length ^ n := by
    induction n with
    | zero => exact MonoidalSupercategory.whiskerLeft_id (R := k) _ _
    | succ n ih =>
      simp only [pow_succ, End.mul_def]
      exact (MonoidalSupercategory.whiskerLeft_comp (R := k)
        ((pres D Sc).obj (ob D v)) (dotE D Sc [i] 0) (dotE D Sc [i] 0 ^ n)).trans
          (congrArg₂ (fun f g => f ≫ g) (whiskerLeft_dotE D Sc v i rfl) ih)
  rw [he]
  exact (map_pow (affineUnitEndHom D Sc cutoff (v ++ [i])) _ n).symm

theorem appendTail_factor {i : I} {v w : List I} (x : AppendIdx i v w) :
    appendTail D Sc x =
      (dotE D Sc (x.oldTarget ++ [i]) x.oldTarget.length ^ x.val.1 : End _) ≫
        appendTail D Sc (appendCrossingSkeleton x).index := by
  have hl : x.oldTarget.length = v.length := by simp [AppendIdx.oldTarget]
  simp only [dotE_pow, appendTail, appendCrossingSkeleton_oldTarget]
  symm
  refine (cl_comp D Sc _ _ _ _).trans ?_
  apply cl_eq_cl
  simp only [appendCrossingSkeleton, AppendCrossingSkeleton.index, List.replicate_zero,
    List.map_nil, List.nil_append, List.map_replicate, hl]

theorem append_tail_normalize {i : I} {v w : List I} (x : AppendIdx i v w)
    (r : hom D Sc cutoff v x.oldTarget) :
    rightContext D Sc cutoff [i] v x.oldTarget r ≫
      affineUnit D Sc cutoff _ _ (appendTail D Sc x) =
    appendSourcePower D Sc cutoff i v x.val.1 ≫
      rightContext D Sc cutoff [i] v x.oldTarget
        (twist k (x.val.1 • D.parity i) r) ≫
      affineUnit D Sc cutoff _ _ (appendTail D Sc (appendCrossingSkeleton x).index) := by
  have hf := congrArg (affineUnit D Sc cutoff (x.oldTarget ++ [i]) w)
    (appendTail_factor D Sc x)
  have hc := affineUnit_comp D Sc cutoff
    (dotE D Sc (x.oldTarget ++ [i]) x.oldTarget.length ^ x.val.1)
    (appendTail D Sc (appendCrossingSkeleton x).index)
  rw [hf, hc]
  have hs := trailing_comp_rightContext D Sc cutoff (v := v) (w := x.oldTarget)
    (firstDot_pow_parity D Sc i [] x.val.1) (twist k (x.val.1 • D.parity i) r)
  rw [twist_twist, ← appendSourcePower_whisker, ← appendSourcePower_whisker] at hs
  have hp : affineUnit D Sc cutoff (x.oldTarget ++ [i]) (x.oldTarget ++ [i])
      (dotE D Sc (x.oldTarget ++ [i]) x.oldTarget.length ^ x.val.1) =
      appendSourcePower D Sc cutoff i x.oldTarget x.val.1 :=
    map_pow (affineUnitEndHom D Sc cutoff (x.oldTarget ++ [i])) _ x.val.1
  rw [hp, ← Category.assoc, ← hs, Category.assoc]

/-- The finite family of bounded powers and crossing-only append tails. -/
def appendFiniteRangeSpan (N : ℕ) (i : I) (v w : List I) :
    Submodule k (TruncatedOld D Sc cutoff N (v ++ [i]) w) :=
  ⨆ (q : AppendCrossingSkeleton i v w)
    (j : Fin (monicELVEndpointProduct D Sc cutoff i v).natDegree),
    LinearMap.range (appendBoundedOldMap D Sc cutoff N i v q.index.oldTarget w j.val
      (affineUnit D Sc cutoff _ _ (appendTail D Sc q.index)))

theorem append_tail_mem_finiteRangeSpan (N : ℕ) {i : I} {v w : List I}
    (x : AppendIdx i v w) (r : hom D Sc cutoff v x.oldTarget) :
    (truncatedIdeal D Sc cutoff N (v ++ [i]) w).mkQ
      (rightContext D Sc cutoff [i] v x.oldTarget r ≫
        affineUnit D Sc cutoff _ _ (appendTail D Sc x)) ∈
      appendFiniteRangeSpan D Sc cutoff N i v w := by
  rw [append_tail_normalize]
  apply (show boundedAppendContinuationSpan D Sc cutoff N i v x.oldTarget w
      (affineUnit D Sc cutoff _ _ (appendTail D Sc (appendCrossingSkeleton x).index)) ≤
      appendFiniteRangeSpan D Sc cutoff N i v w from ?_)
    (appendSourcePower_comp_mem_bounded D Sc cutoff N i v x.oldTarget w x.val.1 _ _)
  apply Submodule.span_le.mpr
  rintro z ⟨j, hj, r, rfl⟩
  apply Submodule.mem_iSup_of_mem (appendCrossingSkeleton x)
  apply Submodule.mem_iSup_of_mem (⟨j, hj⟩ : Fin _)
  exact ⟨(truncatedIdeal D Sc cutoff N v x.oldTarget).mkQ r, rfl⟩

/-- Concrete finite append shuffle spanning, with arbitrary full ELV coefficients. -/
theorem appendFiniteRangeSpan_eq_top (N : ℕ) (i : I) (v w : List I) :
    appendFiniteRangeSpan D Sc cutoff N i v w = ⊤ := by
  apply top_unique
  intro z hz
  clear hz
  obtain ⟨h, rfl⟩ := (truncatedIdeal D Sc cutoff N (v ++ [i]) w).mkQ_surjective z
  obtain ⟨f, rfl⟩ := (appendAffineEquiv D Sc cutoff i v w).symm.surjective h
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add f g hf hg => simp only [map_add]; exact Submodule.add_mem _ hf hg
  | single x a =>
    rw [appendAffineEquiv_symm_single, ← append_insert_twisted_coefficient D Sc cutoff x a]
    exact append_tail_mem_finiteRangeSpan D Sc cutoff N x _

end OddMath.QuiverHecke.ELVOld
