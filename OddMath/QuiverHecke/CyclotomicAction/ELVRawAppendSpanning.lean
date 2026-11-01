import OddMath.QuiverHecke.CyclotomicAction.ELVAppendSpanning

/-! # Finite append ranges before coefficient truncation

The concrete full-ELV monic recurrence reduces moving powers to finitely many
ranges of smaller full old Hom spaces. No positive-weight coefficient ideal is
used. This is the source spanning statement for later ordinary scalar
specialization; it does not assert finite dimension over the ground ring.
-/
noncomputable section
open CategoryTheory
namespace OddMath.QuiverHecke.ELVOld.RawAppend
universe u
variable {I L k : Type u} [AddCommGroup L] [CommRing k]
  (D : SKM.Datum I L) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Bounded powers followed by an arbitrary smaller old Hom and a fixed tail. -/
def boundedAppendContinuationSpan (i : I) (v t w : List I)
    (h : hom D Sc cutoff (t ++ [i]) w) :
    Submodule k (Old D Sc cutoff (v ++ [i]) w) :=
  Submodule.span k {z | ∃ j < (monicELVEndpointProduct D Sc cutoff i v).natDegree,
    ∃ r : hom D Sc cutoff v t,
      z = (ideal D Sc cutoff (v ++ [i]) w).mkQ
        (appendSourcePower D Sc cutoff i v j ≫
          rightContext D Sc cutoff [i] v t r ≫ h)}

/-- The concrete monic recurrence reduces powers even with an arbitrary old Hom
and continuation attached. This is not a generator-interface hypothesis. -/
theorem appendSourcePower_comp_mem_bounded (i : I)
    (v t w : List I) (n : ℕ) (r : hom D Sc cutoff v t)
    (h : hom D Sc cutoff (t ++ [i]) w) :
    (ideal D Sc cutoff (v ++ [i]) w).mkQ
      (appendSourcePower D Sc cutoff i v n ≫
        rightContext D Sc cutoff [i] v t r ≫ h) ∈
      boundedAppendContinuationSpan D Sc cutoff i v t w h := by
  let F : Old D Sc cutoff (v ++ [i]) (v ++ [i]) →ₗ[k]
      Old D Sc cutoff (v ++ [i]) w :=
    (ideal D Sc cutoff (v ++ [i]) (v ++ [i])).liftQ
      (((ideal D Sc cutoff (v ++ [i]) w).mkQ).comp
        (Linear.rightComp k _ (rightContext D Sc cutoff [i] v t r ≫ h)))
      (by
        intro a ha
        exact (Submodule.Quotient.mk_eq_zero _).mpr
          (ideal_comp D Sc cutoff ha _))
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
    change (ideal D Sc cutoff (v ++ [i]) w).mkQ
      ((rightContextEndHom D Sc cutoff i v a * appendSourcePower D Sc cutoff i v j) ≫
        (rightContext D Sc cutoff [i] v t r ≫ h)) = _
    simp only [End.mul_def, rightContextEndHom_apply, rightContext_comp, Category.assoc]
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add a b _ _ ha hb => simpa only [map_add] using Submodule.add_mem _ ha hb
  | smul c a _ ha => simpa only [map_smul] using Submodule.smul_mem _ c ha

/-- The old Hom in each bounded continuation genuinely factors through its
full cyclotomic quotient. -/
def appendBoundedOldMap (i : I) (v t w : List I) (j : ℕ)
    (h : hom D Sc cutoff (t ++ [i]) w) :
    Old D Sc cutoff v t →ₗ[k]
      Old D Sc cutoff (v ++ [i]) w :=
  (ideal D Sc cutoff v t).liftQ
    (((ideal D Sc cutoff (v ++ [i]) w).mkQ).comp
      ((Linear.leftComp k _ (appendSourcePower D Sc cutoff i v j)).comp
        ((Linear.rightComp k _ h).comp (rightContext D Sc cutoff [i] v t))))
    (by
      intro r hr
      exact (Submodule.Quotient.mk_eq_zero _).mpr
        (comp_ideal D Sc cutoff _
          (ideal_comp D Sc cutoff
            (ideal_rightContext D Sc cutoff [i] hr) h)))

@[simp] theorem appendBoundedOldMap_mk (i : I)
    (v t w : List I) (j : ℕ) (h : hom D Sc cutoff (t ++ [i]) w)
    (r : hom D Sc cutoff v t) :
    appendBoundedOldMap D Sc cutoff i v t w j h
      ((ideal D Sc cutoff v t).mkQ r) =
      (ideal D Sc cutoff (v ++ [i]) w).mkQ
        (appendSourcePower D Sc cutoff i v j ≫
          rightContext D Sc cutoff [i] v t r ≫ h) := rfl


/-- The finite family of bounded powers and crossing-only append tails. -/
def appendFiniteRangeSpan (i : I) (v w : List I) :
    Submodule k (Old D Sc cutoff (v ++ [i]) w) :=
  ⨆ (q : AppendCrossingSkeleton i v w)
    (j : Fin (monicELVEndpointProduct D Sc cutoff i v).natDegree),
    LinearMap.range (appendBoundedOldMap D Sc cutoff i v q.index.oldTarget w j.val
      (affineUnit D Sc cutoff _ _ (appendTail D Sc q.index)))

theorem append_tail_mem_finiteRangeSpan {i : I} {v w : List I}
    (x : AppendIdx i v w) (r : hom D Sc cutoff v x.oldTarget) :
    (ideal D Sc cutoff (v ++ [i]) w).mkQ
      (rightContext D Sc cutoff [i] v x.oldTarget r ≫
        affineUnit D Sc cutoff _ _ (appendTail D Sc x)) ∈
      appendFiniteRangeSpan D Sc cutoff i v w := by
  rw [append_tail_normalize]
  apply (show boundedAppendContinuationSpan D Sc cutoff i v x.oldTarget w
      (affineUnit D Sc cutoff _ _ (appendTail D Sc (appendCrossingSkeleton x).index)) ≤
      appendFiniteRangeSpan D Sc cutoff i v w from ?_)
    (appendSourcePower_comp_mem_bounded D Sc cutoff i v x.oldTarget w x.val.1 _ _)
  apply Submodule.span_le.mpr
  rintro z ⟨j, hj, r, rfl⟩
  apply Submodule.mem_iSup_of_mem (appendCrossingSkeleton x)
  apply Submodule.mem_iSup_of_mem (⟨j, hj⟩ : Fin _)
  exact ⟨(ideal D Sc cutoff v x.oldTarget).mkQ r, rfl⟩

/-- Concrete finite append shuffle spanning, with arbitrary full ELV coefficients. -/
theorem appendFiniteRangeSpan_eq_top (i : I) (v w : List I) :
    appendFiniteRangeSpan D Sc cutoff i v w = ⊤ := by
  apply top_unique
  intro z hz
  clear hz
  obtain ⟨h, rfl⟩ := (ideal D Sc cutoff (v ++ [i]) w).mkQ_surjective z
  obtain ⟨f, rfl⟩ := (appendAffineEquiv D Sc cutoff i v w).symm.surjective h
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add f g hf hg => simp only [map_add]; exact Submodule.add_mem _ hf hg
  | single x a =>
    rw [appendAffineEquiv_symm_single, ← append_insert_twisted_coefficient D Sc cutoff x a]
    exact append_tail_mem_finiteRangeSpan D Sc cutoff x _


end OddMath.QuiverHecke.ELVOld.RawAppend
