/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVVacuumSupportOver
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendDegree

/-!
# Bounded degree support of the truncated quotient over a graded base ring

Over a commutative `K`-algebra `R` graded by `𝒜` in degrees `0, …, b`, every Hom module of the
coefficient-truncated quotient has bounded degree support
(`ELVOld.truncatedContent_boundedOver`). As over a ring, the proof is an induction on the source
word: the vacuum support (`ELVOld.truncatedVacuum_support_of_boundOver`) starts it, and the
finite append spanning family, whose maps shift degrees by explicit amounts
(`ELVOld.appendBoundedOldMap_mem_degreeOver`), propagates finite support from a word to the
word with one more strand.

For `K = R` with the trivial grading (`b = 0`) this is `ELVOld.truncatedContent_bounded`.
-/

-- `letI` keeps the restricted-scalar instances available to instance search in these proofs.
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory StringDiagrams OddMath.Diagrams GradedSupercategory MonoidalCategory

namespace OddMath.QuiverHecke.ELVOld

universe u

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  {K : Type u} [CommRing K] {R : Type u} [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R) [GradedAlgebra 𝒜]
  (Sc : SKM.Scalars D R)
  (hP : CoefficientGrading.IsHomogeneous 𝒜 (gdeg D sy) (pres D Sc)) (cutoff : I → ℕ) (N : ℕ)

/-- An affine diagram with a unit coefficient keeps its degree, over a graded base. -/
theorem affineUnit_mem_degreeOver {v w : List I} {d : ℤ}
    {f : (pres D Sc).obj (ob D v) ⟶ (pres D Sc).obj (ob D w)}
    (hf : f ∈ CoefficientGrading.presentedPart 𝒜 (gdeg D sy) (pres D Sc) (ob D v) (ob D w) d) :
    affineUnit D Sc cutoff v w f ∈ elvHomDegreeOver D sy 𝒜 Sc hP cutoff v w d := by
  let _ := Linear.restrictScalars K R
    (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff))
  let _ := Supercategory.restrictScalars K R
    (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff))
  let _ := elvCoefficientCategoryGradingOver D sy 𝒜 cutoff
  let _ := Linear.restrictScalars K R (H D Sc)
  let _ := Supercategory.restrictScalars K R (H D Sc)
  let _ := quiverHeckeGradingOver D sy 𝒜 Sc hP
  have h := BoxProdCoefficient.tmulHom_mem_homDegree (X := obj D Sc cutoff v)
    (Y := obj D Sc cutoff w) (id_mem_degree (R := K) (obj D Sc cutoff v).fst) hf
  rw [zero_add] at h
  exact h

/-- Right whiskering keeps degrees, over a graded base. -/
theorem rightContext_mem_degreeOver (σ : List I) {v w : List I} {n : ℤ}
    {f : hom D Sc cutoff v w} (hf : f ∈ elvHomDegreeOver D sy 𝒜 Sc hP cutoff v w n) :
    rightContext D Sc cutoff σ v w f ∈ elvHomDegreeOver D sy 𝒜 Sc hP cutoff (v ++ σ) (w ++ σ) n := by
  let _ := Linear.restrictScalars K R
    (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff))
  let _ := Supercategory.restrictScalars K R
    (SuperalgebraCat (SKM.SYM.elvCoefficientParity (k := R) D cutoff))
  let _ := elvCoefficientCategoryGradingOver D sy 𝒜 cutoff
  let _ := Linear.restrictScalars K R (H D Sc)
  let _ := Supercategory.restrictScalars K R (H D Sc)
  let _ := quiverHeckeGradingOver D sy 𝒜 Sc hP
  refine BoxProdCoefficient.homDegree_induction (X := obj D Sc cutoff v)
    (Y := obj D Sc cutoff w) (motive := fun y => rightContext D Sc cutoff σ v w y ∈
      elvHomDegreeOver D sy 𝒜 Sc hP cutoff (v ++ σ) (w ++ σ) n) ?_ ?_ ?_ ?_ hf
  · rw [map_zero]
    exact zero_mem _
  · intro y y' hy hy'
    rw [map_add]
    exact add_mem hy hy'
  · intro c y hy
    rw [map_smul]
    exact BoxProdCoefficient.algebraMap_smul_mem_homDegree (X := obj D Sc cutoff (v ++ σ))
      (Y := obj D Sc cutoff (w ++ σ)) c hy
  · rintro p q rfl a ha g hg
    exact BoxProdCoefficient.tmulHom_mem_homDegree (X := obj D Sc cutoff (v ++ σ))
      (Y := obj D Sc cutoff (w ++ σ)) ha
      (CoefficientGrading.wR_mem_presentedPart hg (ob D σ))

/-- The powers of the dot on the new strand, over a graded base. -/
theorem appendSourcePower_mem_degreeOver (i : I) (v : List I) (n : ℕ) :
    appendSourcePower D Sc cutoff i v n ∈
      elvHomDegreeOver D sy 𝒜 Sc hP cutoff (v ++ [i]) (v ++ [i]) (2 * sy.d i * n) := by
  rw [appendSourcePower_whisker]
  apply affineUnit_mem_degreeOver D sy 𝒜 Sc hP cutoff
  have h : (dotE D Sc [i] 0 ^ n : End _) ∈ CoefficientGrading.presentedPart 𝒜 (gdeg D sy)
      (pres D Sc) (ob D [i]) (ob D [i]) (2 * sy.d i * n) := by
    simpa only [firstDotPower, dotE_pow, List.map_replicate] using
      firstDotPower_mem_presentedPart D sy 𝒜 Sc i [] n
  exact CoefficientGrading.wL_mem_presentedPart (ob D v) h

/-- The tail diagram has the sum of its generator degrees, over a graded base. -/
theorem appendTail_mem_presentedPart {i : I} {v w : List I} (x : AppendIdx i v w) :
    appendTail D Sc x ∈ CoefficientGrading.presentedPart 𝒜 (gdeg D sy) (pres D Sc)
      (ob D (x.oldTarget ++ [i])) (ob D w) (appendTailDegree D sy x) :=
  CoefficientGrading.lin_mem_presentedPart
    (CoefficientGrading.of_mem_part' _ (degree_gdeg_mkD D sy _ _))

/-- The source dots, the smaller old Hom and the tail contribute additively, over a graded
base. -/
theorem appendBoundedOldMap_mem_degreeOver (i : I) (v t w : List I)
    (j : ℕ) {h : hom D Sc cutoff (t ++ [i]) w} {a b : ℤ}
    (hh : h ∈ elvHomDegreeOver D sy 𝒜 Sc hP cutoff (t ++ [i]) w b)
    {r : (⟨v⟩ : TruncatedCategory D Sc cutoff N) ⟶ ⟨t⟩}
    (hr : r ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨v⟩ ⟨t⟩ a) :
    (appendBoundedOldMap D Sc cutoff N i v t w j h r :
        (⟨v ++ [i]⟩ : TruncatedCategory D Sc cutoff N) ⟶ ⟨w⟩) ∈
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨v ++ [i]⟩ ⟨w⟩ (2 * sy.d i * j + (a + b)) := by
  obtain ⟨r, hr, rfl⟩ := hr
  rw [appendBoundedOldMap_mk]
  refine mkQ_mem_truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ?_
  let _ := Linear.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  let _ := Supercategory.restrictScalars K R (ELVCoefficientCategory D Sc cutoff)
  let _ := elvHomGradingOver D sy 𝒜 Sc hP cutoff
  exact comp_mem_degree (appendSourcePower_mem_degreeOver D sy 𝒜 Sc hP cutoff i v j)
    (comp_mem_degree (rightContext_mem_degreeOver D sy 𝒜 Sc hP cutoff [i] hr) hh)

/-- Finite smaller supports propagate through the finite append spanning family, over a
graded base. -/
theorem truncatedAppend_finite_supportOver (i : I) (v w : List I)
    (ih : ∀ t : List I, ∃ S : Set ℤ, S.Finite ∧
      ∀ z : (⟨v⟩ : TruncatedCategory D Sc cutoff N) ⟶ ⟨t⟩,
        letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
        z ∈ ⨆ n ∈ S, truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨v⟩ ⟨t⟩ n) :
    ∃ S : Set ℤ, S.Finite ∧
      ∀ z : (⟨v ++ [i]⟩ : TruncatedCategory D Sc cutoff N) ⟶ ⟨w⟩,
        letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
        z ∈ ⨆ n ∈ S, truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨v ++ [i]⟩ ⟨w⟩ n := by
  classical
  letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
  choose S hfin hs using ih
  let T : Set ℤ := ⋃ (q : AppendCrossingSkeleton i v w),
    ⋃ (j : Fin (monicELVEndpointProduct D Sc cutoff i v).natDegree),
      (fun a => 2 * sy.d i * j.val + (a + appendTailDegree D sy q.index)) '' S q.index.oldTarget
  refine ⟨T, Set.finite_iUnion fun q => Set.finite_iUnion fun j =>
    (hfin q.index.oldTarget).image _, fun z => ?_⟩
  have hz : z ∈ appendFiniteRangeSpan D Sc cutoff N i v w := by
    rw [appendFiniteRangeSpan_eq_top]
    trivial
  unfold appendFiniteRangeSpan at hz
  induction hz using Submodule.iSup_induction' with
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | mem q x hx =>
    induction hx using Submodule.iSup_induction' with
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | mem j x hx =>
      obtain ⟨r, rfl⟩ := hx
      have hr := hs q.index.oldTarget r
      induction hr using Submodule.iSup_induction' with
      | zero => rw [map_zero]; exact zero_mem _
      | add r r' _ _ hr hr' => rw [map_add]; exact add_mem hr hr'
      | mem a r hr =>
        induction hr using Submodule.iSup_induction' with
        | zero => rw [map_zero]; exact zero_mem _
        | add r r' _ _ hr hr' => rw [map_add]; exact add_mem hr hr'
        | mem ha r hr =>
          exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem
            (Set.mem_iUnion.mpr ⟨q, Set.mem_iUnion.mpr ⟨j, ⟨a, ha, rfl⟩⟩⟩ :
              2 * sy.d i * j.val + (a + appendTailDegree D sy q.index) ∈ T)
            (appendBoundedOldMap_mem_degreeOver D sy 𝒜 Sc hP cutoff N i v
              q.index.oldTarget w j.val
              (affineUnit_mem_degreeOver D sy 𝒜 Sc hP cutoff
                (appendTail_mem_presentedPart D sy 𝒜 Sc q.index)) hr))

/-- Finite support at arbitrary strand content, over a base ring graded in degrees
`0, …, b`. -/
theorem truncatedContent_finite_support_of_boundOver (b : ℤ)
    (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥) (M : ℤ) (hM : 0 ≤ M)
    (hbound : ∀ a, SKM.SYM.coefficientDegree D sy a ≤ M * SKM.SYM.coefficientWeight D a)
    (v w : List I) :
    ∃ S : Set ℤ, S.Finite ∧
      ∀ z : (⟨v⟩ : TruncatedCategory D Sc cutoff N) ⟶ ⟨w⟩,
        letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
        z ∈ ⨆ n ∈ S, truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨v⟩ ⟨w⟩ n := by
  induction v using List.reverseRecOn generalizing w with
  | nil => exact ⟨Set.Icc 0 (b + M * N), Set.finite_Icc _ _,
      truncatedVacuum_support_of_boundOver D sy 𝒜 Sc hP cutoff N b h𝒜 M hM hbound w⟩
  | append_singleton v i ih =>
      exact truncatedAppend_finite_supportOver D sy 𝒜 Sc hP cutoff N i v w ih

/-- A homogeneous part outside a spanning support vanishes, over a graded base. -/
theorem truncatedDegreeOver_eq_bot_of_support (v w : List I) (S : Set ℤ)
    (hS : ∀ z : (⟨v⟩ : TruncatedCategory D Sc cutoff N) ⟶ ⟨w⟩,
      letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
      z ∈ ⨆ n ∈ S, truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨v⟩ ⟨w⟩ n)
    (n : ℤ) (hn : n ∉ S) :
    truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨v⟩ ⟨w⟩ n = ⊥ := by
  letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
  apply bot_unique
  intro z hz
  have hzero : ∀ y : (⟨v⟩ : TruncatedCategory D Sc cutoff N) ⟶ ⟨w⟩,
      y ∈ ⨆ m ∈ S, truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨v⟩ ⟨w⟩ m →
        truncatedDprojOver D sy 𝒜 Sc hP cutoff N v w n y = 0 := by
    intro y hy
    induction hy using Submodule.iSup_induction' with
    | zero => exact map_zero _
    | add y y' _ _ hy hy' => rw [map_add, hy, hy', add_zero]
    | mem m y hy =>
      induction hy using Submodule.iSup_induction' with
      | zero => exact map_zero _
      | add y y' _ _ hy hy' => rw [map_add, hy, hy', add_zero]
      | mem hm y hy =>
        rw [truncatedDprojOver_of_mem D sy 𝒜 Sc hP cutoff N hy n]
        exact if_neg (fun h => hn (h ▸ hm))
  have he := truncatedDprojOver_of_mem D sy 𝒜 Sc hP cutoff N hz n
  rw [if_pos rfl, hzero z (hS z)] at he
  exact he.symm

/-- **Bounded degree support over a graded base.** If `𝒜` lives in degrees `0, …, b` and the
coefficient degrees are bounded by a multiple of the coefficient weights, every Hom module of
the coefficient-truncated quotient has bounded degree support. -/
theorem truncatedContent_bounded_of_boundOver (b : ℤ)
    (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥) (M : ℤ) (hM : 0 ≤ M)
    (hbound : ∀ a, SKM.SYM.coefficientDegree D sy a ≤ M * SKM.SYM.coefficientWeight D a)
    (v w : List I) :
    ∃ B : ℕ, ∀ n : ℤ, (n < -(B : ℤ) ∨ (B : ℤ) < n) →
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨v⟩ ⟨w⟩ n = ⊥ := by
  classical
  obtain ⟨S, hf, hs⟩ :=
    truncatedContent_finite_support_of_boundOver D sy 𝒜 Sc hP cutoff N b h𝒜 M hM hbound v w
  refine ⟨hf.toFinset.sup Int.natAbs, fun n hn =>
    truncatedDegreeOver_eq_bot_of_support D sy 𝒜 Sc hP cutoff N v w S hs n ?_⟩
  intro hmem
  have hnat : n.natAbs ≤ hf.toFinset.sup Int.natAbs :=
    Finset.le_sup (f := Int.natAbs) (hf.mem_toFinset.mpr hmem)
  have habs : |n| ≤ ((hf.toFinset.sup Int.natAbs : ℕ) : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast hnat
  have := abs_le.mp habs
  omega

/-- Bounded degree support over a base ring graded in degrees `0, …, b`, for finitely many
colours. -/
theorem truncatedContent_boundedOver [Finite I] (b : ℤ)
    (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥) (v w : List I) :
    ∃ B : ℕ, ∀ n : ℤ, (n < -(B : ℤ) ∨ (B : ℤ) < n) →
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨v⟩ ⟨w⟩ n = ⊥ := by
  obtain ⟨M, hM, hb⟩ := SKM.SYM.exists_coefficientDegree_bound D sy
  exact truncatedContent_bounded_of_boundOver D sy 𝒜 Sc hP cutoff N b h𝒜 M hM hb v w

end OddMath.QuiverHecke.ELVOld
