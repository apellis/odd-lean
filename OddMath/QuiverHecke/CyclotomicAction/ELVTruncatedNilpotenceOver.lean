/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVContentSupportOver
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedNilpotence

/-!
# Positive-degree nilpotence in the truncated quotient over a graded base ring

Over a commutative `K`-algebra `R` graded by `𝒜` in degrees `0, …, b`, every endomorphism of
positive degree of a word in the coefficient-truncated quotient is nilpotent, with an exponent
depending only on the content of the word
(`ELVOld.truncatedContent_positive_pow_zero_of_boundOver`). The exponent comes from the bounded
degree support of the endomorphism module (`ELVOld.truncatedContent_bounded_of_boundOver`):
the `e`-th power of an endomorphism of degree `d > 0` has degree `e d`, which lies outside the
support once `e` is large. Positioned dots and the appended last-strand dot are endomorphisms
of positive degree, so they are nilpotent too.

For `K = R` with the trivial grading (`b = 0`) these are the statements of
`OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedNilpotence`.
-/

-- `letI` keeps the restricted-scalar instances available to instance search in these proofs.
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory StringDiagrams OddMath.Diagrams GradedSupercategory MonoidalCategory

namespace OddMath.QuiverHecke.ELVOld

universe u

/-- Powers of a homogeneous endomorphism in a graded supercategory are homogeneous, of the
multiplied degree. -/
theorem endPow_mem_degree {K : Type*} [CommRing K] {C : Type*} [Category C] [Preadditive C]
    [Linear K C] [Supercategory K C] [GradedSupercategory K C] {Y : C} {d : ℤ} {f : End Y}
    (hf : f ∈ degree (R := K) Y Y d) (n : ℕ) : f ^ n ∈ degree (R := K) Y Y (n • d) := by
  induction n with
  | zero => simpa using id_mem_degree (R := K) Y
  | succ n ih =>
    rw [pow_succ, End.mul_def, succ_nsmul']
    exact comp_mem_degree hf ih

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  {K : Type u} [CommRing K] {R : Type u} [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R) [GradedAlgebra 𝒜]
  (Sc : SKM.Scalars D R)
  (hP : CoefficientGrading.IsHomogeneous 𝒜 (gdeg D sy) (pres D Sc)) (cutoff : I → ℕ) (N : ℕ)

/-- Powers of a homogeneous endomorphism of the truncated quotient over a graded base. -/
theorem truncatedEnd_pow_mem_degreeOver {v : List I} {d : ℤ} {f : TruncatedEnd D Sc cutoff N v}
    (hf : f ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨v⟩ ⟨v⟩ d) (n : ℕ) :
    f ^ n ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨v⟩ ⟨v⟩ (n • d) := by
  letI := Linear.restrictScalars K R (TruncatedCategory D Sc cutoff N)
  letI := Supercategory.restrictScalars K R (TruncatedCategory D Sc cutoff N)
  letI := truncatedGradedSupercategoryOver D sy 𝒜 Sc hP cutoff N
  exact endPow_mem_degree (K := K) hf n

/-- **Positive-degree nilpotence over a graded base.** If `𝒜` lives in degrees `0, …, b` and
coefficient degrees are bounded linearly by coefficient weights, all endomorphisms of positive
degree of the words of a fixed content have a common nilpotence exponent. -/
theorem truncatedContent_positive_pow_zero_of_boundOver (b : ℤ)
    (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥) (M : ℤ) (hM : 0 ≤ M)
    (hbound : ∀ a, SKM.SYM.coefficientDegree D sy a ≤ M * SKM.SYM.coefficientWeight D a)
    (ν : List I) :
    ∃ e : ℕ, 0 < e ∧ ∀ (v : List I), v.Perm ν → ∀ (d : ℤ), 0 < d →
      ∀ f : TruncatedEnd D Sc cutoff N v,
        f ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨v⟩ ⟨v⟩ d → f ^ e = 0 := by
  classical
  choose B hB using fun v : List I =>
    truncatedContent_bounded_of_boundOver D sy 𝒜 Sc hP cutoff N b h𝒜 M hM hbound v v
  let L := ν.permutations.toFinset.sup B
  refine ⟨L + 1, by omega, ?_⟩
  intro v hv d hd f hf
  have hv' : v ∈ ν.permutations.toFinset := by simpa using hv
  have hb : B v ≤ L := Finset.le_sup hv'
  have hp := truncatedEnd_pow_mem_degreeOver D sy 𝒜 Sc hP cutoff N hf (L + 1)
  have hdeg : (B v : ℤ) < (L + 1) • d := by
    rw [nsmul_eq_mul]
    have hcast : (B v : ℤ) ≤ L := by exact_mod_cast hb
    have hk : (0 : ℤ) ≤ L := Nat.cast_nonneg L
    push_cast
    nlinarith
  rw [hB v _ (Or.inr hdeg)] at hp
  exact (Submodule.mem_bot _).mp hp

/-- Positive-degree nilpotence over a base ring graded in degrees `0, …, b`, for finitely many
colours. -/
theorem truncatedContent_positive_pow_zeroOver [Finite I] (b : ℤ)
    (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥) (ν : List I) :
    ∃ e : ℕ, 0 < e ∧ ∀ (v : List I), v.Perm ν → ∀ (d : ℤ), 0 < d →
      ∀ f : TruncatedEnd D Sc cutoff N v,
        f ∈ truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨v⟩ ⟨v⟩ d → f ^ e = 0 := by
  obtain ⟨M, hM, hb⟩ := SKM.SYM.exists_coefficientDegree_bound D sy
  exact truncatedContent_positive_pow_zero_of_boundOver D sy 𝒜 Sc hP cutoff N b h𝒜 M hM hb ν

/-- A dot on an active position has its symmetrizer degree, over a graded base. -/
theorem dotE_mem_presentedPart {v : List I} {r : ℕ} {i : I} (hi : v[r]? = some i) :
    dotE D Sc v r ∈ CoefficientGrading.presentedPart 𝒜 (gdeg D sy) (pres D Sc) (ob D v) (ob D v)
      (2 * sy.d i) := by
  unfold dotE genE
  split_ifs with h
  · have hm := cl_mem_presentedPart D sy 𝒜 Sc [PG.dot r] h
    convert hm using 1
    obtain ⟨hr, rfl⟩ := List.getElem?_eq_some_iff.mp hi
    have hdrop : v.drop r = v[r] :: v.drop (r + 1) := List.drop_eq_getElem_cons hr
    simp only [pl_cons, pl_nil, List.append_nil, PG.ld, hdrop,
      List.map_singleton, List.sum_singleton, gdeg]
  · exact Submodule.zero_mem _

/-- A positioned dot of the truncated quotient has its symmetrizer degree, over a graded
base. -/
theorem truncatedDot_degreeOver {v : List I} {r : ℕ} {i : I} (hi : v[r]? = some i) :
    truncatedDot D Sc cutoff N v r ∈
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨v⟩ ⟨v⟩ (2 * sy.d i) :=
  mkQ_mem_truncatedDegreeOver D sy 𝒜 Sc hP cutoff N
    (affineUnit_mem_degreeOver D sy 𝒜 Sc hP cutoff (dotE_mem_presentedPart D sy 𝒜 Sc hi))

/-- The appended last-strand dot has its symmetrizer degree, over a graded base. -/
theorem truncatedAppendDot_degreeOver (i : I) (v : TruncatedCategory D Sc cutoff N) :
    (truncatedAppendDot D Sc cutoff N i).app (D.parity i) v ∈
      truncatedDegreeOver D sy 𝒜 Sc hP cutoff N ⟨v.word ++ [i]⟩ ⟨v.word ++ [i]⟩
        (2 * sy.d i) := by
  rw [truncatedAppendDot_app]
  exact mkQ_mem_truncatedDegreeOver D sy 𝒜 Sc hP cutoff N
    (affineUnit_mem_degreeOver D sy 𝒜 Sc hP cutoff
      (CoefficientGrading.wL_mem_presentedPart (ob D v.word)
        (dotE_mem_presentedPart D sy 𝒜 Sc (v := [i]) (r := 0) rfl)))

include sy 𝒜 hP in
/-- All active positioned dots of the words of a fixed content have one nilpotence exponent,
over a base ring graded in degrees `0, …, b`. -/
theorem truncatedContent_dot_pow_zeroOver [Finite I] (b : ℤ)
    (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥) (ν : List I) :
    ∃ e : ℕ, 0 < e ∧ ∀ (v : List I), v.Perm ν →
      ∀ (r : ℕ) (i : I), v[r]? = some i →
        truncatedDot D Sc cutoff N v r ^ e = 0 := by
  obtain ⟨e, he, hp⟩ := truncatedContent_positive_pow_zeroOver D sy 𝒜 Sc hP cutoff N b h𝒜 ν
  refine ⟨e, he, fun v hv r i hi => hp v hv _ ?_ _
    (truncatedDot_degreeOver D sy 𝒜 Sc hP cutoff N hi)⟩
  have := sy.pos i
  omega

include sy 𝒜 hP in
/-- The appended last-strand dot is nilpotent, uniformly on the source content, over a base
ring graded in degrees `0, …, b`. -/
theorem truncatedAppendDot_pow_zeroOver [Finite I] (b : ℤ)
    (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥) (ν : List I) (i : I) :
    ∃ e : ℕ, 0 < e ∧ ∀ v : TruncatedCategory D Sc cutoff N, v.word.Perm ν →
      let f : TruncatedEnd D Sc cutoff N (v.word ++ [i]) :=
        (truncatedAppendDot D Sc cutoff N i).app (D.parity i) v
      f ^ e = 0 := by
  obtain ⟨e, he, hp⟩ :=
    truncatedContent_positive_pow_zeroOver D sy 𝒜 Sc hP cutoff N b h𝒜 (ν ++ [i])
  refine ⟨e, he, fun v hv => hp _ (hv.append (List.Perm.refl _)) _ ?_ _
    (truncatedAppendDot_degreeOver D sy 𝒜 Sc hP cutoff N i v)⟩
  have := sy.pos i
  omega

include sy 𝒜 hP in
/-- Over a base ring graded in degrees `0, …, b`, coefficient-graded homogeneous parameters give
nilpotence of the appended dot. -/
theorem truncatedAppendDotNilpotentOver [Finite I] (b : ℤ)
    (h𝒜 : ∀ m, m ∉ Set.Icc (0 : ℤ) b → 𝒜 m = ⊥) : TruncatedAppendDotNilpotent D Sc cutoff N :=
  truncatedAppendDot_pow_zeroOver D sy 𝒜 Sc hP cutoff N b h𝒜

end OddMath.QuiverHecke.ELVOld
