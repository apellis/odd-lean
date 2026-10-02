import OddMath.Frontier.EQLimaAllRanks
import OddMath.Frontier.EQLimaPoly
import OddMath.Frontier.EQZabCell
import OddMath.Frontier.EQDGStructures
import DG.Algebra.Cohomology

/-!
# Integral low-rank Ellis–Qi dg cohomology

The rank-zero and rank-one odd nilHecke rings are the corresponding odd polynomial
rings. We specialize the proved integral Lima-basis calculation (Ellis–Qi,
arXiv:1504.01712v2, Proposition A.2) to the empty partition, retaining the actual
differential `d(x) = x²`. This is an ordinary dg-cohomology comparison, not yet a
half-graded derived equivalence or a compact Grothendieck-group calculation.

`cohomologyZeroEquivInt` computes degree zero, normalized on actual integer classes;
`cohomology_eq_zero_of_ne_zero` handles every other degree. No quasi-isomorphism of
dg rings or equivalence of module categories is inferred just from these groups.
-/

noncomputable section
namespace OddMath.Frontier.EQSmallRankDG
open OddMath.SkewPolynomial (SkewPolynomial)
open EQSkewDifferential EQLima

private def emptyIndex (N : ℕ) : {μ : YoungDiagram // IsLima μ ∧ LengthLE N μ} :=
  ⟨⊥, isLima_bot, by simp [LengthLE]⟩

private theorem index_eq_empty {N : ℕ} (hN : N ≤ 1)
    (μ : {μ : YoungDiagram // IsLima μ ∧ LengthLE N μ}) : μ = emptyIndex N :=
  Subtype.ext (lima_lengthLE_small hN μ.property.1 μ.property.2)

/-- Every low-rank cocycle is a boundary plus an integral multiple of the empty Schur class. -/
theorem cocycle_normalForm {N : ℕ} (hN : N ≤ 1) {f : SkewPolynomial N}
    (hf : d N f = 0) : ∃ g : SkewPolynomial N, ∃ z : ℤ,
      f = d N g + z • schurU N ⊥ := by
  classical
  obtain ⟨g, _, a, ha⟩ := cocycle_eq_all N (EQZab.osym_small hN f) hf
  refine ⟨g, a (emptyIndex N), ha.trans ?_⟩
  congr 1
  rw [Finsupp.sum, Finset.sum_eq_single (emptyIndex N)]
  · rfl
  · intro μ _ hμ
    exact (hμ (index_eq_empty hN μ)).elim
  · intro h
    rw [Finsupp.notMem_support_iff.mp h, zero_smul]

/-- No nonzero integral multiple of the empty Schur class is a boundary. -/
theorem constant_eq_zero_of_boundary {N : ℕ} (hN : N ≤ 1) {g : SkewPolynomial N} {z : ℤ}
    (h : z • schurU N ⊥ = d N g) : z = 0 := by
  classical
  have hh := lima_independent_all N (Finsupp.single (emptyIndex N) z)
    (EQZab.osym_small hN g) (by
      rw [Finsupp.sum_single_index (h := fun
        (μ : {μ : YoungDiagram // IsLima μ ∧ LengthLE N μ}) (z : ℤ) =>
          z • schurU N μ.1) (zero_smul _ _)]
      exact h)
  simpa using congrArg (fun a => a (emptyIndex N)) hh

/-- The low-rank cohomology coefficient is unique, not just a spanning coefficient. -/
theorem normalForm_unique {N : ℕ} (hN : N ≤ 1) {f g g' : SkewPolynomial N} {z z' : ℤ}
    (h : f = d N g + z • schurU N ⊥)
    (h' : f = d N g' + z' • schurU N ⊥) : z = z' := by
  apply sub_eq_zero.mp
  apply constant_eq_zero_of_boundary hN (g := g' - g)
  rw [map_sub, sub_smul]
  have hh := h.symm.trans h'
  exact sub_eq_sub_iff_add_eq_add.mpr (by simpa [add_comm] using hh)

private theorem schur_empty {N : ℕ} (hN : N ≤ 1) : schurU N ⊥ = 1 := by
  have hrow : rowExp N ⊥ = 0 := by
    funext i
    apply Nat.eq_zero_of_not_pos
    intro hi
    exact YoungDiagram.notMem_bot _ (YoungDiagram.mem_iff_lt_rowLen.mpr hi)
  rw [schurU, hrow]
  exact EQZab.untwisted_zero_small hN

/-- Every cocycle of the actual low-rank dg ring is a boundary plus an integer. -/
theorem dg_cocycle_normalForm {N : ℕ} (hN : N ≤ 1) {f : OPol N}
    (hf : DG.d f = 0) : ∃ g : OPol N, ∃ z : ℤ, f = DG.d g + z := by
  obtain ⟨g, z, hz⟩ := cocycle_normalForm hN (f := (OPol.equiv N).symm f) hf
  refine ⟨OPol.equiv N g, z, ?_⟩
  apply (OPol.equiv N).symm.injective
  simpa only [map_add, map_intCast, OPol.symm_d, RingEquiv.symm_apply_apply,
    schur_empty hN, zsmul_one] using hz

/-- The integer class cannot disappear in low-rank dg cohomology. -/
theorem dg_int_eq_zero_of_boundary {N : ℕ} (hN : N ≤ 1) {g : OPol N} {z : ℤ}
    (h : (z : OPol N) = DG.d g) : z = 0 := by
  apply constant_eq_zero_of_boundary hN (g := (OPol.equiv N).symm g)
  simpa only [schur_empty hN, zsmul_one, map_intCast, OPol.symm_d] using
    congrArg (OPol.equiv N).symm h

private theorem int_mem_zero (N : ℕ) (z : ℤ) :
    (z : OPol N) ∈ DG.grading 0 := by
  rw [← zsmul_one]
  exact AddSubgroup.zsmul_mem _ DG.one_mem_grading z

private theorem boundary_of_eq {N : ℕ} {n : ℤ} {x : OPol N}
    (hx : x ∈ DG.grading n) {g : OPol N} (hg : DG.d g = x) :
    x ∈ DG.coboundaries (OPol N) n := by
  refine ⟨DirectSum.decompose (DG.grading (M := OPol N)) g (n - 1),
    (DirectSum.decompose (DG.grading (M := OPol N)) g (n - 1)).property, ?_⟩
  rw [← DG.decompose_d, sub_add_cancel, hg, DirectSum.decompose_of_mem_same _ hx]

/-- Every nonzero-degree cohomology class of the integral low-rank dg ring vanishes. -/
theorem cohomology_eq_zero_of_ne_zero {N : ℕ} (hN : N ≤ 1) {n : ℤ} (hn : n ≠ 0)
    (x : DG.cohomology (OPol N) n) : x = 0 := by
  classical
  induction x using DG.cohomology.induction_on with
  | h x =>
    obtain ⟨g, z, hz⟩ := dg_cocycle_normalForm hN x.property.2
    apply (DG.cohomology.mk_eq_zero_iff x).mpr
    have h := congrArg
      (fun y : OPol N => (DirectSum.decompose (DG.grading (M := OPol N)) y n : OPol N)) hz
    rw [DirectSum.decompose_of_mem_same (DG.grading (M := OPol N)) x.property.1,
      DirectSum.decompose_add,
      DirectSum.add_apply, AddSubgroup.coe_add,
      DirectSum.decompose_of_mem_ne (DG.grading (M := OPol N)) (int_mem_zero N z) hn.symm,
      add_zero] at h
    refine ⟨DirectSum.decompose (DG.grading (M := OPol N)) g (n - 1),
      (DirectSum.decompose (DG.grading (M := OPol N)) g (n - 1)).property, ?_⟩
    rw [← DG.decompose_d, sub_add_cancel]
    exact h.symm

/-- The actual degree-zero integer cocycles in `OPol_N`. -/
def intCocycles (N : ℕ) : ℤ →+ DG.cocycles (OPol N) 0 where
  toFun z := ⟨z, int_mem_zero N z, DG.d_intCast z⟩
  map_zero' := Subtype.ext (Int.cast_zero)
  map_add' a b := Subtype.ext (Int.cast_add a b)

/-- The degree-zero cohomology map taking an integer to its actual constant class. -/
def intClass (N : ℕ) : ℤ →+ DG.cohomology (OPol N) 0 :=
  (DG.cohomology.mk (OPol N) 0).comp (intCocycles N)

theorem intClass_injective {N : ℕ} (hN : N ≤ 1) : Function.Injective (intClass N) := by
  intro a b hab
  have hz : intClass N (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have hb := (DG.cohomology.mk_eq_zero_iff (intCocycles N (a - b))).mp hz
  obtain ⟨g, _, hg⟩ := hb
  exact sub_eq_zero.mp (dg_int_eq_zero_of_boundary hN hg.symm)

theorem intClass_surjective {N : ℕ} (hN : N ≤ 1) : Function.Surjective (intClass N) := by
  intro x
  induction x using DG.cohomology.induction_on with
  | h x =>
    obtain ⟨g, z, hz⟩ := dg_cocycle_normalForm hN x.property.2
    refine ⟨z, (DG.cohomology.mk_eq_mk_iff (intCocycles N z) x).mpr ?_⟩
    apply boundary_of_eq (sub_mem (int_mem_zero N z) x.property.1) (g := -g)
    rw [DG.d_neg, hz]
    abel

/-- `H⁰(OPol_N) ≃ ℤ` for `N = 0,1`, normalized on the class of the actual unit. -/
def cohomologyZeroEquivInt {N : ℕ} (hN : N ≤ 1) :
    DG.cohomology (OPol N) 0 ≃+ ℤ :=
  (AddEquiv.ofBijective (intClass N) ⟨intClass_injective hN, intClass_surjective hN⟩).symm

theorem cohomologyZeroEquivInt_intClass {N : ℕ} (hN : N ≤ 1) (z : ℤ) :
    cohomologyZeroEquivInt hN (intClass N z) = z :=
  (cohomologyZeroEquivInt hN).apply_symm_apply z

end OddMath.Frontier.EQSmallRankDG
