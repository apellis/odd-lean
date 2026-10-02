import OddMath.Frontier.EQSmallRankDG
import DG.Homotopy.Comparison
import DG.K0.DGRing

/-!
# The actual integral low-rank dg-ring quasi-isomorphism

The unit inclusion from `ℤ` concentrated in degree zero into `OPol_N` is a dg-ring
quasi-isomorphism for `N ≤ 1`. Unlike an abstract computation of cohomology groups,
this identifies the map inducing the isomorphisms. It uses the proved integral
low-rank calculation, with the original differential `d(x) = x²` unchanged.
Keller's theorem then gives the ordinary derived equivalence and the induced
isomorphism of compact Grothendieck groups, carrying the regular class to the
regular class. No half-graded equivalence or tensor-product formula is asserted.
-/

noncomputable section
universe w₁ w₂
namespace OddMath.Frontier.EQSmallRankDG
open EQSkewDifferential CategoryTheory
open scoped DG.DegreeZero

/-- The ordinary unit inclusion, preserving the actual grading and differential. -/
def intInclusion (N : ℕ) : ℤ →ᵈᵍ+* OPol N where
  __ := Int.castRingHom (OPol N)
  map_mem' := by
    intro n z hz
    rcases DG.DegreeZero.mem_grading_iff.mp hz with rfl | rfl
    · change (z : OPol N) ∈ DG.grading 0
      rw [← zsmul_one]
      exact AddSubgroup.zsmul_mem _ DG.one_mem_grading z
    · change ((0 : ℤ) : OPol N) ∈ DG.grading n
      rw [Int.cast_zero]
      exact zero_mem _
  map_d' z := by
    change ((DG.d z : ℤ) : OPol N) = DG.d (z : OPol N)
    rw [DG.DegreeZero.d_apply, Int.cast_zero, DG.d_intCast]

/-- The actual unit inclusion is a quasi-isomorphism in integral ranks zero and one. -/
theorem intInclusion_isQuasiIso {N : ℕ} (hN : N ≤ 1) :
    (intInclusion N).IsQuasiIso := by
  intro n
  constructor
  · apply (injective_iff_map_eq_zero _).mpr
    intro x hx
    induction x using DG.cohomology.induction_on with
    | h z =>
      rw [DG.DGRingHom.cohomologyMap_mk] at hx
      obtain ⟨g, _, hg⟩ := (DG.cohomology.mk_eq_zero_iff _).mp hx
      have hz : (z : ℤ) = 0 := dg_int_eq_zero_of_boundary hN hg.symm
      have hzero : z = 0 := Subtype.ext hz
      rw [hzero, map_zero]
  · intro x
    by_cases hn : n = 0
    · subst n
      obtain ⟨z, rfl⟩ := intClass_surjective hN x
      refine ⟨DG.cohomology.mk ℤ 0 ⟨z, DG.mem_degreeZeroGrading_zero ℤ z, rfl⟩, ?_⟩
      rw [DG.DGRingHom.cohomologyMap_mk]
      rfl
    · exact ⟨0, (map_zero _).trans (cohomology_eq_zero_of_ne_zero hN hn x).symm⟩

section Derived

variable {N : ℕ} [DG.HasDerivedCategory.{w₁, 0} ℤ]
 [DG.HasDerivedCategory.{w₂, 0} (OPol N)]

/-- Ordinary derived induction along the actual integral unit inclusion is an equivalence. -/
def derivedEquivalence (hN : N ≤ 1) :
   DG.DerivedCategory ℤ ≌ DG.DerivedCategory (OPol N) :=
 (intInclusion N).derivedEquivalence (intInclusion_isQuasiIso hN)

/-- The induced equivalence of ordinary compact Grothendieck groups. -/
def compactK0Equiv (hN : N ≤ 1) :
   DG.DGRing.K0 ℤ ≃+ DG.DGRing.K0 (OPol N) :=
 DG.DGRing.K0.mapEquivOfIsQuasiIso (intInclusion N) (intInclusion_isQuasiIso hN)

/-- Derived induction sends the actual regular integral class to the regular polynomial class. -/
theorem compactK0Equiv_self (hN : N ≤ 1) :
   compactK0Equiv hN (DG.DGRing.K0.self ℤ) = DG.DGRing.K0.self (OPol N) :=
 DG.DGRing.K0.map_self (intInclusion N)

end Derived
end OddMath.Frontier.EQSmallRankDG
