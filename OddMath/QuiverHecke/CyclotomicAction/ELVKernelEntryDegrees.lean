import OddMath.QuiverHecke.CyclotomicAction.ELVIndResKernelInteger
import OddMath.QuiverHecke.CyclotomicAction.ELVOldGeneratorDegrees
import OddMath.QuiverHecke.CyclotomicAction.ELVActualKernelMatrices

/-! # Integer degrees of the prescribed represented matrix entries

The forward finite matrix uses the literal signed mate, ordinary dot/cap
rows and unscaled unit/dot columns. Their degrees are proved on the
intrinsic represented Hom-tensor grading; no grading of arbitrary
module Homs or inverse-degree premise is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory GradedSupercategory
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
  (sy : SKM.Symmetrizer D) (hc : Sc.Homogeneous)
private theorem oldComp_degree {v t w : OldCategory D Sc cutoff} {m n : ℤ}
    (f : v ⟶ t) (g : t ⟶ w)
    (hf : f ∈ oldDegree D sy Sc hc cutoff v.word t.word m)
    (hg : g ∈ oldDegree D sy Sc hc cutoff t.word w.word n) :
    f ≫ g ∈ oldDegree D sy Sc hc cutoff v.word w.word (m + n) := by
  obtain ⟨a, ha, rfl⟩ := hf
  obtain ⟨b, hb, rfl⟩ := hg
  let := elvHomGrading D sy Sc hc cutoff
  exact Submodule.mem_map_of_mem (comp_mem_degree ha hb)

private theorem oldTwist_degree {v t : OldCategory D Sc cutoff} {n : ℤ}
    (p : ZMod 2) (f : v ⟶ t) (hf : f ∈ oldDegree D sy Sc hc cutoff v.word t.word n) :
    twist k p f ∈ oldDegree D sy Sc hc cutoff v.word t.word n := by
  rw [twist_apply, oldCategory_proj, oldCategory_proj]
  exact Submodule.add_mem _ (oldProj_mem_oldDegree D sy Sc hc cutoff 0 hf)
    (Submodule.smul_mem _ _ (oldProj_mem_oldDegree D sy Sc hc cutoff 1 hf))

/-- The represented lower-loop degree is the sum of the two Hom degrees. -/
abbrev representedKernelDegree (i : I) (v t : OldCategory D Sc cutoff) (n : ℤ) :=
  letI := oldCategoryGradedSupercategory D Sc cutoff sy hc
  IndResKernel.integerDegree (k := k) (append D Sc cutoff i) v t n

/-- The chosen signed mate has degree `-2 dᵢ` on represented kernels. -/
theorem mateKernelComponent_degree (i : I) (v t : OldCategory D Sc cutoff)
    {n : ℤ} {x : IndResKernel.Component (k := k) (append D Sc cutoff i) v t}
    (hx : x ∈ representedKernelDegree D Sc cutoff sy hc i v t n) :
    mateKernelComponent D Sc cutoff i v t x ∈
      oldDegree D sy Sc hc cutoff (v.word ++ [i]) (t.word ++ [i]) (n - 2 * sy.d i) := by
  let := oldCategoryGradedSupercategory D Sc cutoff sy hc
  let : IsGradedSuperfunctor k (append D Sc cutoff i) := (oldAppendGraded D Sc cutoff sy hc i).isGraded
  refine ((IndResKernel.integerDegree_le_iff (append D Sc cutoff i) v t n
    ((oldDegree D sy Sc hc cutoff (v.word ++ [i]) (t.word ++ [i]) (n - 2 * sy.d i)).comap
      (mateKernelComponent D Sc cutoff i v t))).2 ?_) hx
  intro s q r hqr g hg b hb
  simp only [Submodule.mem_comap]
  rw [IndResKernel.componentTensor, mateKernelComponent_tensor]
  change g ∈ oldDegree D sy Sc hc cutoff ((append D Sc cutoff i).obj s).word t.word q at hg
  change b ∈ oldDegree D sy Sc hc cutoff v.word ((append D Sc cutoff i).obj s).word r at hb
  have hd := oldComp_degree D Sc cutoff sy hc
    ((append D Sc cutoff i).map b)
    (equalCrossComponent D Sc cutoff i s ≫ twist k (D.parity i) ((append D Sc cutoff i).map g))
    (oldAppend_mem_degree D Sc cutoff sy hc i hb)
    (oldComp_degree D Sc cutoff sy hc (equalCrossComponent D Sc cutoff i s)
      (twist k (D.parity i) ((append D Sc cutoff i).map g))
      (equalCrossComponent_degree D Sc cutoff sy hc i s)
      (oldTwist_degree D Sc cutoff sy hc (D.parity i) _ (oldAppend_mem_degree D Sc cutoff sy hc i hg)))
  have he : r + (-2 * sy.d i + q) = n - 2 * sy.d i := by omega
  simpa only [he] using (oldDegree D sy Sc hc cutoff (v.word ++ [i]) (t.word ++ [i])
    (r + (-2 * sy.d i + q))).neg_mem hd

set_option backward.dsimp.instances true in
/-- The chosen induction dot raises represented integer degree by `2 dᵢ`. -/
theorem dotKernelComponent_degree (i : I) (v t : OldCategory D Sc cutoff)
    {n : ℤ} {x : IndResKernel.Component (k := k) (append D Sc cutoff i) v t}
    (hx : x ∈ representedKernelDegree D Sc cutoff sy hc i v t n) :
    dotKernelComponent D Sc cutoff i v t x ∈
      representedKernelDegree D Sc cutoff sy hc i v t (n + 2 * sy.d i) := by
  let := oldCategoryGradedSupercategory D Sc cutoff sy hc
  let : IsGradedSuperfunctor k (append D Sc cutoff i) := (oldAppendGraded D Sc cutoff sy hc i).isGraded
  refine ((IndResKernel.integerDegree_le_iff (append D Sc cutoff i) v t n
    ((representedKernelDegree D Sc cutoff sy hc i v t (n + 2 * sy.d i)).comap
      (dotKernelComponent D Sc cutoff i v t))).2 ?_) hx
  intro s q r hqr g hg b hb
  simp only [Submodule.mem_comap]
  rw [IndResKernel.componentTensor, dotKernelComponent_tensor]
  change g ∈ oldDegree D sy Sc hc cutoff ((append D Sc cutoff i).obj s).word t.word q at hg
  have hnew : oldAppendDotComponent D Sc cutoff i s ≫ twist k (D.parity i) g ∈
      degree (R := k) ((append D Sc cutoff i).obj s) t (2 * sy.d i + q) := by
    change _ ∈ oldDegree D sy Sc hc cutoff ((append D Sc cutoff i).obj s).word t.word _
    exact oldComp_degree D Sc cutoff sy hc _ _ (oldAppendDotComponent_degree D Sc cutoff sy hc i s)
      (oldTwist_degree D Sc cutoff sy hc (D.parity i) g hg)
  have hd := IndResKernel.componentTensor_mem_integerDegree (append D Sc cutoff i) v t s
    (oldAppendDotComponent D Sc cutoff i s ≫ twist k (D.parity i) g) b hnew hb
  have he : 2 * sy.d i + q + r = n + 2 * sy.d i := by omega
  dsimp only [representedKernelDegree, IndResKernel.componentTensor,
    oldCategoryGradedSupercategory] at hd ⊢
  simpa only [he] using hd

/-- The actual dot powers have their prescribed multiple integer degree. -/
theorem dotKernelComponent_power_degree (i : I) (v t : OldCategory D Sc cutoff)
    (m : ℕ) {n : ℤ} {x : IndResKernel.Component (k := k) (append D Sc cutoff i) v t}
    (hx : x ∈ representedKernelDegree D Sc cutoff sy hc i v t n) :
    (dotKernelComponent D Sc cutoff i v t ^ m) x ∈
      representedKernelDegree D Sc cutoff sy hc i v t (n + 2 * sy.d i * m) := by
  let := oldCategoryGradedSupercategory D Sc cutoff sy hc
  induction m with
  | zero => simpa only [pow_zero, Module.End.one_apply, Nat.cast_zero, mul_zero, add_zero] using hx
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := dotKernelComponent_degree D Sc cutoff sy hc i v t ih
    have he : n + 2 * sy.d i * (m : ℤ) + 2 * sy.d i = n + 2 * sy.d i * (m + 1 : ℕ) := by
      push_cast
      ring
    simpa only [he] using h

/-- The ordinary chosen counit has represented degree zero. -/
theorem counitKernelComponent_degree (i : I) (v t : OldCategory D Sc cutoff)
    {n : ℤ} {x : IndResKernel.Component (k := k) (append D Sc cutoff i) v t}
    (hx : x ∈ representedKernelDegree D Sc cutoff sy hc i v t n) :
    counitKernelComponent D Sc cutoff i v t x ∈ oldDegree D sy Sc hc cutoff v.word t.word n := by
  let := oldCategoryGradedSupercategory D Sc cutoff sy hc
  let : IsGradedSuperfunctor k (append D Sc cutoff i) := (oldAppendGraded D Sc cutoff sy hc i).isGraded
  refine ((IndResKernel.integerDegree_le_iff (append D Sc cutoff i) v t n
    ((oldDegree D sy Sc hc cutoff v.word t.word n).comap
      (counitKernelComponent D Sc cutoff i v t))).2 ?_) hx
  intro s q r hqr g hg b hb
  simp only [Submodule.mem_comap]
  rw [IndResKernel.componentTensor, counitKernelComponent_tensor]
  change g ∈ oldDegree D sy Sc hc cutoff ((append D Sc cutoff i).obj s).word t.word q at hg
  change b ∈ oldDegree D sy Sc hc cutoff v.word ((append D Sc cutoff i).obj s).word r at hb
  have hd := oldComp_degree D Sc cutoff sy hc b g hb hg
  have he : r + q = n := by omega
  simpa only [he] using hd

/-- Every actual ordinary dot/cap row has degree `2 dᵢ m`. -/
theorem capKernelComponent_degree (i : I) (v t : OldCategory D Sc cutoff)
    (m : ℕ) {n : ℤ} {x : IndResKernel.Component (k := k) (append D Sc cutoff i) v t}
    (hx : x ∈ representedKernelDegree D Sc cutoff sy hc i v t n) :
    capKernelComponent D Sc cutoff i m v t x ∈
      oldDegree D sy Sc hc cutoff v.word t.word (n + 2 * sy.d i * m) :=
  counitKernelComponent_degree D Sc cutoff sy hc i v t
    (dotKernelComponent_power_degree D Sc cutoff sy hc i v t m hx)

/-- Every actual unscaled unit/dot column has degree `2 dᵢ m`, including
its prescribed scalar sign and exponent zero. -/
theorem unitKernelComponent_degree (i : I) (v t : OldCategory D Sc cutoff)
    (m : ℕ) {n : ℤ} {b : v ⟶ t}
    (hb : b ∈ oldDegree D sy Sc hc cutoff v.word t.word n) :
    unitKernelComponent D Sc cutoff i m v t b ∈
      oldDegree D sy Sc hc cutoff (v.word ++ [i]) (t.word ++ [i]) (n + 2 * sy.d i * m) := by
  let := oldCategoryGradedSupercategory D Sc cutoff sy hc
  cases v with
  | mk v =>
    cases t with
    | mk t =>
      change inductionUnitDotColumn D Sc cutoff i v t m b ∈ _
      rw [inductionUnitDotColumn_comp]
      have hm : (ideal D Sc cutoff (t ++ [i]) (t ++ [i])).mkQ (appendMovingPower D Sc cutoff i t m) ∈
          oldDegree D sy Sc hc cutoff (t ++ [i]) (t ++ [i]) (2 * sy.d i * m) := by
        apply Submodule.mem_map_of_mem
        rw [appendMovingPower_whisker, ← appendSourcePower_whisker]
        exact appendSourcePower_mem_degree D Sc cutoff sy hc i t m
      exact Submodule.smul_mem _ _ (oldComp_degree D Sc cutoff sy hc _ _
        (oldAppend_mem_degree D Sc cutoff sy hc i hb) hm)

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
