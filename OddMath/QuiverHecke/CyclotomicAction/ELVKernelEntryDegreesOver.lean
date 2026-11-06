/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVIndResKernelIntegerOver
import OddMath.QuiverHecke.CyclotomicAction.ELVOldCategoryGradingOver
import OddMath.QuiverHecke.CyclotomicAction.ELVTruncatedNilpotenceOver
import OddMath.QuiverHecke.CyclotomicAction.ELVKernelEntryDegrees

/-!
# Degrees of the represented kernel matrix entries over a graded base ring

Over a commutative `K`-algebra `R` graded by `𝒜`, the old quotient category is a graded
supercategory over `K` (`ELVOld.oldCategoryGradedSupercategoryOver`). The append functor
preserves its degrees (`oldAppend_mem_degreeOver`), the appended dot has degree `2 dᵢ` and the
equal-colour crossing has degree `-2 dᵢ`. The represented kernels carry the integer degree of
`IndResKernel.integerDegreeOver`, and the signed mate, the induction dot, the counit, the
dot/cap rows and the unit/dot columns shift it as in the field case
(`OddMath.QuiverHecke.CyclotomicAction.ELVKernelEntryDegrees`).
-/

-- `letI` keeps the restricted-scalar instances available to instance search in these proofs.
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory StringDiagrams Supercategory GradedSupercategory OddMath.Diagrams

namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor

universe u

variable {I X : Type u} [AddCommGroup X] (D : SKM.Datum I X) (sy : SKM.Symmetrizer D)
  {K : Type u} [CommRing K] {R : Type u} [CommRing R] [Algebra K R]
  (𝒜 : ℤ → Submodule K R) [GradedAlgebra 𝒜]
  (Sc : SKM.Scalars D R)
  (hP : CoefficientGrading.IsHomogeneous 𝒜 (gdeg D sy) (pres D Sc)) (cutoff : I → ℕ)

omit [Algebra K R] in
/-- A sign multiple stays in an additive subgroup. -/
private theorem sign_smul_mem {M : Type*} {_ : AddCommGroup M} {_ : Module R M}
    {_ : Module K M} (S : Submodule K M) (q : ZMod 2) {x : M} (hx : x ∈ S) : sign R q • x ∈ S := by
  rcases parity_eq_zero_or_one q with rfl | rfl
  · simpa using hx
  · simpa using S.neg_mem hx

/-- The equal-colour crossing of the last two strands has degree `-2 dᵢ`, over a graded base. -/
theorem crossLast_mem_presentedPart (s : List I) (i : I) :
    crossLast D Sc s i i ∈ CoefficientGrading.presentedPart 𝒜 (gdeg D sy) (pres D Sc)
      (ob D (s ++ [i] ++ [i])) (ob D (s ++ [i] ++ [i])) (-2 * sy.d i) := by
  have h := cl_mem_presentedPart D sy 𝒜 Sc (t := s ++ [i] ++ [i]) (t' := s ++ [i] ++ [i])
    [PG.cross s.length] (by simpa using sChain_crossAt s [] i i)
  unfold crossLast
  convert h using 1
  symm
  simp [pl, PG.ld, gdeg, SKM.Datum.d_self]
  ring_nf

/-- The append functor preserves degrees of the old quotient, over a graded base. -/
theorem oldAppend_mem_degreeOver (i : I) {v w : OldCategory D Sc cutoff} {n : ℤ} {f : v ⟶ w}
    (hf : f ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v w n) :
    (append D Sc cutoff i).map f ∈
      oldDegreeOver D sy 𝒜 Sc hP cutoff ((append D Sc cutoff i).obj v)
        ((append D Sc cutoff i).obj w) n := by
  obtain ⟨a, ha, rfl⟩ := hf
  exact ⟨_, rightContext_mem_degreeOver D sy 𝒜 Sc hP cutoff [i] ha, rfl⟩

/-- Parity twists preserve degrees of the old quotient, over a graded base. -/
theorem oldTwist_mem_degreeOver {v t : OldCategory D Sc cutoff} {n : ℤ} (p : ZMod 2)
    (f : v ⟶ t) (hf : f ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v t n) :
    twist R p f ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v t n := by
  letI := Linear.restrictScalars K R (OldCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (OldCategory D Sc cutoff)
  letI := oldCategoryGradedSupercategoryOver D sy 𝒜 Sc hP cutoff
  have hf' : f ∈ degree (R := K) v t n := hf
  rw [twist_apply, ← Supercategory.proj_restrictScalars K R (OldCategory D Sc cutoff) 0 f,
    ← Supercategory.proj_restrictScalars K R (OldCategory D Sc cutoff) 1 f]
  exact Submodule.add_mem _ (proj_mem_degree (R := K) 0 hf')
    (sign_smul_mem _ _ (proj_mem_degree (R := K) 1 hf'))

/-- Composition adds degrees in the old quotient, over a graded base. -/
theorem oldComp_mem_degreeOver {v t w : OldCategory D Sc cutoff} {m n : ℤ}
    {f : v ⟶ t} {g : t ⟶ w}
    (hf : f ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v t m)
    (hg : g ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff t w n) :
    f ≫ g ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v w (m + n) := by
  letI := Linear.restrictScalars K R (OldCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (OldCategory D Sc cutoff)
  letI := oldCategoryGradedSupercategoryOver D sy 𝒜 Sc hP cutoff
  exact comp_mem_degree (R := K) (C := OldCategory D Sc cutoff) hf hg

/-- The prescribed last dot has degree `2 dᵢ`, over a graded base. -/
theorem oldAppendDotComponent_degreeOver (i : I) (s : OldCategory D Sc cutoff) :
    oldAppendDotComponent D Sc cutoff i s ∈
      oldDegreeOver D sy 𝒜 Sc hP cutoff ((append D Sc cutoff i).obj s)
        ((append D Sc cutoff i).obj s) (2 * sy.d i) :=
  mkQ_mem_oldDegreeOver D sy 𝒜 Sc hP cutoff
    (affineUnit_mem_degreeOver D sy 𝒜 Sc hP cutoff
      (CoefficientGrading.wL_mem_presentedPart (ob D s.word)
        (dotE_mem_presentedPart D sy 𝒜 Sc (v := [i]) (r := 0) rfl)))

/-- The prescribed last equal crossing has degree `-2 dᵢ`, over a graded base. -/
theorem equalCrossComponent_degreeOver (i : I) (s : OldCategory D Sc cutoff) :
    equalCrossComponent D Sc cutoff i s ∈
      oldDegreeOver D sy 𝒜 Sc hP cutoff ((append D Sc cutoff i).obj ((append D Sc cutoff i).obj s))
        ((append D Sc cutoff i).obj ((append D Sc cutoff i).obj s)) (-2 * sy.d i) :=
  mkQ_mem_oldDegreeOver D sy 𝒜 Sc hP cutoff
    (affineUnit_mem_degreeOver D sy 𝒜 Sc hP cutoff (crossLast_mem_presentedPart D sy 𝒜 Sc s.word i))

/-- The represented lower-loop degree over a graded base: the sum of the two Hom degrees. -/
abbrev representedKernelDegreeOver (i : I) (v t : OldCategory D Sc cutoff) (n : ℤ) :=
  letI := Linear.restrictScalars K R (OldCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (OldCategory D Sc cutoff)
  letI := oldCategoryGradedSupercategoryOver D sy 𝒜 Sc hP cutoff
  letI : ∀ X Y : OldCategory D Sc cutoff, IsScalarTower K R (X ⟶ Y) :=
    Linear.isScalarTower_restrictScalars K R _
  IndResKernel.integerDegreeOver (K := K) (R := R) (append D Sc cutoff i) v t n

/-- The chosen signed mate has degree `-2 dᵢ` on represented kernels, over a graded base. -/
theorem mateKernelComponent_degreeOver (i : I) (v t : OldCategory D Sc cutoff)
    {n : ℤ} {x : IndResKernel.Component (k := R) (append D Sc cutoff i) v t}
    (hx : x ∈ representedKernelDegreeOver D sy 𝒜 Sc hP cutoff i v t n) :
    mateKernelComponent D Sc cutoff i v t x ∈
      oldDegreeOver D sy 𝒜 Sc hP cutoff ((append D Sc cutoff i).obj v)
        ((append D Sc cutoff i).obj t) (n - 2 * sy.d i) := by
  letI := Linear.restrictScalars K R (OldCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (OldCategory D Sc cutoff)
  letI := oldCategoryGradedSupercategoryOver D sy 𝒜 Sc hP cutoff
  let _ : ∀ X Y : OldCategory D Sc cutoff, IsScalarTower K R (X ⟶ Y) :=
    Linear.isScalarTower_restrictScalars K R _
  refine ((IndResKernel.integerDegreeOver_le_iff (K := K) (R := R) (append D Sc cutoff i) v t n
    ((oldDegreeOver D sy 𝒜 Sc hP cutoff ((append D Sc cutoff i).obj v)
      ((append D Sc cutoff i).obj t) (n - 2 * sy.d i)).comap
      ((mateKernelComponent D Sc cutoff i v t).restrictScalars K))).2 ?_) hx
  intro s q r hqr g hg b hb
  simp only [Submodule.mem_comap, LinearMap.coe_restrictScalars]
  rw [IndResKernel.componentTensor, mateKernelComponent_tensor]
  have hd := oldComp_mem_degreeOver D sy 𝒜 Sc hP cutoff
    (oldAppend_mem_degreeOver D sy 𝒜 Sc hP cutoff i hb)
    (oldComp_mem_degreeOver D sy 𝒜 Sc hP cutoff
      (equalCrossComponent_degreeOver D sy 𝒜 Sc hP cutoff i s)
      (oldTwist_mem_degreeOver D sy 𝒜 Sc hP cutoff (D.parity i) _
        (oldAppend_mem_degreeOver D sy 𝒜 Sc hP cutoff i hg)))
  rw [show n - 2 * sy.d i = r + (-2 * sy.d i + q) by omega]
  exact Submodule.neg_mem _ hd

/-- The chosen induction dot raises represented degree by `2 dᵢ`, over a graded base. -/
theorem dotKernelComponent_degreeOver (i : I) (v t : OldCategory D Sc cutoff)
    {n : ℤ} {x : IndResKernel.Component (k := R) (append D Sc cutoff i) v t}
    (hx : x ∈ representedKernelDegreeOver D sy 𝒜 Sc hP cutoff i v t n) :
    dotKernelComponent D Sc cutoff i v t x ∈
      representedKernelDegreeOver D sy 𝒜 Sc hP cutoff i v t (n + 2 * sy.d i) := by
  letI := Linear.restrictScalars K R (OldCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (OldCategory D Sc cutoff)
  letI := oldCategoryGradedSupercategoryOver D sy 𝒜 Sc hP cutoff
  let _ : ∀ X Y : OldCategory D Sc cutoff, IsScalarTower K R (X ⟶ Y) :=
    Linear.isScalarTower_restrictScalars K R _
  refine ((IndResKernel.integerDegreeOver_le_iff (K := K) (R := R) (append D Sc cutoff i) v t n
    ((representedKernelDegreeOver D sy 𝒜 Sc hP cutoff i v t (n + 2 * sy.d i)).comap
      ((dotKernelComponent D Sc cutoff i v t).restrictScalars K))).2 ?_) hx
  intro s q r hqr g hg b hb
  simp only [Submodule.mem_comap, LinearMap.coe_restrictScalars]
  rw [IndResKernel.componentTensor, dotKernelComponent_tensor]
  have hnew := oldComp_mem_degreeOver D sy 𝒜 Sc hP cutoff
    (oldAppendDotComponent_degreeOver D sy 𝒜 Sc hP cutoff i s)
    (oldTwist_mem_degreeOver D sy 𝒜 Sc hP cutoff (D.parity i) g hg)
  have hd := IndResKernel.componentTensor_mem_integerDegreeOver (K := K) (R := R)
    (append D Sc cutoff i) v t s
    (oldAppendDotComponent D Sc cutoff i s ≫ twist R (D.parity i) g) b hnew hb
  rw [show n + 2 * sy.d i = 2 * sy.d i + q + r by omega]
  exact hd

/-- The induction dot powers have their multiple degree, over a graded base. -/
theorem dotKernelComponent_power_degreeOver (i : I) (v t : OldCategory D Sc cutoff)
    (m : ℕ) {n : ℤ} {x : IndResKernel.Component (k := R) (append D Sc cutoff i) v t}
    (hx : x ∈ representedKernelDegreeOver D sy 𝒜 Sc hP cutoff i v t n) :
    (dotKernelComponent D Sc cutoff i v t ^ m) x ∈
      representedKernelDegreeOver D sy 𝒜 Sc hP cutoff i v t (n + 2 * sy.d i * m) := by
  induction m with
  | zero => simpa only [pow_zero, Module.End.one_apply, Nat.cast_zero, mul_zero, add_zero] using hx
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply]
    have h := dotKernelComponent_degreeOver D sy 𝒜 Sc hP cutoff i v t ih
    rw [show n + 2 * sy.d i * ((m + 1 : ℕ) : ℤ) = n + 2 * sy.d i * (m : ℤ) + 2 * sy.d i by
      push_cast; ring]
    exact h

/-- The chosen counit has represented degree zero, over a graded base. -/
theorem counitKernelComponent_degreeOver (i : I) (v t : OldCategory D Sc cutoff)
    {n : ℤ} {x : IndResKernel.Component (k := R) (append D Sc cutoff i) v t}
    (hx : x ∈ representedKernelDegreeOver D sy 𝒜 Sc hP cutoff i v t n) :
    counitKernelComponent D Sc cutoff i v t x ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v t n := by
  letI := Linear.restrictScalars K R (OldCategory D Sc cutoff)
  letI := Supercategory.restrictScalars K R (OldCategory D Sc cutoff)
  letI := oldCategoryGradedSupercategoryOver D sy 𝒜 Sc hP cutoff
  let _ : ∀ X Y : OldCategory D Sc cutoff, IsScalarTower K R (X ⟶ Y) :=
    Linear.isScalarTower_restrictScalars K R _
  refine ((IndResKernel.integerDegreeOver_le_iff (K := K) (R := R) (append D Sc cutoff i) v t n
    ((oldDegreeOver D sy 𝒜 Sc hP cutoff v t n).comap
      ((counitKernelComponent D Sc cutoff i v t).restrictScalars K))).2 ?_) hx
  intro s q r hqr g hg b hb
  simp only [Submodule.mem_comap, LinearMap.coe_restrictScalars]
  rw [IndResKernel.componentTensor, counitKernelComponent_tensor]
  rw [show n = r + q by omega]
  exact oldComp_mem_degreeOver D sy 𝒜 Sc hP cutoff hb hg

/-- Every dot/cap row has degree `2 dᵢ m`, over a graded base. -/
theorem capKernelComponent_degreeOver (i : I) (v t : OldCategory D Sc cutoff)
    (m : ℕ) {n : ℤ} {x : IndResKernel.Component (k := R) (append D Sc cutoff i) v t}
    (hx : x ∈ representedKernelDegreeOver D sy 𝒜 Sc hP cutoff i v t n) :
    capKernelComponent D Sc cutoff i m v t x ∈
      oldDegreeOver D sy 𝒜 Sc hP cutoff v t (n + 2 * sy.d i * m) :=
  counitKernelComponent_degreeOver D sy 𝒜 Sc hP cutoff i v t
    (dotKernelComponent_power_degreeOver D sy 𝒜 Sc hP cutoff i v t m hx)

/-- Every unit/dot column has degree `2 dᵢ m`, including its sign, over a graded base. -/
theorem unitKernelComponent_degreeOver (i : I) (v t : OldCategory D Sc cutoff)
    (m : ℕ) {n : ℤ} {b : v ⟶ t}
    (hb : b ∈ oldDegreeOver D sy 𝒜 Sc hP cutoff v t n) :
    unitKernelComponent D Sc cutoff i m v t b ∈
      oldDegreeOver D sy 𝒜 Sc hP cutoff ((append D Sc cutoff i).obj v)
        ((append D Sc cutoff i).obj t) (n + 2 * sy.d i * m) := by
  letI := Linear.restrictScalars K R (OldCategory D Sc cutoff)
  cases v with
  | mk v =>
    cases t with
    | mk t =>
      change inductionUnitDotColumn D Sc cutoff i v t m b ∈ _
      rw [inductionUnitDotColumn_comp]
      have hm : ((ideal D Sc cutoff (t ++ [i]) (t ++ [i])).mkQ
          (appendMovingPower D Sc cutoff i t m) :
            (append D Sc cutoff i).obj (⟨t⟩ : OldCategory D Sc cutoff) ⟶
              (append D Sc cutoff i).obj (⟨t⟩ : OldCategory D Sc cutoff)) ∈
          oldDegreeOver D sy 𝒜 Sc hP cutoff ((append D Sc cutoff i).obj ⟨t⟩)
            ((append D Sc cutoff i).obj ⟨t⟩) (2 * sy.d i * m) := by
        refine mkQ_mem_oldDegreeOver D sy 𝒜 Sc hP cutoff ?_
        rw [appendMovingPower_whisker, ← appendSourcePower_whisker]
        exact appendSourcePower_mem_degreeOver D sy 𝒜 Sc hP cutoff i t m
      rw [inductionUnitDotSign]
      exact sign_smul_mem _ _ (oldComp_mem_degreeOver D sy 𝒜 Sc hP cutoff
        (oldAppend_mem_degreeOver D sy 𝒜 Sc hP cutoff i hb) hm)

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
