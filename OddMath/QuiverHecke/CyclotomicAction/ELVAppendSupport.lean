/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendProjective

/-! # Finite moving support on the append endpoint

The common-row coordinates carry a filtration by the last-strand exponent.
Every vector has finite moving support. Arbitrary old matrix coefficients
preserve each filtration step; central movement is the proved exponent shift.
-/
noncomputable section
open scoped Classical DirectSum
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Common rows supported strictly below a moving-exponent bound. -/
def appendRowsBelow (i : I) (ν : List I) (N : ℕ) :
    Submodule (ContentRing D Sc cutoff ν)ᵐᵒᵖ (AppendRows D Sc cutoff i ν) where
  carrier := {z | ∀ q, N ≤ q.2 → z q = 0}
  zero_mem' := by intro q _; rfl
  add_mem' := by intro a b ha hb q hq; simp [ha q hq, hb q hq]
  smul_mem' := by
    intro a z hz q hq
    change a • z q = 0
    rw [hz q hq, smul_zero]

/-- Finite support gives a uniform upper bound on every moving exponent. -/
theorem appendRows_bounded (i : I) (ν : List I) (z : AppendRows D Sc cutoff i ν) :
    ∃ N, z ∈ appendRowsBelow D Sc cutoff i ν N := by
  refine ⟨z.support.sup (fun q => q.2 + 1), ?_⟩
  intro q hq
  by_contra hn
  have hm : q ∈ z.support := DFinsupp.mem_support_iff.mpr hn
  have hh := Finset.le_sup (f := fun q : AppendTailIndex i ν × ℕ => q.2 + 1) hm
  omega

/-- No old matrix coefficient can increase moving support. -/
theorem appendRows_old_nonincrease (i : I) (ν : List I) (N : ℕ)
    (a : (ContentRing D Sc cutoff ν)ᵐᵒᵖ) (z : AppendRows D Sc cutoff i ν)
    (hz : z ∈ appendRowsBelow D Sc cutoff i ν N) :
    a • z ∈ appendRowsBelow D Sc cutoff i ν N :=
  (appendRowsBelow D Sc cutoff i ν N).smul_mem a hz

/-- Actual endpoint extraction intertwines the full, noncommutative old action. -/
theorem appendDecode_old_action (i : I) (ν : List I)
    (a : (ContentRing D Sc cutoff ν)ᵐᵒᵖ) (z : AppendContent D Sc cutoff i ν) :
    appendDecode D Sc cutoff i ν (a • z) = a • appendDecode D Sc cutoff i ν z :=
  appendDecode_smul D Sc cutoff i ν a z

/-- Actual endpoint extraction carries the central dot/square to last-power translation. -/
theorem appendDecode_central (i : I) (ν : List I) (z : AppendContent D Sc cutoff i ν) :
    appendDecode D Sc cutoff i ν (appendContentCentral D Sc cutoff i ν z) =
      appendRowsShift D Sc cutoff i ν (centralDegree D i) (appendDecode D Sc cutoff i ν z) := by
  apply appendRowsReconstruct_injective D Sc cutoff i ν
  rw [appendRowsReconstruct_decode, appendRowsReconstruct_shift, appendRowsReconstruct_decode]

end OddMath.QuiverHecke.ELVOld
