/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVOutputBalancedComparison

/-!
# Output old action and the chronological short span

The relative-coset stability needed for `DeformedMackeyBoundary.md` (2).
Arbitrary full-ELV output old arrows preserve the chronological short span.
By its exact kernel identification, equal long extractions remain equal after
old output endomorphisms. Transport across the bare long chain, including its
canonical coefficient twist, remains a separate obligation.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Output old arrows preserve the relative chronological short span, with full
ELV coefficients and arbitrary source and output words. -/
theorem act_appendInsert_chronologicalShortSpan (i : I) (v t w : List I)
    (g : hom D Sc cutoff t w) :
    (chronologicalShortSpan D Sc cutoff i v t).map
      (act D Sc cutoff i (appendInsert D Sc cutoff i t w g)) ≤
        chronologicalShortSpan D Sc cutoff i v w := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro _ ⟨s, r, h, rfl⟩
  change projection D Sc cutoff i v (w ++ [i])
    ((insert D Sc cutoff i v (s ++ [i]) r ≫
      rightContext D Sc cutoff [i] (i :: s) t h) ≫
      rightContext D Sc cutoff [i] t w g) ∈ chronologicalShortSpan D Sc cutoff i v w
  rw [Category.assoc, ← rightContext_comp]
  exact Submodule.subset_span ⟨s, r, h ≫ g, rfl⟩

/-- Equality of long output coordinates remains equality after an arbitrary
full old output endomorphism. This uses the exact relative kernel, not a bound
on the total crossing length. -/
theorem outputLongExtraction_act_appendInsert_congr (p : ZMod 2) (i : I) (v : List I)
    (g : hom D Sc cutoff v v) {x y : Target D Sc cutoff i v (v ++ [i])}
    (h : outputLongExtraction D Sc cutoff p i v x =
      outputLongExtraction D Sc cutoff p i v y) :
    outputLongExtraction D Sc cutoff p i v
      (act D Sc cutoff i (appendInsert D Sc cutoff i v v g) x) =
    outputLongExtraction D Sc cutoff p i v
      (act D Sc cutoff i (appendInsert D Sc cutoff i v v g) y) := by
  have hk : x - y ∈ chronologicalShortSpan D Sc cutoff i v v := by
    rw [← ker_outputLongExtraction_eq_chronologicalShortSpan D Sc cutoff p i v]
    change outputLongExtraction D Sc cutoff p i v (x - y) = 0
    rw [map_sub, h, sub_self]
  have hm := act_appendInsert_chronologicalShortSpan D Sc cutoff i v v v g
    (Submodule.mem_map_of_mem hk)
  rw [← ker_outputLongExtraction_eq_chronologicalShortSpan D Sc cutoff p i v] at hm
  change outputLongExtraction D Sc cutoff p i v
    (act D Sc cutoff i (appendInsert D Sc cutoff i v v g) (x - y)) = 0 at hm
  rwa [map_sub, map_sub, sub_eq_zero] at hm

end OddMath.QuiverHecke.ELVOld
