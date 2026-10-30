/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVPDescent

/-!
# Full-ELV chronological short-image inclusion

The actual `pMap` sends the explicitly generated chronological short submodule
into the explicitly generated final equal-colour crossing submodule. The
old-factor balance twist is retained. This is the generator-factorization part
of `DeformedMackeyBoundary.md` (4)–(5), over the ground ring with full exterior
coefficients. Identification of the chronological short span with the PBW
short coordinate summand, and identification of the crossing span with the
prescribed balanced tensor target, are not asserted here.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Old insertion on the right, with the full coefficient Hom space. -/
abbrev appendInsert (i : I) (v w : List I) := rightContext D Sc cutoff [i] v w

/-- Chronological short generators at a fixed output. No PBW identification is asserted. -/
def chronologicalShortSpan (i : I) (v t : List I) :
    Submodule k (Target D Sc cutoff i v (t ++ [i])) :=
  Submodule.span k {z | ∃ s, ∃ r : hom D Sc cutoff v (s ++ [i]),
    ∃ h : hom D Sc cutoff (i :: s) t,
      projection D Sc cutoff i v (t ++ [i])
        (insert D Sc cutoff i v (s ++ [i]) r ≫
          rightContext D Sc cutoff [i] (i :: s) t h) = z}

/-- The explicit last equal-colour crossing span in the append quotient. -/
def chronologicalCrossingSpan (i : I) (v t : List I) :
    Submodule k (AppendTarget D Sc cutoff i v (t ++ [i])) :=
  Submodule.span k {z | ∃ s, ∃ r : hom D Sc cutoff v (s ++ [i]),
    ∃ g : hom D Sc cutoff (s ++ [i]) t,
      appendProjection D Sc cutoff i v (t ++ [i])
        (appendInsert D Sc cutoff i v (s ++ [i]) r ≫
          affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
          rightContext D Sc cutoff [i] (s ++ [i]) t g) = z}

/-- Moving the old factor through W retains its full parity twist. -/
theorem pMap_chronologicalShort_generator (i : I) (v s t : List I)
    (r : hom D Sc cutoff v (s ++ [i])) (h : hom D Sc cutoff (i :: s) t) :
    pMap D Sc cutoff i v (t ++ [i])
      (projection D Sc cutoff i v (t ++ [i])
        (insert D Sc cutoff i v (s ++ [i]) r ≫
          rightContext D Sc cutoff [i] (i :: s) t h)) =
    appendProjection D Sc cutoff i v (t ++ [i])
      (appendInsert D Sc cutoff i v (s ++ [i]) (twist k (appendQ D cutoff i v) r) ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
        rightContext D Sc cutoff [i] (s ++ [i]) t (appendW D Sc cutoff i s ≫ h)) := by
  have he := appendError_mem_appendRelations D Sc cutoff i
    (twist k (appendQ D cutoff i v) r)
  rw [appendError_apply, twist_twist] at he
  have hc := appendRelations_comp D Sc cutoff i he
    (rightContext D Sc cutoff [i] (i :: s) t h)
  have hz := (appendProjection_eq_zero_iff D Sc cutoff i v (t ++ [i]) _).mpr hc
  rw [Preadditive.sub_comp, map_sub, sub_eq_zero] at hz
  change appendProjection D Sc cutoff i v (t ++ [i])
    (appendW D Sc cutoff i v ≫ (insert D Sc cutoff i v (s ++ [i]) r ≫
      rightContext D Sc cutoff [i] (i :: s) t h)) = _
  rw [← Category.assoc, ← hz, appendW_append]
  simp only [appendInsert, rightContext_comp, Category.assoc]

/-- The concrete P sends the chronological short span into the crossing span. -/
theorem pMap_chronologicalShortSpan_le (i : I) (v t : List I) :
    (chronologicalShortSpan D Sc cutoff i v t).map
      (pMap D Sc cutoff i v (t ++ [i])) ≤ chronologicalCrossingSpan D Sc cutoff i v t := by
  rw [Submodule.map_le_iff_le_comap]
  apply Submodule.span_le.mpr
  rintro _ ⟨s, r, h, rfl⟩
  change pMap D Sc cutoff i v (t ++ [i]) _ ∈ chronologicalCrossingSpan D Sc cutoff i v t
  rw [pMap_chronologicalShort_generator]
  exact Submodule.subset_span ⟨s, twist k (appendQ D cutoff i v) r,
    appendW D Sc cutoff i s ≫ h, rfl⟩

end OddMath.QuiverHecke.ELVOld
