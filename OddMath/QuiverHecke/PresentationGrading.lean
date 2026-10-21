/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import StringDiagrams.Super.PresentedGraded

/-! Integer grading of a presented supercategory, used for the target algebras of BE2 (11.7)–(11.8). -/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
universe u v w z r
variable {S : Signature.{u,v,w}} {k : Type z} [CommRing k]
  (P : Presentation.{z,r} S k) (hp : P.IsParityHomogeneous) (deg : S.Gen → ℤ)
  (hd : P.IsHomogeneous deg)

private theorem presented_proj_eq {a b : P.Presented} (p : ZMod 2) (f : a ⟶ b) :
    letI := P.supercategory hp
    Supercategory.proj k p f = Presentation.homogeneousComponent hp p f := by
  let _ := P.supercategory hp
  refine Supercategory.induction_on (R := k) f ?_ ?_ ?_
  · exact (map_zero _).trans (map_zero (Presentation.homogeneousComponent hp p)).symm
  · intro q g hg
    by_cases hq : q = p
    · subst hq
      exact (Supercategory.proj_of_mem hg).trans
        (Presentation.homogeneousComponent_of_mem hp hg).symm
    · exact (Supercategory.proj_of_mem_ne hg hq).trans
        (Presentation.homogeneousComponent_of_mem_of_ne hp hg hq).symm
  · intro g h hg hh
    exact ((map_add _ g h).trans (congrArg₂ (· + ·) hg hh)).trans
      (map_add (Presentation.homogeneousComponent hp p) g h).symm

/-- The integer degree and parity decompositions of a presented category are compatible. -/
@[instance_reducible]
def presentedGrading :
    letI := P.supercategory hp
    GradedSupercategory k P.Presented := by
  let _ := P.supercategory hp
  exact
    { degree a b d := P.homDeg deg a.as b.as d
      isInternal_degree a b := Presentation.isInternal_homDeg hd a.as b.as
      proj_mem_degree := by
        intro a b n f p hf
        rw [presented_proj_eq P hp]
        exact Presentation.homogeneousComponent_mem_homDeg hp p hf
      id_mem_degree a := P.id_mem_homDeg deg a.as
      comp_mem_degree hf hg := Presentation.comp_mem_homDeg hf hg }

end OddMath.QuiverHecke
