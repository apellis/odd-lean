/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.DistinctPureReservoirSector

/-! # Pure-reservoir braids with adjacent equal colours

The equal reservoir crossing agrees with the general normalized reservoir core.
Unlike probe crossings, no additional equal-colour scalar occurs here.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir

/-- A three-letter path whose probe content does not increase is entirely
reservoir. Step validity is recovered from the path, not assumed separately. -/
theorem pureReservoirPath_cases {ν : X} {i j r : I} {s t : Sector I}
    (ht : t.1 = s.1) (p : SPath (wd D ν [up i, up j, up r]) s t) :
    ∃ hi hj hr e, p = distinctPureReservoirPath ν i j r s hi hj hr e := by
  obtain ⟨a, b, c, ha, hb, hc, e, rfl⟩ := SPath.exists_eq_three p
  have h := congrArg (fun x : Sector I => x.1.sum (fun _ n => n)) e
  rw [ht] at h
  cases a <;> cases b <;> cases c <;>
    first | exact ⟨ha, hb, hc, e, rfl⟩ | (exfalso; simp [nextSector,
      Finsupp.sum_add_index' (h := fun (_ : I) (n : ℕ) => n)
        (fun _ => rfl) (fun _ _ _ => rfl)] at h <;> omega)

variable [∀ a b : B, PiSupercategory k (a ⟶ b)]
variable (P : ProbeReservoir k B D Sc)

/-- The pure-reservoir non-correction braid for arbitrary source and target
paths. Only the outer colours must differ; adjacent colours may coincide. -/
theorem pureReservoir_braid (ν : X) (i j r : I) {s t : Sector I}
    (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hir : i ≠ r)
    (ht : t.1 = s.1)
    (p : SPath (wd D ν [up i, up j, up r]) s t)
    (q : SPath (wd D ν [up r, up j, up i]) s t) (Z : P.H t) :
    braidLeft (P.swappedGens c L) i j r ν p q Z =
      braidRight (P.swappedGens c L) i j r ν p q Z := by
  obtain ⟨hi, hj, hr, e, rfl⟩ := pureReservoirPath_cases ht p
  obtain ⟨hr', hj', hi', e', rfl⟩ := pureReservoirPath_cases ht q
  exact P.pureReservoir_braid_canonical ν i j r s c L hir hi hj hr hr' hj' hi' e e' Z

/-- The adjacent-equal `i i j` pure-reservoir braid. -/
theorem adjacentPureReservoir_iij (ν : X) (i j : I) {s t : Sector I}
    (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hij : i ≠ j)
    (ht : t.1 = s.1)
    (p : SPath (wd D ν [up i, up i, up j]) s t)
    (q : SPath (wd D ν [up j, up i, up i]) s t) (Z : P.H t) :
    braidLeft (P.swappedGens c L) i i j ν p q Z =
      braidRight (P.swappedGens c L) i i j ν p q Z :=
  P.pureReservoir_braid ν i i j c L hij ht p q Z

/-- The adjacent-equal `i j j` pure-reservoir braid. -/
theorem adjacentPureReservoir_ijj (ν : X) (i j : I) {s t : Sector I}
    (c : P.CrossCoeff Sc) (L : P.LeftwardData) (hij : i ≠ j)
    (ht : t.1 = s.1)
    (p : SPath (wd D ν [up i, up j, up j]) s t)
    (q : SPath (wd D ν [up j, up j, up i]) s t) (Z : P.H t) :
    braidLeft (P.swappedGens c L) i j j ν p q Z =
      braidRight (P.swappedGens c L) i j j ν p q Z :=
  P.pureReservoir_braid ν i j j c L hij ht p q Z

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
