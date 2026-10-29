/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.DistinctPureReservoirSector
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.MiddleDistinctProbeSector
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.ReverseDistinctProbeSector
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.MiddleDistinctReservoirSector
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.ReverseDistinctReservoirSector

/-! # Pairwise-distinct braid entries for arbitrary sector paths

Endpoint uniqueness reduces arbitrary source and target paths to the eight
probe/reservoir placements. The pure placements use the supplied factor braids;
the six mixed placements retain their mixed parameter polynomials.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM
universe u
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc)

/-- The braid equality for three pairwise-distinct colours, on every pair of
source and target paths. This is the pairwise-distinct part of `CrossBraid.braid`,
not the remaining cases with adjacent equal colours or repeated outer colour. -/
theorem braid_pairwiseDistinct (ν : X) (i j r : I)
    (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hij : i ≠ j) (hir : i ≠ r) (hjr : j ≠ r) {s t : Sector I}
    (p : SPath (wd D ν [up i, up j, up r]) s t)
    (q : SPath (wd D ν [up r, up j, up i]) s t) (Z : P.H t) :
    braidLeft (P.swappedGens c L) i j r ν p q Z =
      braidRight (P.swappedGens c L) i j r ν p q Z := by
  obtain ⟨a, b, d, ha, hb, hd, e, _⟩ := SPath.exists_eq_three p
  cases a <;> cases b <;> cases d
  · have vr : StepValid (true, r) false s := by
      simpa [StepValid, nextSector, hir.symm, hjr.symm] using hd
    have vj : StepValid (true, j) false (nextSector (true, r) false s) := by
      simpa [StepValid, nextSector, hij.symm, hjr] using hb
    have vi : StepValid (true, i) false (nextSector (true, j) false
        (nextSector (true, r) false s)) := by
      simpa [StepValid, nextSector, hij, hir] using ha
    have e' : nextSector (true, i) false (nextSector (true, j) false
        (nextSector (true, r) false s)) = t := by
      simpa only [nextSector, tsub_right_comm] using e
    rw [path_eq_three_distinct hij hir hjr p
      (distinctPureReservoirPath ν i j r s ha hb hd e),
      path_eq_three_distinct hjr.symm hir.symm hij.symm q
        (distinctPureReservoirPath ν r j i s vr vj vi e')]
    exact P.distinctPureReservoir_braid ν i j r s c L hij hir hjr
      ha hb hd vr vj vi e e' Z
  · have vy : StepValid (true, i) false s := by
      simpa [StepValid, nextSector, hij, hir, hjr, hij.symm, hir.symm, hjr.symm] using ha
    have vz : StepValid (true, j) false (nextSector (true, i) false s) := by
      simpa [StepValid, nextSector, hij, hir, hjr, hij.symm, hir.symm, hjr.symm] using hb
    have vz' : StepValid (true, j) false s := by
      simpa [StepValid, nextSector, hij, hir, hjr, hij.symm, hir.symm, hjr.symm] using vz
    have vy' : StepValid (true, i) false (nextSector (true, j) false s) := by
      simpa [StepValid, nextSector, hij, hir, hjr, hij.symm, hir.symm, hjr.symm] using vy
    have et : nextSector (true, i) false (nextSector (true, j) false
        (nextSector (true, r) true s)) = t := by
      simpa only [nextSector, tsub_right_comm] using e
    cases et
    have es : nextSector (true, j) false (nextSector (true, i) false
        (nextSector (true, r) true s)) = nextSector (true, i) false
          (nextSector (true, j) false (nextSector (true, r) true s)) := by
      simp only [nextSector, tsub_right_comm]
    rw [path_eq_three_distinct hij hir hjr p (distinctReservoirTarget ν r i j s vy vz es),
      path_eq_three_distinct hjr.symm hir.symm hij.symm q
        (distinctReservoirSource ν r j i s vz' vy' rfl)]
    exact P.reverseDistinctReservoir_braid ν r i j s vy vz vz' vy' c L
      hir.symm hjr.symm hij es Z
  · have vy : StepValid (true, i) false s := by
      simpa [StepValid, nextSector, hij, hir, hjr, hij.symm, hir.symm, hjr.symm] using ha
    have vz : StepValid (true, r) false (nextSector (true, i) false s) := by
      simpa [StepValid, nextSector, hij, hir, hjr, hij.symm, hir.symm, hjr.symm] using hd
    have vz' : StepValid (true, r) false s := by
      simpa [StepValid, nextSector, hij, hir, hjr, hij.symm, hir.symm, hjr.symm] using vz
    have vy' : StepValid (true, i) false (nextSector (true, r) false s) := by
      simpa [StepValid, nextSector, hij, hir, hjr, hij.symm, hir.symm, hjr.symm] using vy
    have et : nextSector (true, i) false (nextSector (true, r) false
        (nextSector (true, j) true s)) = t := by
      simpa only [nextSector, tsub_right_comm] using e
    cases et
    have es : nextSector (true, r) false (nextSector (true, i) false
        (nextSector (true, j) true s)) = nextSector (true, i) false
          (nextSector (true, r) false (nextSector (true, j) true s)) := by
      simp only [nextSector, tsub_right_comm]
    rw [path_eq_three_distinct hij hir hjr p (distinctReservoirMiddle ν j i r s vy vz es),
      path_eq_three_distinct hjr.symm hir.symm hij.symm q
        (distinctReservoirMiddle ν j r i s vz' vy' rfl)]
    exact P.middleDistinctReservoir_braid ν j i r s vy vz vz' vy' c L
      hij.symm hjr hir es Z
  · have vz : StepValid (true, i) false s := by
      simpa only [StepValid, nextSector] using ha
    have et : nextSector (true, i) false (nextSector (true, j) true
        (nextSector (true, r) true s)) = t := by
      simpa only [nextSector, add_right_comm] using e
    cases et
    have es : nextSector (true, i) false (nextSector (true, r) true
        (nextSector (true, j) true s)) = nextSector (true, i) false
          (nextSector (true, j) true (nextSector (true, r) true s)) := by
      simp only [nextSector, add_right_comm]
    rw [path_eq_three_distinct hij hir hjr p (distinctProbeTarget ν j r i s vz es),
      path_eq_three_distinct hjr.symm hir.symm hij.symm q
        (distinctProbeSource ν r j i s vz rfl)]
    exact P.reverseDistinctProbe_braid ν j r i s vz c L hjr hij.symm hir.symm es Z
  · have vy : StepValid (true, j) false s := by
      simpa [StepValid, nextSector, hij, hir, hjr, hij.symm, hir.symm, hjr.symm] using hb
    have vz : StepValid (true, r) false (nextSector (true, j) false s) := by
      simpa [StepValid, nextSector, hij, hir, hjr, hij.symm, hir.symm, hjr.symm] using hd
    have vz' : StepValid (true, r) false s := by
      simpa [StepValid, nextSector, hij, hir, hjr, hij.symm, hir.symm, hjr.symm] using vz
    have vy' : StepValid (true, j) false (nextSector (true, r) false s) := by
      simpa [StepValid, nextSector, hij, hir, hjr, hij.symm, hir.symm, hjr.symm] using vy
    have et : nextSector (true, j) false (nextSector (true, r) false
        (nextSector (true, i) true s)) = t := by
      simpa only [nextSector, tsub_right_comm] using e
    cases et
    have es : nextSector (true, r) false (nextSector (true, j) false
        (nextSector (true, i) true s)) = nextSector (true, j) false
          (nextSector (true, r) false (nextSector (true, i) true s)) := by
      simp only [nextSector, tsub_right_comm]
    rw [path_eq_three_distinct hij hir hjr p (distinctReservoirSource ν i j r s vy vz es),
      path_eq_three_distinct hjr.symm hir.symm hij.symm q
        (distinctReservoirTarget ν i r j s vz' vy' rfl)]
    exact P.distinctReservoir_braid ν i j r s vy vz vz' vy' c L
      hij hir hjr es Z
  · have vz : StepValid (true, j) false s := by
      simpa only [StepValid, nextSector] using hb
    have et : nextSector (true, j) false (nextSector (true, i) true
        (nextSector (true, r) true s)) = t := by
      simpa only [nextSector, add_right_comm] using e
    cases et
    have es : nextSector (true, j) false (nextSector (true, r) true
        (nextSector (true, i) true s)) = nextSector (true, j) false
          (nextSector (true, i) true (nextSector (true, r) true s)) := by
      simp only [nextSector, add_right_comm]
    rw [path_eq_three_distinct hij hir hjr p (distinctProbeMiddle ν i r j s vz es),
      path_eq_three_distinct hjr.symm hir.symm hij.symm q
        (distinctProbeMiddle ν r i j s vz rfl)]
    exact P.middleDistinctProbe_braid ν i r j s vz c L hir hij hjr.symm es Z
  · have vz : StepValid (true, r) false s := by
      simpa only [StepValid, nextSector] using hd
    have et : nextSector (true, r) false (nextSector (true, i) true
        (nextSector (true, j) true s)) = t := by
      simpa only [nextSector, add_right_comm] using e
    cases et
    have es : nextSector (true, r) false (nextSector (true, j) true
        (nextSector (true, i) true s)) = nextSector (true, r) false
          (nextSector (true, i) true (nextSector (true, j) true s)) := by
      simp only [nextSector, add_right_comm]
    rw [path_eq_three_distinct hij hir hjr p (distinctProbeSource ν i j r s vz es),
      path_eq_three_distinct hjr.symm hir.symm hij.symm q
        (distinctProbeTarget ν j i r s vz rfl)]
    exact P.distinctProbe_braid ν i j r s vz c L hij hir hjr es Z
  · have e' : nextSector (true, i) true (nextSector (true, j) true
        (nextSector (true, r) true s)) = t := by
      simpa only [nextSector, add_assoc, add_comm, add_left_comm] using e
    rw [path_eq_three_distinct hij hir hjr p (distinctPureProbePath ν i j r s e),
      path_eq_three_distinct hjr.symm hir.symm hij.symm q (distinctPureProbePath ν r j i s e')]
    exact P.distinctPureProbe_braid ν i j r s c L hij hir hjr e e' Z

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
