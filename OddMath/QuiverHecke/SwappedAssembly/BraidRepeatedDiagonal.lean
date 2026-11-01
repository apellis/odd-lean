/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidNonRepeated
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterPureProbeMatrix
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterPureReservoirMatrix
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterMiddleProbe
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterMiddleReservoir
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterLiteralDiagonal
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterBraid

/-! Global full diagonal correction for arbitrary repeated-outer paths. -/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc)

lemma braid_repeated_diag (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (i j : I) (ν : X) (hij : i ≠ j)
    {s t : Sector I} (p : SPath (wd D ν [up i, up j, up i]) s t) (Z : P.H t) :
    braidLeft (P.swappedGens c L) i j i ν p p Z -
      braidRight (P.swappedGens c L) i j i ν p p Z =
      ∑ a ∈ Finset.range (D.dn i j),
        (zsign k (D.parity i * (D.parity j + a)) * (Sc.t i j : k)) •
          (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] p Z) a ≫
            compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] p Z)
              (D.dn i j - 1 - a)) +
      ∑ b ∈ Finset.Ioo 0 (D.dn i j), ∑ d ∈ Finset.Ioo 0 (D.dn j i), ∑ a ∈ Finset.range b,
        (zsign k (D.parity i * (D.parity j + a)) * Sc.s i j b d) •
          (compPow (dotEntry (P.swappedGens c L) ν [up i, up j] i [] p Z) a ≫
            compPow (dotEntry (P.swappedGens c L) ν [up i] j [up i] p Z) d ≫
            compPow (dotEntry (P.swappedGens c L) ν [] i [up j, up i] p Z) (b - 1 - a)) := by
  obtain ⟨a, b, d, ha, hb, hd, e, rfl⟩ := SPath.exists_eq_three p
  cases a <;> cases b <;> cases d
  · exact P.repeatedOuterPureReservoir_braidEq_diag ν i j s c L ha hb hd e _ Z hij
  · obtain ⟨hj0, hi0⟩ := AdjacentReservoirSquareBlock.opposite_valid i j s ha hb hij
    have e' : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) = t := by
      simpa only [nextSector, tsub_right_comm] using e
    exact RepeatedOuterPre.full_diag_transport P i j s ha hb hj0 hi0 ν e e' Z c L hc h hij
  · exact P.middleProbe_braidEq_diag_transport ν i j s ha hd c L e Z _ hij
  · have et : nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)) = t := by
      simpa only [nextSector, add_right_comm] using e
    subst et
    exact P.repeatedOuter_braidEq_diag ν i j s c L ha e Z hc h hij
  · obtain ⟨hi, hj⟩ := AdjacentReservoirSquareBlock.opposite_valid j i s hb hd hij.symm
    have e' : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) = t := by
      simpa only [nextSector, tsub_right_comm] using e
    exact RepeatedOuterPost.full_diag_transport P i j s hb hd ν hi hj e e' Z c L hc h hij
  · exact P.middleReservoir_braidEq_diag_transport ν i j s hb c L e Z _ hij
  · exact P.separatedOuter_braidEq_diag_transport ν i j s hd e Z c L hc h hij
  · exact P.repeatedOuterPureProbe_braidEq_diag ν i j s c L e _ Z hij

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
