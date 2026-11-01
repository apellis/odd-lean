/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidRepeatedDiagonal

/-! Global structural assembly of the actual swapped CrossBraid fields. -/
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

lemma braid_repeated_offDiag (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (i j : I) (ν : X) (hij : i ≠ j)
    {s t : Sector I} (p q : SPath (wd D ν [up i, up j, up i]) s t)
    (Z : P.H t) (hpq : p ≠ q) :
    braidLeft (P.swappedGens c L) i j i ν p q Z =
      braidRight (P.swappedGens c L) i j i ν p q Z := by
  obtain ⟨a, b, d, ha, hb, hd, e, hp⟩ := SPath.exists_eq_three p
  cases a <;> cases b <;> cases d
  · exact (hpq (repeatedOuterPureReservoir_path_eq ν i j (by rw [← e]; rfl) p q)).elim
  · obtain ⟨hj0, hi0⟩ := AdjacentReservoirSquareBlock.opposite_valid i j s ha hb hij
    have e' : nextSector (true, i) false (nextSector (true, j) false (nextSector (true, i) true s)) = t := by
      simpa only [nextSector, tsub_right_comm] using e
    rcases adjacentPost_iji_cases hij ha hb hj0 hi0 e e' q with hq | hq
    · exact (hpq (hp.trans hq.symm)).elim
    · exact RepeatedOuterReservoirReverse.braid_entry_path P i j s ha hb hj0 hi0 ν e e' Z p q hp hq c L hc h hij
  · cases e
    exact (hpq ((reservoirPairMiddle_unique ν j i s ha hd hij.symm p).trans
      (reservoirPairMiddle_unique ν j i s ha hd hij.symm q).symm)).elim
  · have e' : nextSector (true, i) false (nextSector (true, j) true (nextSector (true, i) true s)) = t := by
      simpa only [nextSector, add_right_comm] using e
    exact P.repeatedOuter_oneReservoir_offDiag ν i j s ha c L hc h hij e e' p q Z hpq
  · obtain ⟨hi, hj⟩ := AdjacentReservoirSquareBlock.opposite_valid j i s hb hd hij.symm
    have e' : nextSector (true, j) false (nextSector (true, i) false (nextSector (true, i) true s)) = t := by
      simpa only [nextSector, tsub_right_comm] using e
    rcases adjacentPost_iji_cases hij hi hj hb hd e' e q with hq | hq
    · subst p q
      exact P.repeatedReservoir_offDiag_transport ν i j s hi hj hb hd e e' Z c L hij
    · exact (hpq (hp.trans hq.symm)).elim
  · cases e
    exact (hpq ((probePairMiddle_unique ν i j s hb hij p).trans
      (probePairMiddle_unique ν i j s hb hij q).symm)).elim
  · have e' : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) = t := by
      simpa only [nextSector, add_right_comm] using e
    exact P.repeatedOuter_oneReservoir_offDiag ν i j s hd c L hc h hij e' e p q Z hpq
  · exact (hpq (repeatedOuterPureProbe_path_eq ν i j e p q)).elim

/-- All three literal matrix fields of the Brundan–Ellis braid relation.
The proof dispatches arbitrary paths and derives the necessary sector witnesses;
no braid field or additional model assumption is supplied. -/
theorem crossBraidOfInputs (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) : CrossBraid (P.swappedGens c L) where
  braid := P.braid_nonRepeated c L hc h
  braidEq_offDiag := P.braid_repeated_offDiag c L hc h
  braidEq_diag := P.braid_repeated_diag c L hc h

/-- The assembled braid relation on the actual layer representation. -/
theorem braidRelationsOfInputs (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) {Gs Ys : ∀ s, P.H s} :
    BraidRelations Sc (P.layerRep Gs Ys (P.swappedGens c L)) :=
  P.braidRelations (P.crossBraidOfInputs c L hc h)

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
