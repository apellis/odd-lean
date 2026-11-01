/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentReservoirReverseBlock
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentPureProbe
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentPureReservoir
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentSplitBraid
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.AdjacentReverseBraid
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.ReverseReservoirSector
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.QWeightedReverseSector
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.PairwiseDistinct
import OddMath.QuiverHecke.SwappedAssembly.BraidSame.AllPaths

/-! Global structural assembly of the non-correction CrossBraid field. -/
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

lemma braid_adjacent_iij (ν : X) (i j : I) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) {s t : Sector I}
    (p : SPath (wd D ν [up i, up i, up j]) s t)
    (q : SPath (wd D ν [up j, up i, up i]) s t) (Z : P.H t) :
    braidLeft (P.swappedGens c L) i i j ν p q Z =
      braidRight (P.swappedGens c L) i i j ν p q Z := by
  obtain ⟨a, b, d, ha, hb, hd, e, _⟩ := SPath.exists_eq_three p
  cases a <;> cases b <;> cases d
  · exact P.adjacentPureReservoir_iij ν i j c L hij (by rw [← e]; rfl) p q Z
  · cases e
    rw [reservoirPairTarget_unique ν j i s ha hb hij.symm p,
      reservoirPairSource_unique ν j i s ha hb hij.symm q]
    exact P.reverseReservoirPair_braid ν j i s ha hb c L Z hij.symm
  · exact AdjacentReservoirSquareBlock.braid_block P i j s ha hd ν e Z p q c L hc h hij
  · have et : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) = t := by
      simpa only [nextSector, add_right_comm] using e
    cases et
    exact P.adjacentSplit_braid ν i j s ha c L hc h hij p q Z
  · exact AdjacentReservoirSquareBlock.braid_block P i j s hb hd ν e Z p q c L hc h hij
  · have et : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) = t := by
      simpa only [nextSector, add_right_comm] using e
    cases et
    exact P.adjacentSplit_braid ν i j s hb c L hc h hij p q Z
  · cases e
    rw [probePairSource_unique ν i j s hd hij p, probePairTarget_unique ν i j s hd hij q]
    exact P.probePair_braid ν i j s hd c L Z hij
  · exact P.adjacentPureProbe_iij ν i j s c L hij e p q Z

lemma braid_adjacent_jii (ν : X) (i j : I) (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs) (hij : i ≠ j) {s t : Sector I}
    (p : SPath (wd D ν [up j, up i, up i]) s t)
    (q : SPath (wd D ν [up i, up i, up j]) s t) (Z : P.H t) :
    braidLeft (P.swappedGens c L) j i i ν p q Z =
      braidRight (P.swappedGens c L) j i i ν p q Z := by
  obtain ⟨a, b, d, ha, hb, hd, e, _⟩ := SPath.exists_eq_three p
  cases a <;> cases b <;> cases d
  · exact P.adjacentPureReservoir_ijj ν j i c L hij.symm (by rw [← e]; rfl) p q Z
  · exact AdjacentReservoirReverseBlock.braid_block P i j s ha hb ν e Z p q c L hc h hij
  · exact AdjacentReservoirReverseBlock.braid_block P i j s ha hd ν e Z p q c L hc h hij
  · cases e
    rw [probePairTarget_unique ν i j s ha hij p, probePairSource_unique ν i j s ha hij q]
    exact P.reverseProbePair_braid ν i j s ha c L Z hij
  · cases e
    rw [reservoirPairSource_unique ν j i s hb hd hij.symm p,
      reservoirPairTarget_unique ν j i s hb hd hij.symm q]
    exact P.reservoirPair_braid ν j i s hb hd c L Z hij.symm
  · have et : nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)) = t := by
      simpa only [nextSector, add_right_comm] using e
    cases et
    exact P.adjacentReverse_braid ν i j s hb c L hc h hij p q Z
  · have et : nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)) = t := by
      simpa only [nextSector, add_right_comm] using e
    cases et
    exact P.adjacentReverse_braid ν i j s hd c L hc h hij p q Z
  · exact P.adjacentPureProbe_ijj ν j i s c L hij.symm e p q Z

/-- The entire non-correction field of CrossBraid, for arbitrary colours,
sectors, and paths. -/
lemma braid_nonRepeated (c : P.CrossCoeff Sc) (L : P.LeftwardData)
    (hc : c.IsInverse) (h : P.CrossCoeffInputs)
    (i j r : I) (ν : X) (hn : ¬(i = r ∧ i ≠ j)) {s t : Sector I}
    (p : SPath (wd D ν [up i, up j, up r]) s t)
    (q : SPath (wd D ν [up r, up j, up i]) s t) (Z : P.H t) :
    braidLeft (P.swappedGens c L) i j r ν p q Z =
      braidRight (P.swappedGens c L) i j r ν p q Z := by
  by_cases hij : i = j
  · subst j
    by_cases hir : i = r
    · subst r
      exact braid_same c L ν i hc h p q Z
    · exact P.braid_adjacent_iij ν i r c L hc h hir p q Z
  · have hir : i ≠ r := fun he => hn ⟨he, hij⟩
    by_cases hjr : j = r
    · subst r
      exact P.braid_adjacent_jii ν j i c L hc h (Ne.symm hij) p q Z
    · exact P.braid_pairwiseDistinct ν i j r c L hij hir hjr p q Z

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
