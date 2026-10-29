import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.ProbePairSector

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
variable (ν : X) (i r : I) (s : Sector I) (hR : StepValid (true, r) false s)
variable (c : P.CrossCoeff Sc) (L : P.LeftwardData)
  (Z : P.H (nextSector (true, r) false (nextSector (true, i) true (nextSector (true, i) true s))))

/-- The literal reverse mixed entry on the left pair retains its Q factor. -/
theorem reverseProbePair_left_mixed (hir : i ≠ r) :
    crossEntry (P.swappedGens c L) ν [] r i [up i]
      (probePairTarget ν i r s hR) (probePairMiddle ν i r s hR) Z =
    (P.mixedJ i r s hR ((P.step (true, i) true _ trivial).obj Z)).inv ≫
      P.mixedQ i r s hR ((P.step (true, i) true _ trivial).obj Z) := by
  refine (crossEntry_left (P.swappedGens c L) ν r i i
    (.cons _ false s hR (.cons _ true _ trivial (.nil _)))
    (.cons _ true s trivial (.cons _ false _ hR (.nil _)))
    (.cons _ true _ trivial (.nil _)) Z).trans ?_
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  dsimp only [swappedGens]
  rw [P.crossImage_ne c hir.symm]
  rfl

/-- The literal reverse mixed entry on the right pair retains its Q factor. -/
theorem reverseProbePair_right_mixed (hir : i ≠ r) :
    crossEntry (P.swappedGens c L) ν [up i] r i []
      (probePairMiddle ν i r s hR) (probePairSource ν i r s hR) Z =
    (P.step (true, i) true s trivial).map
      ((P.mixedJ i r (nextSector (true, i) true s) hR Z).inv ≫
        P.mixedQ i r (nextSector (true, i) true s) hR Z) := by
  refine (crossEntry_right (P.swappedGens c L) ν i r i true trivial
    (.cons _ false _ hR (.cons _ true _ trivial (.nil _)))
    (.cons _ true _ trivial (.cons _ false _ hR (.nil _))) Z).trans ?_
  dsimp only [swappedGens]
  rw [P.crossImage_ne c hir.symm]
  rfl

/-- Exact reduction of the reverse sector braid; both Q factors remain literal. -/
theorem reverseProbePair_braid_iff (hir : i ≠ r) :
    braidLeft (P.swappedGens c L) r i i ν
      (probePairTarget ν i r s hR) (probePairSource ν i r s hR) Z =
    braidRight (P.swappedGens c L) r i i ν
      (probePairTarget ν i r s hR) (probePairSource ν i r s hR) Z ↔
    ((P.mixedJ i r s hR ((P.step (true, i) true _ trivial).obj Z)).inv ≫
      P.mixedQ i r s hR ((P.step (true, i) true _ trivial).obj Z)) ≫
      (P.step (true, i) true s trivial).map
        ((P.mixedJ i r (nextSector (true, i) true s) hR Z).inv ≫
          P.mixedQ i r (nextSector (true, i) true s) hR Z) ≫
      P.preCrossSame i s ((P.step (true, r) false
        (nextSector (true, i) true (nextSector (true, i) true s)) hR).obj Z) =
    (P.step (true, r) false s hR).map
        (P.preCrossSame i (nextSector (true, r) false s) Z) ≫
      ((P.mixedJ i r s hR ((P.step (true, i) true _ trivial).obj Z)).inv ≫
        P.mixedQ i r s hR ((P.step (true, i) true _ trivial).obj Z)) ≫
      (P.step (true, i) true s trivial).map
        ((P.mixedJ i r (nextSector (true, i) true s) hR Z).inv ≫
          P.mixedQ i r (nextSector (true, i) true s) hR Z) := by
  classical
  let : Subsingleton (SPath (wd D ν [up i, up i, up r]) s
      (nextSector (true, r) false (nextSector (true, i) true (nextSector (true, i) true s)))) :=
    ⟨fun p q => (probePairSource_unique ν i r s hR hir p).trans
      (probePairSource_unique ν i r s hR hir q).symm⟩
  let : Subsingleton (SPath (wd D ν [up i, up r, up i]) s
      (nextSector (true, r) false (nextSector (true, i) true (nextSector (true, i) true s)))) :=
    ⟨fun p q => (probePairMiddle_unique ν i r s hR hir p).trans
      (probePairMiddle_unique ν i r s hR hir q).symm⟩
  let : Subsingleton (SPath (wd D ν [up r, up i, up i]) s
      (nextSector (true, r) false (nextSector (true, i) true (nextSector (true, i) true s)))) :=
    ⟨fun p q => (probePairTarget_unique ν i r s hR hir p).trans
      (probePairTarget_unique ν i r s hR hir q).symm⟩
  let := Fintype.ofFinite (SPath (wd D ν [up i, up i, up r]) s
    (nextSector (true, r) false (nextSector (true, i) true (nextSector (true, i) true s))))
  let := Fintype.ofFinite (SPath (wd D ν [up i, up r, up i]) s
    (nextSector (true, r) false (nextSector (true, i) true (nextSector (true, i) true s))))
  let := Fintype.ofFinite (SPath (wd D ν [up r, up i, up i]) s
    (nextSector (true, r) false (nextSector (true, i) true (nextSector (true, i) true s))))
  unfold braidLeft braidRight
  rw [Fintype.sum_subsingleton _ (probePairSource (D := D) ν i r s hR),
    Fintype.sum_subsingleton _ (probePairMiddle (D := D) ν i r s hR),
    Fintype.sum_subsingleton _ (probePairMiddle (D := D) ν i r s hR),
    Fintype.sum_subsingleton _ (probePairTarget (D := D) ν i r s hR)]
  rw [reverseProbePair_left_mixed _ _ _ _ _ _ _ _ _ hir,
    reverseProbePair_right_mixed _ _ _ _ _ _ _ _ _ hir,
    probePair_left_same, probePair_right_same]
  simp only [Category.assoc]

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly

#print axioms OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir.reverseProbePair_braid_iff
