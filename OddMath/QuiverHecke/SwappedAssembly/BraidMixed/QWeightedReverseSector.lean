/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.ProbePairQCentrality

/-! The reverse Q-weighted two-probe sector braid, retaining both mixed Q factors.
This closes the reverse direction of the two-probe case in MixedColourRemainingBraid §2.
No Q polynomial is inverted. -/

open CategoryTheory
namespace ReverseWeightedPair
variable {C : Type*} [Category C] {A B D : C}

/-- Transport a commuting two-factor weight along a pair of isomorphisms. -/
theorem transport (f : A ≅ B) (g : B ≅ D)
    (ψ : A ⟶ A) (χ : D ⟶ D) (Q : B ⟶ B) (R : A ⟶ A)
    (htri : ψ ≫ f.hom ≫ g.hom = f.hom ≫ g.hom ≫ χ)
    (hcentral : (f.hom ≫ Q ≫ f.inv) ≫ R ≫ ψ = ψ ≫ (f.hom ≫ Q ≫ f.inv) ≫ R) :
    (g.inv ≫ Q) ≫ (f.inv ≫ R) ≫ ψ = χ ≫ (g.inv ≫ Q) ≫ (f.inv ≫ R) := by
  apply (cancel_epi (f.hom ≫ g.hom)).1
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  calc
    f.hom ≫ Q ≫ f.inv ≫ R ≫ ψ = ψ ≫ f.hom ≫ Q ≫ f.inv ≫ R := by
      simpa only [Category.assoc] using hcentral
    _ = (ψ ≫ f.hom ≫ g.hom) ≫ g.inv ≫ Q ≫ f.inv ≫ R := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = (f.hom ≫ g.hom ≫ χ) ≫ g.inv ≫ Q ≫ f.inv ≫ R := by rw [htri]
    _ = _ := by simp only [Category.assoc]
theorem reassociate (f : D ⟶ B) (g : B ⟶ A) (ψ : A ⟶ A) (χ : D ⟶ D) :
    ((f ≫ g) ≫ ψ = (χ ≫ f) ≫ g) ↔ (f ≫ g ≫ ψ = χ ≫ f ≫ g) := by
  simp only [Category.assoc]
end ReverseWeightedPair

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
  change 𝟙 _ ≫ P.crossImage c r i (SKM.wt D ν [up i])
    (.cons _ false s hR (.cons _ true _ trivial (.nil _)))
    (.cons _ true s trivial (.cons _ false _ hR (.nil _)))
    ((P.step (true, i) true _ trivial).obj Z) ≫ 𝟙 _ = _
  simp only [Category.id_comp, Category.comp_id]
  exact P.crossImage_ne c (Ne.symm hir) _ _ _ _

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
  change (P.step (true, i) true s trivial).map
    (P.crossImage c r i ν
      (.cons _ false (nextSector (true, i) true s) hR (.cons _ true _ trivial (.nil _)))
      (.cons _ true (nextSector (true, i) true s) trivial (.cons _ false _ hR (.nil _))) Z) = _
  exact congrArg (P.step (true, i) true s trivial).map
    (P.crossImage_ne c (Ne.symm hir) ν _ _ Z)

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
  exact ReverseWeightedPair.reassociate _ _ _ _

/-- The reverse two-probe sector braid, with its prescribed Q-weighted mixed entries.
The crossing coefficients and leftward data are arbitrary; no inverse-coefficient
or Q-invertibility assumption is required. -/
theorem reverseProbePair_braid (hir : i ≠ r) :
    braidLeft (P.swappedGens c L) r i i ν
      (probePairTarget ν i r s hR) (probePairSource ν i r s hR) Z =
    braidRight (P.swappedGens c L) r i i ν
      (probePairTarget ν i r s hR) (probePairSource ν i r s hR) Z := by
  apply (reverseProbePair_braid_iff P ν i r s hR c L Z hir).2
  let f := P.probePairFirstIso i r s hR Z
  let g := P.mixedJ i r s hR ((P.step (true, i) true _ trivial).obj Z)
  let Q := P.mixedQ i r s hR ((P.step (true, i) true _ trivial).obj Z)
  let U := (P.mixedJ i r (nextSector (true, i) true s) hR Z).inv ≫
    P.mixedQ i r (nextSector (true, i) true s) hR Z
  let ψ := P.preCrossSame i s ((P.step (true, r) false
    (nextSector (true, i) true (nextSector (true, i) true s)) hR).obj Z)
  let χ := (P.step (true, r) false s hR).map
    (P.preCrossSame i (nextSector (true, r) false s) Z)
  change (g.inv ≫ Q) ≫ (P.step (true, i) true s trivial).map U ≫ ψ =
    χ ≫ (g.inv ≫ Q) ≫ (P.step (true, i) true s trivial).map U
  have h : (g.inv ≫ Q) ≫ (f.inv ≫ (P.step (true, i) true s trivial).map
      (P.mixedQ i r (nextSector (true, i) true s) hR Z)) ≫ ψ =
    χ ≫ (g.inv ≫ Q) ≫ (f.inv ≫ (P.step (true, i) true s trivial).map
      (P.mixedQ i r (nextSector (true, i) true s) hR Z)) := ReverseWeightedPair.transport
    (P.probePairFirstIso i r s hR Z)
    (P.mixedJ i r s hR ((P.step (true, i) true _ trivial).obj Z))
    (P.preCrossSame i s ((P.step (true, r) false
      (nextSector (true, i) true (nextSector (true, i) true s)) hR).obj Z))
    ((P.step (true, r) false s hR).map
      (P.preCrossSame i (nextSector (true, r) false s) Z))
    (P.mixedQ i r s hR ((P.step (true, i) true _ trivial).obj Z))
    ((P.step (true, i) true s trivial).map
      (P.mixedQ i r (nextSector (true, i) true s) hR Z))
    (P.preCrossSame_mixedJ_pair_ne i r s hR Z)
    (by simpa only [Commute, SemiconjBy, End.mul_def, Category.assoc] using
      probePairQProduct_central Sc P i r s hR Z)
  simpa only [f, U, probePairFirstIso, Functor.mapIso_inv, Functor.map_comp] using h

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
