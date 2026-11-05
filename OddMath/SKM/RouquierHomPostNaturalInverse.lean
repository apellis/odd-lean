import OddMath.SKM.RouquierHomPostInverse

/-!
# Supernaturality of postcomposition inverse coordinates

The finite-window maps of `HomProbeMatrix.md` extend to homogeneous
supernatural transformations on the full probe supercategory. The even
coordinate isomorphisms preserve the specified content shifts, and the
homogeneous middle maps are the prescribed factor inverse entries.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r

section Coordinates
variable {k : Type r} [CommRing k] {C C' : Type*} [Category C] [Category C']
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive C'] [Linear k C'] [Supercategory k C']
  {F G H K : C ⥤ C'} [F.Additive] [G.Additive] [H.Additive] [K.Additive]
  [F.Linear k] [G.Linear k] [H.Linear k] [K.Linear k]

omit [F.Linear k] in

omit [F.Linear k] in

/-- Moving the source to its literal parity shift makes a homogeneous map even. -/
theorem IsSupernatural.shiftSource [IsSuperfunctor k F] [PiSupercategory k C'] {p : ZMod 2}
    {x : ∀ Z, F.obj Z ⟶ G.obj Z} (hx : IsSupernatural k p x) :
    IsSupernatural k 0 (F := F ⋙ homParityShift (k := k) p) (G := G)
      (fun Z => ((homParityShiftDatum (k := k) p).iso (F.obj Z)).hom ≫ x Z) := by
  have ht := ((homParityShiftDatum (k := k) p).supernatural.whiskerLeft F).comp hx
  rw [zmod2_add_self] at ht
  exact ht
end Coordinates

variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : X → B) (W : RouquierFamily (k := k) (B := B) D)
  (i : I) (betaP : I →₀ ℕ) (muP : X) {muM nuM rhoM : X}
  (h : muM + D.α i = nuM) (h₂ : nuM + D.α i = rhoM)

/-- Powers of the specified dot are homogeneous supernatural transformations. -/
theorem homContentPostDot_power_supernatural (n : ℕ) :
    IsSupernatural k (n * D.parity i)
      (F := homContentPostE T W i betaP muP h)
      (G := homContentPostE T W i betaP muP h)
      (fun Z => homContentPostDot T W i betaP muP h Z ^ n) := by
  have hx := ((homPostTransform (k := k) (a := T (-muP))
    (rouquierPower (W.dot i h) n) (rouquierPower_mem (W.dot_mem i h) n)).isSupernatural
      (n * D.parity i)).whiskerRight (homParityShift (k := k) (homContentShift D i betaP))
  simpa only [homPostTransform, ite_true, homContentPostDot_power] using hx

/-- Dotted units use the same specified adjunction, not an output-shift replacement. -/
theorem homContentPostCup_supernatural (n : ℕ) :
    IsSupernatural k (n * D.parity i)
      (F := 𝟭 (homWeightSector T W.obj muP muM))
      (G := homContentPostE T W i betaP muP h ⋙ homContentPostF T W i betaP muP h)
      (homContentPostCup T W i betaP muP h n) := by
  have hx := (homContentPostDot_power_supernatural T W i betaP muP h n).whiskerRight
    (homContentPostF T W i betaP muP h)
  have hc := isSupernatural_of_natTrans (homContentPostAdjunction T W i betaP muP h).unit
    (homContentPostAdjunction_unit_mem T W i betaP muP h)
  have ht := hc.comp hx
  rw [zero_add] at ht
  exact ht

end OddMath.SKM
