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

/-- Natural source coordinate with the specified two-shift removal. -/
def homContentPostInverseSourceNatIso :
    homContentPostF T W i betaP muP h ⋙ homContentPostE T W i betaP muP h ≅
      homPost (k := k) (a := T (-muP)) (W.F i h ≫ W.E i h) :=
  homShiftConjugationNatIso (homPost (k := k) (W.F i h) ⋙ homPost (k := k) (W.E i h))
    (homContentShift D i betaP) ≪≫ homPostComp (W.F i h) (W.E i h)

/-- Natural target coordinate retains the adjacent shift-square comparison. -/
def homContentPostInverseTargetNatIso :
    homContentPostE T W i betaP muP h ⋙ homContentPostF T W i betaP muP h ≅
      homPost (k := k) (a := T (-muP)) (W.E i h ≫ W.F i h) :=
  Functor.isoWhiskerLeft (homPost (k := k) (W.E i h))
    (Functor.isoWhiskerRight (homParityShiftSquare (k := k) (homContentShift D i betaP))
      (homPost (k := k) (W.F i h))) ≪≫ homPostComp (W.E i h) (W.F i h)

@[simp] theorem homContentPostInverseSourceNatIso_app (Z : homWeightSector T W.obj muP nuM) :
    (homContentPostInverseSourceNatIso T W i betaP muP h).app Z =
      homContentPostInverseSource T W i betaP muP h Z := by
  apply Iso.ext
  simp [homContentPostInverseSourceNatIso, homContentPostInverseSource,
    homContentPostSourceIso, homShiftConjugationNatIso_hom_app, homPostComp, homPost]

@[simp] theorem homContentPostInverseTargetNatIso_app (Z : homWeightSector T W.obj muP muM) :
    (homContentPostInverseTargetNatIso T W i betaP muP h).app Z =
      homContentPostInverseTarget T W i betaP muP h Z := by
  apply Iso.ext
  rfl

@[simp] theorem homContentPostInverseSourceNatIso_hom_app
    (Z : homWeightSector T W.obj muP nuM) :
    (homContentPostInverseSourceNatIso T W i betaP muP h).hom.app Z =
      (homContentPostInverseSource T W i betaP muP h Z).hom :=
  congrArg Iso.hom (homContentPostInverseSourceNatIso_app T W i betaP muP h Z)

@[simp] theorem homContentPostInverseSourceNatIso_inv_app
    (Z : homWeightSector T W.obj muP nuM) :
    (homContentPostInverseSourceNatIso T W i betaP muP h).inv.app Z =
      (homContentPostInverseSource T W i betaP muP h Z).inv :=
  congrArg Iso.inv (homContentPostInverseSourceNatIso_app T W i betaP muP h Z)

@[simp] theorem homContentPostInverseTargetNatIso_hom_app
    (Z : homWeightSector T W.obj muP muM) :
    (homContentPostInverseTargetNatIso T W i betaP muP h).hom.app Z =
      (homContentPostInverseTarget T W i betaP muP h Z).hom :=
  congrArg Iso.hom (homContentPostInverseTargetNatIso_app T W i betaP muP h Z)

@[simp] theorem homContentPostInverseTargetNatIso_inv_app
    (Z : homWeightSector T W.obj muP muM) :
    (homContentPostInverseTargetNatIso T W i betaP muP h).inv.app Z =
      (homContentPostInverseTarget T W i betaP muP h Z).inv :=
  congrArg Iso.inv (homContentPostInverseTargetNatIso_app T W i betaP muP h Z)

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
