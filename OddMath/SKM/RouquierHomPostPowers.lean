import OddMath.SKM.RouquierHomPostPrincipal
import OddMath.SKM.RouquierMateSectors

/-!
# Dotted content-shifted postcomposition coordinates

The natural-power identities of `HomProbeMatrix.md` §3 (9) give the dotted
finite-window entries beyond the principal mate comparison. The dot is the
shifted postcomposition of the factor dot, and the cup and cap use the
specified adjunction. No inverse dot or transposed-dot normalization is used.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r

private theorem map_end_pow {C : Type*} {C' : Type*} [Category C] [Category C']
    (F : C ⥤ C') {Z : C} (d : End Z) (n : ℕ) :
    (show End (F.obj Z) from F.map d) ^ n = F.map (d ^ n) := by
  induction n with
  | zero => exact (F.map_id Z).symm
  | succ n ih => rw [pow_succ', pow_succ', End.mul_def, End.mul_def, ih, F.map_comp]

variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : X → B) (W : RouquierFamily (k := k) (B := B) D)
  (i : I) (betaP : I →₀ ℕ) (muP : X) {muM nuM : X} (h : muM + D.α i = nuM)

/-- The prescribed dot is the parity-shift functor applied to the postcomposition dot. -/
def homContentPostDot (Z : homWeightSector T W.obj muP muM) :
    End ((homContentPostE T W i betaP muP h).obj Z) :=
  (homParityShift (k := k) (homContentShift D i betaP)).map (Z ◁ W.dot i h)

/-- Functoriality preserves every ordered natural power, with no transpose sign. -/
theorem homContentPostDot_power (n : ℕ) (Z : homWeightSector T W.obj muP muM) :
    homContentPostDot T W i betaP muP h Z ^ n =
      (homParityShift (k := k) (homContentShift D i betaP)).map
        (Z ◁ rouquierPower (W.dot i h) n) := by
  rw [homContentPostDot, map_end_pow, whiskerLeft_rouquierPower (k := k)]

/-- Dotted unit of the specified content-shifted postcomposition adjunction. -/
def homContentPostCup (n : ℕ) (Z : homWeightSector T W.obj muP muM) :
    Z ⟶ (homContentPostF T W i betaP muP h).obj
      ((homContentPostE T W i betaP muP h).obj Z) :=
  (homContentPostAdjunction T W i betaP muP h).unit.app Z ≫
    (homContentPostF T W i betaP muP h).map (homContentPostDot T W i betaP muP h Z ^ n)

/-- Dotted counit of the same specified adjunction, with the shift on the right-adjoint input. -/
def homContentPostCap (n : ℕ) (Z : homWeightSector T W.obj muP nuM) :
    (homContentPostE T W i betaP muP h).obj
      ((homContentPostF T W i betaP muP h).obj Z) ⟶ Z :=
  (homContentPostDot T W i betaP muP h ((homContentPostF T W i betaP muP h).obj Z) ^ n) ≫
    (homContentPostAdjunction T W i betaP muP h).counit.app Z

/-- Removing the output coordinate of the dotted unit leaves the literal factor unit word. -/
theorem homContentPostCup_coordinates (n : ℕ) (Z : homWeightSector T W.obj muP muM) :
    homContentPostCup T W i betaP muP h n Z ≫
      (homContentPostTargetIso T W i betaP muP h Z).hom =
    (rightUnitor Z).inv ≫ Z ◁ (W.adj i h).unit ≫
      (associator Z (W.E i h) (W.F i h)).inv ≫
      (Z ◁ rouquierPower (W.dot i h) n) ▷ W.F i h := by
  rw [homContentPostCup, homContentPostAdjunction_unit_coordinates, homContentPostDot_power]
  have hn := (homParityShiftSquare (k := k) (homContentShift D i betaP)).hom.naturality
    (Z ◁ rouquierPower (W.dot i h) n)
  change (homParityShift (k := k) (homContentShift D i betaP)).map
      ((homParityShift (k := k) (homContentShift D i betaP)).map
        (Z ◁ rouquierPower (W.dot i h) n)) ≫ _ = _ at hn
  simp only [Category.assoc]
  change (homPostUnit (W.adj i h)).app Z ≫
    (homPost (k := k) (W.F i h)).map
      ((homParityShiftSquare (k := k) (homContentShift D i betaP)).inv.app _) ≫
    (homPost (k := k) (W.F i h)).map
      ((homParityShift (k := k) (homContentShift D i betaP)).map
        ((homParityShift (k := k) (homContentShift D i betaP)).map
          (Z ◁ rouquierPower (W.dot i h) n))) ≫
    (homPost (k := k) (W.F i h)).map
      ((homParityShiftSquare (k := k) (homContentShift D i betaP)).hom.app _) = _
  rw [← Functor.map_comp, hn, Functor.map_comp]
  simp only [← Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
  simp [homPostUnit, homPostId, homPostComp, homPostTransform,
    SuperNatTrans.toNatTrans, homPost, Category.assoc]

/-- Removing the input coordinate of the dotted counit cancels both homogeneous signs. -/
theorem homContentPostCap_coordinates (n : ℕ) (Z : homWeightSector T W.obj muP nuM) :
    homContentPostCap T W i betaP muP h n Z =
    (homContentPostSourceIso T W i betaP muP h Z).hom ≫
      (Z ≫ W.F i h) ◁ rouquierPower (W.dot i h) n ≫
      (associator Z (W.F i h) (W.E i h)).hom ≫
      Z ◁ (W.adj i h).counit ≫ (rightUnitor Z).hom := by
  rw [homContentPostCap, homContentPostDot_power, homContentPostAdjunction_counit_coordinates]
  have ht := ((homPostTransform (k := k) (a := T (-muP))
    (rouquierPower (W.dot i h) n) (rouquierPower_mem (W.dot_mem i h) n)).isSupernatural
      ((n : ZMod 2) * D.parity i)).whiskerLeft (homPost (k := k) (W.F i h))
  have hc := homShiftConjugationIso_supernatural
    (homPost (k := k) (W.F i h) ⋙ homPost (k := k) (W.E i h))
    (homPost (k := k) (W.F i h) ⋙ homPost (k := k) (W.E i h))
    (homContentShift D i betaP) ((n : ZMod 2) * D.parity i) _ ht Z
  simp only [homPostTransform, ite_eq_left, homPost] at hc
  dsimp only [homContentPostSourceIso, homContentPostF, Functor.comp_obj, homPost]
  rw [← Category.assoc, hc]
  simp [homPostCounit, homPostId, homPostComp,
    homPostTransform, SuperNatTrans.toNatTrans, homPost, Category.assoc]

end OddMath.SKM
