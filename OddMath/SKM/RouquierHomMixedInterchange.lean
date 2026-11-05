import OddMath.SKM.RouquierHomPostPowers

/-!
# Content-shifted mixed Hom interchange

The prescribed comparison J in `HomSwappingMates.md` §1 (1), used in
`SwappedHomInversion.md` §3 (2), is built from the two homogeneous shift
removals and the pre/post associator. The dot transport below is derived
from super-interchange, not supplied as a mixed-crossing relation.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {a b c d : B}

/-- First remove the source shift, reassociate, then insert the target shift.
The two removals are homogeneous comparisons, not even identifications. -/
def homMixedInterchange (E : a ⟶ b) (F : c ⟶ d) (κ τ : ZMod 2) (Z : b ⟶ c) :
    E ≫ (homParityShift (k := k) κ).obj (Z ≫ F) ≅
      (homParityShift (k := k) τ).obj ((E ≫ Z) ≫ F) :=
  (homPre (k := k) E).mapIso ((homParityShiftDatum (k := k) κ).iso (Z ≫ F)) ≪≫
    (associator E Z F).symm ≪≫
      ((homParityShiftDatum (k := k) τ).iso ((E ≫ Z) ≫ F)).symm

/-- J has the sum of the two shift parities. -/
theorem homMixedInterchange_mem (E : a ⟶ b) (F : c ⟶ d) (κ τ : ZMod 2)
    (Z : b ⟶ c) :
    (homMixedInterchange (k := k) E F κ τ Z).hom ∈ parity (R := k) _ _ (κ + τ) := by
  simp only [homMixedInterchange, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, homPre]
  apply comp_mem
  · exact TwoSupercategory.whiskerLeft_mem E ((homParityShiftDatum (k := k) κ).hom_mem _)
  · simpa only [zero_add] using comp_mem
      (inv_mem _ (TwoSupercategory.associator_hom_mem (R := k) E Z F))
      ((homParityShiftDatum (k := k) τ).inv_mem _)

/-- Transport of the precomposition dot through the prescribed J. -/
theorem homMixedInterchange_pre (E : a ⟶ b) (F : c ⟶ d) (κ τ : ZMod 2)
    (Z : b ⟶ c) {s : ZMod 2} (x : E ⟶ E) (hx : x ∈ parity (R := k) _ _ s) :
    x ▷ (homParityShift (k := k) κ).obj (Z ≫ F) ≫
        (homMixedInterchange (k := k) E F κ τ Z).hom =
      koszulSign (κ + τ) s • ((homMixedInterchange (k := k) E F κ τ Z).hom ≫
        (homParityShift (k := k) τ).map ((x ▷ Z) ▷ F)) := by
  simp only [homMixedInterchange, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    homPre, Category.assoc]
  rw [← Category.assoc, TwoSupercategory.super_interchange hx
    ((homParityShiftDatum (k := k) κ).hom_mem _)]
  rw [Preadditive.zsmul_comp, Category.assoc,
    TwoSupercategory.associator_inv_naturality_left_assoc (R := k)]
  rw [(homParityShiftDatum (k := k) τ).inv_naturality
    (TwoSupercategory.whiskerRight_mem F (TwoSupercategory.whiskerRight_mem Z hx))]
  rw [← koszulSign_smul (R := k), Preadditive.comp_zsmul, Preadditive.comp_zsmul,
    smul_smul, koszulSign_add_left, koszulSign_comm s κ]

/-- Transport of the shifted postcomposition dot through the same J. -/
theorem homMixedInterchange_post (E : a ⟶ b) (F : c ⟶ d) (κ τ : ZMod 2)
    (Z : b ⟶ c) {s : ZMod 2} (y : F ⟶ F) (hy : y ∈ parity (R := k) _ _ s) :
    E ◁ (homParityShift (k := k) κ).map (Z ◁ y) ≫
        (homMixedInterchange (k := k) E F κ τ Z).hom =
      koszulSign (κ + τ) s • ((homMixedInterchange (k := k) E F κ τ Z).hom ≫
        (homParityShift (k := k) τ).map ((E ≫ Z) ◁ y)) := by
  simp only [homMixedInterchange, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    homPre, Category.assoc]
  rw [← Category.assoc, ← TwoSupercategory.whiskerLeft_comp (R := k),
    (homParityShiftDatum (k := k) κ).hom_naturality (TwoSupercategory.whiskerLeft_mem Z hy),
    TwoSupercategory.whiskerLeft_smul, TwoSupercategory.whiskerLeft_comp (R := k),
    Linear.smul_comp]
  rw [Category.assoc, TwoSupercategory.associator_inv_naturality_right_assoc (R := k),
    (homParityShiftDatum (k := k) τ).inv_naturality
      (TwoSupercategory.whiskerLeft_mem (E ≫ Z) hy)]
  rw [← koszulSign_smul (R := k), ← koszulSign_smul (R := k),
    Preadditive.comp_zsmul, Preadditive.comp_zsmul, smul_smul, koszulSign_add_left]

/-- The two transported dots satisfy the Koszul exchange on the AB object. -/
theorem homMixedInterchange_dot_exchange (E : a ⟶ b) (F : c ⟶ d)
    (τ : ZMod 2) (Z : b ⟶ c) {s t : ZMod 2}
    (x : E ⟶ E) (y : F ⟶ F)
    (hx : x ∈ parity (R := k) _ _ s) (hy : y ∈ parity (R := k) _ _ t) :
    (homParityShift (k := k) τ).map ((x ▷ Z) ▷ F) ≫
        (homParityShift (k := k) τ).map ((E ≫ Z) ◁ y) =
      koszulSign s t • ((homParityShift (k := k) τ).map ((E ≫ Z) ◁ y) ≫
        (homParityShift (k := k) τ).map ((x ▷ Z) ▷ F)) := by
  rw [← Functor.map_comp,
    TwoSupercategory.super_interchange (TwoSupercategory.whiskerRight_mem Z hx) hy,
    Functor.map_zsmul, Functor.map_comp]

section Factors
variable {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T W : RouquierFamily (k := k) (B := B) D) (i : I) (β : I →₀ ℕ)
  {muP nuP muM nuM : X}
  (hT : -nuP + D.α i = -muP) (hW : muM + D.α i = nuM)

/-- J on the supplied factor families, with the actual two content labels. -/
def homContentMixedInterchange (Z : homWeightSector T.obj W.obj muP muM) :
    (homContentPreE T W.obj i nuM hT).obj
        ((homContentPostE T.obj W i β muP hW).obj Z) ≅
      (homContentPostE T.obj W i (β + Finsupp.single i 1) nuP hW).obj
        ((homContentPreE T W.obj i muM hT).obj Z) :=
  homMixedInterchange (k := k) (T.E i hT) (W.E i hW)
    (homContentShift D i β) (homContentShift D i (β + Finsupp.single i 1)) Z

/-- The prescribed negative swapping coefficient, parametrized by the AB
coefficient a. This is not a definition of a or of its finite expansion. -/
def homContentMixedSwap (Z : homWeightSector T.obj W.obj muP muM)
    (a : End ((homContentPostE T.obj W i (β + Finsupp.single i 1) nuP hW).obj
      ((homContentPreE T W.obj i muM hT).obj Z))) :=
  -(a ≫ a ≫ (homContentMixedInterchange T W i β hT hW Z).inv)

end Factors
end OddMath.SKM
