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

/-- Both inverse products are literal adjacent cancellations. -/
theorem homMixedInterchange_products (E : a ⟶ b) (F : c ⟶ d) (κ τ : ZMod 2)
    (Z : b ⟶ c) :
    (homMixedInterchange (k := k) E F κ τ Z).hom ≫ (homMixedInterchange (k := k) E F κ τ Z).inv = 𝟙 _ ∧
    (homMixedInterchange (k := k) E F κ τ Z).inv ≫ (homMixedInterchange (k := k) E F κ τ Z).hom = 𝟙 _ :=
  ⟨(homMixedInterchange (k := k) E F κ τ Z).hom_inv_id,
    (homMixedInterchange (k := k) E F κ τ Z).inv_hom_id⟩

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

private theorem mixedContentParity :
    homContentShift D i β + homContentShift D i (β + Finsupp.single i 1) = D.parity i := by
  rw [homContentShift_add_single, ← add_assoc, zmod2_add_self, zero_add]
  rcases parity_eq_zero_or_one (D.parity i) with hp | hp <;> simp only [hp] <;> rfl

/-- J on the supplied factor families, with the actual two content labels. -/
def homContentMixedInterchange (Z : homWeightSector T.obj W.obj muP muM) :
    (homContentPreE T W.obj i nuM hT).obj
        ((homContentPostE T.obj W i β muP hW).obj Z) ≅
      (homContentPostE T.obj W i (β + Finsupp.single i 1) nuP hW).obj
        ((homContentPreE T W.obj i muM hT).obj Z) :=
  homMixedInterchange (k := k) (T.E i hT) (W.E i hW)
    (homContentShift D i β) (homContentShift D i (β + Finsupp.single i 1)) Z

/-- The prescribed mixed interchange has colour parity, at every weight. -/
theorem homContentMixedInterchange_mem (Z : homWeightSector T.obj W.obj muP muM) :
    (homContentMixedInterchange T W i β hT hW Z).hom ∈ parity (R := k) _ _ (D.parity i) := by
  have ht := homMixedInterchange_mem (k := k)
    (T.E i hT) (W.E i hW) (homContentShift D i β)
      (homContentShift D i (β + Finsupp.single i 1)) Z
  rw [mixedContentParity (D := D) i β] at ht
  exact ht

/-- The pre dot picks up q through J; no dot-slide premise is added. -/
theorem homContentMixedInterchange_pre (Z : homWeightSector T.obj W.obj muP muM) :
    T.dot i hT ▷ (homContentPostE T.obj W i β muP hW).obj Z ≫
        (homContentMixedInterchange T W i β hT hW Z).hom =
      koszulSign (D.parity i) (D.parity i) •
        ((homContentMixedInterchange T W i β hT hW Z).hom ≫
          (homContentPostE T.obj W i (β + Finsupp.single i 1) nuP hW).map
            (T.dot i hT ▷ Z)) := by
  have ht := homMixedInterchange_pre (k := k)
    (T.E i hT) (W.E i hW) (homContentShift D i β)
      (homContentShift D i (β + Finsupp.single i 1)) Z (T.dot i hT) (T.dot_mem i hT)
  rw [mixedContentParity (D := D) i β] at ht
  exact ht

/-- The reservoir post dot picks up the same q, with its specified shift action. -/
theorem homContentMixedInterchange_post (Z : homWeightSector T.obj W.obj muP muM) :
    (homContentPreE T W.obj i nuM hT).map (homContentPostDot T.obj W i β muP hW Z) ≫
        (homContentMixedInterchange T W i β hT hW Z).hom =
      koszulSign (D.parity i) (D.parity i) •
        ((homContentMixedInterchange T W i β hT hW Z).hom ≫
          homContentPostDot T.obj W i (β + Finsupp.single i 1) nuP hW (T.E i hT ≫ Z)) := by
  have ht := homMixedInterchange_post (k := k)
    (T.E i hT) (W.E i hW) (homContentShift D i β)
      (homContentShift D i (β + Finsupp.single i 1)) Z (W.dot i hW) (W.dot_mem i hW)
  rw [mixedContentParity (D := D) i β] at ht
  exact ht

/-- Koszul commutation of the actual shifted pre and post dots on AB. -/
theorem homContentMixedDot_exchange (Z : homWeightSector T.obj W.obj muP muM) :
    (homContentPostE T.obj W i (β + Finsupp.single i 1) nuP hW).map (T.dot i hT ▷ Z) ≫
        homContentPostDot T.obj W i (β + Finsupp.single i 1) nuP hW (T.E i hT ≫ Z) =
      koszulSign (D.parity i) (D.parity i) •
        (homContentPostDot T.obj W i (β + Finsupp.single i 1) nuP hW (T.E i hT ≫ Z) ≫
          (homContentPostE T.obj W i (β + Finsupp.single i 1) nuP hW).map (T.dot i hT ▷ Z)) :=
  homMixedInterchange_dot_exchange (k := k) (T.E i hT) (W.E i hW)
    (homContentShift D i (β + Finsupp.single i 1)) Z
      (T.dot i hT) (W.dot i hW) (T.dot_mem i hT) (W.dot_mem i hW)

/-- Even pre-dot squares cross J without a residual sign. -/
theorem homContentMixedInterchange_pre_square (Z : homWeightSector T.obj W.obj muP muM) :
    rouquierPower (T.dot i hT) 2 ▷ (homContentPostE T.obj W i β muP hW).obj Z ≫
        (homContentMixedInterchange T W i β hT hW Z).hom =
      (homContentMixedInterchange T W i β hT hW Z).hom ≫
        (homContentPostE T.obj W i (β + Finsupp.single i 1) nuP hW).map
          (rouquierPower (T.dot i hT) 2 ▷ Z) := by
  have ht := homMixedInterchange_pre (k := k)
    (T.E i hT) (W.E i hW) (homContentShift D i β)
      (homContentShift D i (β + Finsupp.single i 1)) Z
        (rouquierPower (T.dot i hT) 2) (rouquierPower_mem (T.dot_mem i hT) 2)
  have htwo : (2 : ZMod 2) = 0 := by decide
  simp only [Nat.cast_ofNat, htwo, zero_mul, koszulSign_zero_right, one_smul] at ht
  exact ht

/-- Even reservoir-dot squares cross J without a residual sign. -/
theorem homContentMixedInterchange_post_square (Z : homWeightSector T.obj W.obj muP muM) :
    (homContentPreE T W.obj i nuM hT).map
        ((homParityShift (k := k) (homContentShift D i β)).map
          (Z ◁ rouquierPower (W.dot i hW) 2)) ≫
        (homContentMixedInterchange T W i β hT hW Z).hom =
      (homContentMixedInterchange T W i β hT hW Z).hom ≫
        (homParityShift (k := k) (homContentShift D i (β + Finsupp.single i 1))).map
          ((T.E i hT ≫ Z) ◁ rouquierPower (W.dot i hW) 2) := by
  have ht := homMixedInterchange_post (k := k)
    (T.E i hT) (W.E i hW) (homContentShift D i β)
      (homContentShift D i (β + Finsupp.single i 1)) Z
        (rouquierPower (W.dot i hW) 2) (rouquierPower_mem (W.dot_mem i hW) 2)
  have htwo : (2 : ZMod 2) = 0 := by decide
  simp only [Nat.cast_ofNat, htwo, zero_mul, koszulSign_zero_right, one_smul] at ht
  exact ht

/-- The prescribed negative swapping coefficient, parametrized by the AB
coefficient a. This is not a definition of a or of its finite expansion. -/
def homContentMixedSwap (Z : homWeightSector T.obj W.obj muP muM)
    (a : End ((homContentPostE T.obj W i (β + Finsupp.single i 1) nuP hW).obj
      ((homContentPreE T W.obj i muM hT).obj Z))) :=
  -(a ≫ a ≫ (homContentMixedInterchange T W i β hT hW Z).inv)

/-- Both composites of the prescribed swapping entries retain the minus.
In functional order these are -a² and -J⁻¹ a² J, respectively. -/
theorem homContentMixedSwap_products (Z : homWeightSector T.obj W.obj muP muM)
    (a : End ((homContentPostE T.obj W i (β + Finsupp.single i 1) nuP hW).obj
      ((homContentPreE T W.obj i muM hT).obj Z))) :
    homContentMixedSwap T W i β hT hW Z a ≫
        (homContentMixedInterchange T W i β hT hW Z).hom = -(a ≫ a) ∧
    (homContentMixedInterchange T W i β hT hW Z).hom ≫
        homContentMixedSwap T W i β hT hW Z a =
      -((homContentMixedInterchange T W i β hT hW Z).hom ≫ a ≫ a ≫
        (homContentMixedInterchange T W i β hT hW Z).inv) := by
  constructor <;> simp only [homContentMixedSwap, Preadditive.neg_comp,
    Preadditive.comp_neg, Category.assoc, Iso.inv_hom_id, Category.comp_id]

end Factors
end OddMath.SKM
