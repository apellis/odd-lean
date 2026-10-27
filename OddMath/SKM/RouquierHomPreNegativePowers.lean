import OddMath.SKM.RouquierHomPreSuperInverse

/-!
# Negative probe powers in normalized precomposition windows

This proves the negative-index extension of the dotted coordinates in
`SwappedHomInversion.md`, §2. The index n denotes exponent -n: only the
probe dot is inverted. Units and counits are the prescribed normalized
precomposition adjunction, not maps defined by their coordinate formulas.
The literal central series comparison of §3 (4)–(5) remains separate.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T : RouquierFamily (k := k) (B := B) D) (W : X → B)
  (i : I) (muM : X) {muP nuP : X} (h : -nuP + D.α i = -muP)
  [IsIso (T.dot i h)]

/-- The inverse of the raw probe dot, whiskered without a transpose. -/
def homPreDotInverse (Z : homWeightSector T.obj W muP muM) :
    End ((homContentPreE T W i muM h).obj Z) := inv (T.dot i h) ▷ Z

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- Whiskering preserves the first inverse identity. -/
theorem homPreDot_dotInverse (Z : homWeightSector T.obj W muP muM) :
    homReservoirDot T W i muM h Z ≫ homPreDotInverse T W i muM h Z = 𝟙 _ := by
  simp only [homReservoirDot, homPreDotInverse,
    ← TwoSupercategory.comp_whiskerRight (R := k), IsIso.hom_inv_id,
    TwoSupercategory.id_whiskerRight (R := k)]
  rfl

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- Whiskering preserves the other inverse identity, including on zero corners. -/
theorem homPreDotInverse_dot (Z : homWeightSector T.obj W muP muM) :
    homPreDotInverse T W i muM h Z ≫ homReservoirDot T W i muM h Z = 𝟙 _ := by
  simp only [homReservoirDot, homPreDotInverse,
    ← TwoSupercategory.comp_whiskerRight (R := k), IsIso.inv_hom_id,
    TwoSupercategory.id_whiskerRight (R := k)]
  rfl

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] [TwoSupercategory k B] in
private theorem preDot_inv_mem : inv (T.dot i h) ∈ parity (R := k) _ _ (D.parity i) :=
  inv_mem (asIso (T.dot i h)) (T.dot_mem i h)

omit [∀ a b : B, PiSupercategory k (a ⟶ b)] in
/-- An inverse odd dot is odd; no even identification is used. -/
theorem homPreDotInverse_power_supernatural (n : ℕ) :
    IsSupernatural k (n * D.parity i)
      (F := homContentPreE T W i muM h)
      (G := homContentPreE T W i muM h)
      (fun Z => homPreDotInverse T W i muM h Z ^ n) := by
  have hi := preDot_inv_mem T i h
  have ht := (homPreTransform (k := k) (c := W muM)
    (rouquierPower (inv (T.dot i h)) n) (rouquierPower_mem hi n)).isSupernatural
      (n * D.parity i)
  simpa only [homPreDotInverse, whiskerRight_rouquierPower (k := k),
    homContentPreE, homPreTransform, ite_true] using ht

/-- The normalized cup dotted by the raw probe power with exponent -n. -/
def homPreNegativeCup (n : ℕ) (Z : homWeightSector T.obj W muP muM) :
    Z ⟶ (homContentPreF T W i muM h).obj ((homContentPreE T W i muM h).obj Z) :=
  (homContentPreAdjunction T W T.leftAdjoints i muM h).unit.app Z ≫
    (homContentPreF T W i muM h).map (homPreDotInverse T W i muM h Z ^ n)

/-- The normalized cap dotted by the raw probe power with exponent -n. -/
def homPreNegativeCap (n : ℕ) (Z : homWeightSector T.obj W nuP muM) :
    (homContentPreE T W i muM h).obj ((homContentPreF T W i muM h).obj Z) ⟶ Z :=
  (homPreDotInverse T W i muM h ((homContentPreF T W i muM h).obj Z) ^ n) ≫
    (homContentPreAdjunction T W T.leftAdjoints i muM h).counit.app Z

/-- Negative dotted cups retain signed naturality on arbitrary homogeneous Hom maps. -/
theorem homPreNegativeCup_supernatural (n : ℕ) :
    IsSupernatural k (n * D.parity i)
      (F := 𝟭 (homWeightSector T.obj W muP muM))
      (G := homContentPreE T W i muM h ⋙ homContentPreF T W i muM h)
      (homPreNegativeCup T W i muM h n) := by
  have hc := isSupernatural_of_natTrans
    (homContentPreAdjunction T W T.leftAdjoints i muM h).unit
    (homContentPreAdjunction_unit_mem T W i muM h)
  have hd := (homPreDotInverse_power_supernatural T W i muM h n).whiskerRight
    (homContentPreF T W i muM h)
  have ht := hc.comp hd
  rw [zero_add] at ht
  exact ht

/-- Negative dotted caps retain signed naturality on arbitrary homogeneous Hom maps. -/
theorem homPreNegativeCap_supernatural (n : ℕ) :
    IsSupernatural k (n * D.parity i)
      (F := homContentPreF T W i muM h ⋙ homContentPreE T W i muM h)
      (G := 𝟭 (homWeightSector T.obj W nuP muM))
      (homPreNegativeCap T W i muM h n) := by
  have hd := (homPreDotInverse_power_supernatural T W i muM h n).whiskerLeft
    (homContentPreF T W i muM h)
  have hc := isSupernatural_of_natTrans
    (homContentPreAdjunction T W T.leftAdjoints i muM h).counit
    (homContentPreAdjunction_counit_mem T W i muM h)
  have ht := hd.comp hc
  rw [add_zero] at ht
  exact ht

/-- Alpha at exponent -n: negative and positive n have equal parity. -/
theorem homPreNegativeCup_coordinates (n : ℕ) (Z : homWeightSector T.obj W muP muM) :
    homPreNegativeCup T W i muM h n Z ≫
      ((homParityShiftDatum (k := k) (leftAdjParity D i (-nuP))).iso
        (T.F i h ≫ T.E i h ≫ Z)).hom =
    koszulSign (leftAdjParity D i (-nuP)) ((n : ZMod 2) * D.parity i) •
      ((leftUnitor Z).inv ≫ T.leftCup i h ▷ Z ≫
        (associator (T.F i h) (T.E i h) Z).hom ≫
        T.F i h ◁ (rouquierPower (inv (T.dot i h)) n ▷ Z)) := by
  rw [homPreNegativeCup, homContentPreAdjunction_leftAdjoints_unit_app]
  simp only [homPreDotInverse, whiskerRight_rouquierPower (k := k),
    homContentPreF, Functor.comp_map, homPre, Category.assoc]
  rw [(homParityShiftDatum (k := k) (leftAdjParity D i (-nuP))).hom_naturality
    (TwoSupercategory.whiskerLeft_mem (T.F i h)
      (TwoSupercategory.whiskerRight_mem Z
        (rouquierPower_mem (preDot_inv_mem T i h) n)))]
  simp only [Linear.comp_smul, Iso.inv_hom_id_assoc]
  rw [koszulSign_smul (R := k)]

/-- Beta at exponent -n, including the inverse cap scalar at its source height. -/
theorem homPreNegativeCap_coordinates (n : ℕ) (Z : homWeightSector T.obj W nuP muM) :
    homPreNegativeCap T W i muM h n Z =
    koszulSign (leftAdjParity D i (-nuP))
      (1 + (n : ZMod 2) * D.parity i) •
      (T.E i h ◁ ((homParityShiftDatum (k := k) (leftAdjParity D i (-nuP))).iso
        (T.F i h ≫ Z)).hom ≫
        rouquierPower (inv (T.dot i h)) n ▷ (T.F i h ≫ Z) ≫
        (associator (T.E i h) (T.F i h) Z).inv ≫
        ((((T.leftAdjScalar i (-nuP))⁻¹ : kˣ) : k) • T.leftCap i h) ▷ Z ≫
        (leftUnitor Z).hom) := by
  rw [homPreNegativeCap, homContentPreAdjunction_leftAdjoints_counit_app]
  simp only [homPreDotInverse, whiskerRight_rouquierPower (k := k),
    Preadditive.comp_zsmul, ← Category.assoc]
  dsimp only [homContentPreF, homContentPreE, Functor.comp_obj, homPre]
  rw [TwoSupercategory.super_interchange
    (rouquierPower_mem (preDot_inv_mem T i h) n)
    ((homParityShiftDatum (k := k) (leftAdjParity D i (-nuP))).hom_mem (T.F i h ≫ Z))]
  simp only [Preadditive.zsmul_comp, smul_smul, koszulSign_add_right, Category.assoc]
  rw [koszulSign_comm ((n : ZMod 2) * D.parity i)]
  have hs (σ : ZMod 2) : koszulSign σ σ = koszulSign σ 1 := by
    fin_cases σ <;> rfl
  rw [hs]

/-- The exponent-zero window is the existing nonnegative window. -/
theorem homPreNegativeCup_zero (Z : homWeightSector T.obj W muP muM) :
    homPreNegativeCup T W i muM h 0 Z = homReservoirCup T W i muM h 0 Z := by
  simp only [homPreNegativeCup, homReservoirCup, pow_zero]

theorem homPreNegativeCap_zero (Z : homWeightSector T.obj W nuP muM) :
    homPreNegativeCap T W i muM h 0 Z = homReservoirCap T W i muM h 0 Z := by
  simp only [homPreNegativeCap, homReservoirCap, pow_zero]

end OddMath.SKM
