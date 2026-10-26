import OddMath.SKM.RouquierMateCoordinates

/-!
# Mate projection coordinates from sector summands

This continues the port of the reduction for `rouqSig_eq` in
`Categorification/TwoRep/RouqCoproduct.lean`. There the coproduct family splits
`E_i` into the two factor summands, the unit and counit are diagonal, and the
dotted coordinates are the factor's own dotted cups and caps. Its downstream
consumer is the coupled mate of the content-shifted Hom family, whose raising
functor has a postcomposition sector and a precomposition sector.

`SuperRouquierLoc.MateProjectionFormula.of_sectors` realizes every coordinate
hypothesis of `MateProjectionFormula.of_coordinates` from sector data:

* sector summands `E₁ₛ, F₁ₛ` (source) and `E₂ₛ, F₂ₛ` (target), with even
  inclusions into, respectively even projections out of, the coupled 1-morphisms;
* sector adjunctions, to which the coupled counit restricts and the coupled
  unit projects;
* sector dots, which the coupled dots restrict to.

The coordinates are then the actual dotted sector cups and caps: positive powers
of the reservoir dot, and positive powers of the inverse probe dot for the
negative indices. The remaining hypotheses are the upward slide of the coupled
crossing, inverses of the two probe dots, and nilpotence of the two reservoir dots.
No inverse of the coupled mate, negative bubble window, or feedback nilpotence is
assumed, and no biproduct completeness of the sectors is used. Constructing the
coupled crossing of the content-shifted Hom family and its slide is a separate
obligation; this is not an A2 theorem.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
open scoped BigOperators
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

section Powers
variable {a b c : B}

omit [∀ a b : B, Preadditive (a ⟶ b)] in
@[simp] theorem rouquierPower_zero {E : a ⟶ b} (x : E ⟶ E) : rouquierPower x 0 = 𝟙 E := rfl

omit [∀ a b : B, Preadditive (a ⟶ b)] in
theorem rouquierPower_succ {E : a ⟶ b} (x : E ⟶ E) (n : ℕ) :
    rouquierPower x (n + 1) = rouquierPower x n ≫ x := rfl

include k

/-- Whiskered powers on the left are powers in the endomorphism monoid. -/
theorem whiskerLeft_rouquierPower (F : c ⟶ a) {E : a ⟶ b} (x : E ⟶ E) (n : ℕ) :
    (show End (F ≫ E) from F ◁ x) ^ n = F ◁ rouquierPower x n := by
  induction n with
  | zero => exact (TwoSupercategory.whiskerLeft_id (R := k) F E).symm
  | succ n ih =>
    rw [pow_succ', End.mul_def, ih, rouquierPower_succ,
      TwoSupercategory.whiskerLeft_comp (R := k)]

/-- Whiskered powers on the right are powers in the endomorphism monoid. -/
theorem whiskerRight_rouquierPower {E : a ⟶ b} (x : E ⟶ E) (F : b ⟶ c) (n : ℕ) :
    (show End (E ≫ F) from x ▷ F) ^ n = rouquierPower x n ▷ F := by
  induction n with
  | zero => exact (TwoSupercategory.id_whiskerRight (R := k) E F).symm
  | succ n ih =>
    rw [pow_succ', End.mul_def, ih, rouquierPower_succ,
      TwoSupercategory.comp_whiskerRight (R := k)]

theorem zero_whiskerRight' {E E' : a ⟶ b} (F : b ⟶ c) : (0 : E ⟶ E') ▷ F = 0 := by
  rw [show (0 : E ⟶ E') = (0 : ℤ) • (0 : E ⟶ E') by simp,
    TwoSupercategory.zsmul_whiskerRight (R := k), zero_smul]

theorem whiskerLeft_zero' (F : c ⟶ a) {E E' : a ⟶ b} : F ◁ (0 : E ⟶ E') = 0 := by
  rw [show (0 : E ⟶ E') = (0 : ℤ) • (0 : E ⟶ E') by simp,
    TwoSupercategory.whiskerLeft_zsmul (R := k), zero_smul]

end Powers

/-- The inclusion of a source sector `F₁ₛ ≫ E₁ₛ` into `F₁ ≫ E₁`. -/
def sectorIn {a b : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E : a ⟶ b} {F : b ⟶ a}
    (iE : E ⟶ E₁) (iF : F ⟶ F₁) : F ≫ E ⟶ F₁ ≫ E₁ :=
  iF ▷ E ≫ F₁ ◁ iE

/-- The projection of `E₂ ≫ F₂` onto a target sector `E₂ₛ ≫ F₂ₛ`. -/
def sectorOut {b c : B} {E₂ : b ⟶ c} {F₂ : c ⟶ b} {E : b ⟶ c} {F : c ⟶ b}
    (pE : E₂ ⟶ E) (pF : F₂ ⟶ F) : E₂ ≫ F₂ ⟶ E ≫ F :=
  pE ▷ F₂ ≫ E ◁ pF

/-- A source sector: a summand of a right adjunction preserved by its dot and
counit. Only the inclusions are used, not a biproduct decomposition. -/
structure SourceSector {a b : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (x₁ : E₁ ⟶ E₁) where
  E : a ⟶ b
  F : b ⟶ a
  adj : SuperAdjunction (k := k) E F
  dot : E ⟶ E
  dot_mem : ∃ q, dot ∈ parity (R := k) _ _ q
  iE : E ⟶ E₁
  iF : F ⟶ F₁
  iF_mem : iF ∈ parity (R := k) _ _ 0
  dot_comm : iE ≫ x₁ = dot ≫ iE
  counit_comm : sectorIn iE iF ≫ A₁.counit = adj.counit

/-- A target sector: a summand of a right adjunction preserved by its dot and unit. -/
structure TargetSector {b c : B} {E₂ : b ⟶ c} {F₂ : c ⟶ b}
    (A₂ : SuperAdjunction (k := k) E₂ F₂) (x₂ : E₂ ⟶ E₂) where
  E : b ⟶ c
  F : c ⟶ b
  adj : SuperAdjunction (k := k) E F
  dot : E ⟶ E
  dot_mem : ∃ q, dot ∈ parity (R := k) _ _ q
  pE : E₂ ⟶ E
  pF : F₂ ⟶ F
  pF_mem : pF ∈ parity (R := k) _ _ 0
  dot_comm : x₂ ≫ pE = pE ≫ dot
  unit_comm : A₂.unit ≫ sectorOut pE pF = adj.unit

namespace SourceSector
variable {a b : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
  {A₁ : SuperAdjunction (k := k) E₁ F₁} {x₁ : E₁ ⟶ E₁} (S : SourceSector A₁ x₁)

/-- The coupled dot restricts to the sector dot through the inclusion. -/
theorem in_dot : sectorIn S.iE S.iF ≫ (F₁ ◁ x₁) = (S.F ◁ S.dot) ≫ sectorIn S.iE S.iF := by
  obtain ⟨q, hq⟩ := S.dot_mem
  unfold sectorIn
  rw [Category.assoc, ← TwoSupercategory.whiskerLeft_comp (R := k), S.dot_comm,
    TwoSupercategory.whiskerLeft_comp (R := k), ← Category.assoc,
    TwoSupercategory.super_interchange S.iF_mem hq, koszulSign_zero_left, one_smul,
    Category.assoc]

/-- The whole factor is a source sector of itself. -/
def self (A₁ : SuperAdjunction (k := k) E₁ F₁) (x₁ : E₁ ⟶ E₁) {q : ZMod 2}
    (hx : x₁ ∈ parity (R := k) _ _ q) : SourceSector A₁ x₁ where
  E := E₁
  F := F₁
  adj := A₁
  dot := x₁
  dot_mem := ⟨q, hx⟩
  iE := 𝟙 E₁
  iF := 𝟙 F₁
  iF_mem := id_mem _
  dot_comm := by rw [Category.id_comp, Category.comp_id]
  counit_comm := by
    simp only [sectorIn, TwoSupercategory.id_whiskerRight (R := k),
      TwoSupercategory.whiskerLeft_id (R := k), Category.id_comp]

/-- The dotted sector cap with `n` dots. -/
def cap (n : ℕ) : S.F ≫ S.E ⟶ 𝟙 b := S.F ◁ rouquierPower S.dot n ≫ S.adj.counit

end SourceSector

namespace TargetSector
variable {b c : B} {E₂ : b ⟶ c} {F₂ : c ⟶ b}
  {A₂ : SuperAdjunction (k := k) E₂ F₂} {x₂ : E₂ ⟶ E₂} (S : TargetSector A₂ x₂)

/-- The coupled dot restricts to the sector dot through the projection. -/
theorem dot_out : (x₂ ▷ F₂) ≫ sectorOut S.pE S.pF = sectorOut S.pE S.pF ≫ (S.dot ▷ S.F) := by
  obtain ⟨q, hq⟩ := S.dot_mem
  unfold sectorOut
  rw [← Category.assoc, ← TwoSupercategory.comp_whiskerRight (R := k), S.dot_comm,
    TwoSupercategory.comp_whiskerRight (R := k), Category.assoc,
    TwoSupercategory.super_interchange hq S.pF_mem, koszulSign_zero_right, one_smul,
    Category.assoc]

/-- The whole factor is a target sector of itself. -/
def self (A₂ : SuperAdjunction (k := k) E₂ F₂) (x₂ : E₂ ⟶ E₂) {q : ZMod 2}
    (hx : x₂ ∈ parity (R := k) _ _ q) : TargetSector A₂ x₂ where
  E := E₂
  F := F₂
  adj := A₂
  dot := x₂
  dot_mem := ⟨q, hx⟩
  pE := 𝟙 E₂
  pF := 𝟙 F₂
  pF_mem := id_mem _
  dot_comm := by rw [Category.id_comp, Category.comp_id]
  unit_comm := by
    simp only [sectorOut, TwoSupercategory.id_whiskerRight (R := k),
      TwoSupercategory.whiskerLeft_id (R := k), Category.comp_id]

/-- The dotted sector cup with `n` dots. -/
def cup (n : ℕ) : 𝟙 b ⟶ S.E ≫ S.F := S.adj.unit ≫ rouquierPower S.dot n ▷ S.F

end TargetSector

variable {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}
  {A₁ : SuperAdjunction (k := k) E₁ F₁} {A₂ : SuperAdjunction (k := k) E₂ F₂}
  {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂}

/-- Probe caps: negative indices use powers of the inverse probe dot. -/
def probeCap (S : SourceSector A₁ x₁) (w : S.E ⟶ S.E) (n : ℤ) : S.F ≫ S.E ⟶ 𝟙 b :=
  S.F ◁ rouquierPower w (-n).toNat ≫ S.adj.counit

/-- Probe cups: negative indices use powers of the inverse probe dot. -/
def probeCup (S : TargetSector A₂ x₂) (z : S.E ⟶ S.E) (n : ℤ) : 𝟙 b ⟶ S.E ≫ S.F :=
  S.adj.unit ≫ rouquierPower z (-n).toNat ▷ S.F

/-- The normalized mate formula with the actual dotted sector cups and caps.
The source and target reservoir sectors are `RA`, `TA`; the probe sectors are
`RB`, `TB`, with inverse dots `w`, `z`. Besides the upward slide of the coupled
crossing, only the probe inverses and reservoir nilpotence are assumed. -/
theorem SuperRouquierLoc.MateProjectionFormula.of_sectors
    (t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (p : ZMod 2)
    (hslide : t ≫ E₁ ◁ x₂ - koszulSign p p • (x₁ ▷ E₂ ≫ t) = 𝟙 (E₁ ≫ E₂))
    (RA RB : SourceSector A₁ x₁) (TA TB : TargetSector A₂ x₂)
    (w : RB.E ⟶ RB.E) (hw : w ≫ RB.dot = 𝟙 RB.E)
    (z : TB.E ⟶ TB.E) (hz : TB.dot ≫ z = 𝟙 TB.E)
    (nC nD : ℕ) (hnC : rouquierPower TA.dot nC = 0) (hnD : rouquierPower RA.dot nD = 0) :
    SuperRouquierLoc.MateProjectionFormula A₁ A₂ t p
      (sectorIn RA.iE RA.iF) (sectorIn RB.iE RB.iF)
      (sectorOut TA.pE TA.pF) (sectorOut TB.pE TB.pF)
      TA.cup RA.cap (probeCup TB z) (probeCap RB w) nC nD := by
  refine SuperRouquierLoc.MateProjectionFormula.of_coordinates (k := k) A₁ A₂ x₁ x₂ t p hslide
    _ _ _ _ (RA.F ◁ RA.dot) (RB.F ◁ RB.dot) (RB.F ◁ w) (TA.dot ▷ TA.F)
    (TB.dot ▷ TB.F) (z ▷ TB.F)
    RA.in_dot RB.in_dot TA.dot_out TB.dot_out ?_ ?_ _ _ _ _ ?_ ?_ nC nD ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← TwoSupercategory.whiskerLeft_comp (R := k), hw,
      TwoSupercategory.whiskerLeft_id (R := k)]
  · rw [← TwoSupercategory.comp_whiskerRight (R := k), hz,
      TwoSupercategory.id_whiskerRight (R := k)]
  · simp only [Category.assoc]
    rw [reassoc_of% RB.counit_comm, TA.unit_comm]
    simp only [probeCap, TargetSector.cup, neg_zero, Int.toNat_zero,
      rouquierPower_zero, TwoSupercategory.whiskerLeft_id (R := k),
      TwoSupercategory.id_whiskerRight (R := k), Category.id_comp, Category.comp_id]
  · simp only [Category.assoc]
    rw [reassoc_of% RA.counit_comm, TB.unit_comm]
    simp only [probeCup, SourceSector.cap, neg_zero, Int.toNat_zero,
      rouquierPower_zero, TwoSupercategory.whiskerLeft_id (R := k),
      TwoSupercategory.id_whiskerRight (R := k), Category.id_comp, Category.comp_id]
  · rw [whiskerRight_rouquierPower (k := k), hnC, zero_whiskerRight' (k := k)]
  · rw [whiskerLeft_rouquierPower (k := k), hnD, whiskerLeft_zero' (k := k)]
  · intro r _
    rw [whiskerRight_rouquierPower (k := k)]
    simp only [TargetSector.cup, rouquierPower_zero,
      TwoSupercategory.id_whiskerRight (R := k), Category.comp_id]
  · intro r _
    rw [whiskerLeft_rouquierPower (k := k)]
    simp only [probeCap, neg_zero, Int.toNat_zero, rouquierPower_zero,
      TwoSupercategory.whiskerLeft_id (R := k), Category.id_comp]
    rw [show (-(-(r : ℤ) - 1)).toNat = r + 1 by omega]
  · intro r _
    rw [whiskerLeft_rouquierPower (k := k)]
    simp only [SourceSector.cap, rouquierPower_zero,
      TwoSupercategory.whiskerLeft_id (R := k), Category.id_comp]
  · intro r _
    rw [whiskerRight_rouquierPower (k := k)]
    simp only [probeCup, neg_zero, Int.toNat_zero, rouquierPower_zero,
      TwoSupercategory.id_whiskerRight (R := k), Category.comp_id]
    rw [show (-(-(r : ℤ) - 1)).toNat = r + 1 by omega]

end OddMath.SKM
