import OddMath.SKM.RouquierMateSeries

/-!
# Mate projections from ordered sector coordinates

This ports the reduction used for `rouqSig_eq` in
`Categorification/TwoRep/RouqCoproduct.lean`. Its downstream consumer is the
bubble comparison for the reservoir–probe Hom family.

The theorem derives both projections from the cup–crossing–cap composite,
provided the sector dots intertwine, the cap–cup projections factor, and the
dotted coordinates are the specified ordered powers. These hypotheses are
not supplied here by the content-shifted Hom construction. No inverse of the
coupled mate, negative bubble window, or feedback nilpotence is assumed.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
open scoped BigOperators
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

/-- The normalized mate formula follows from sector dot intertwining and
ordered factor coordinates. Establishing these hypotheses for the shifted
Hom family is a separate obligation; this is not an A2 theorem. -/
theorem SuperRouquierLoc.MateProjectionFormula.of_coordinates
    {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)
    (x₁ : E₁ ⟶ E₁) (x₂ : E₂ ⟶ E₂) (t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (p : ZMod 2)
    (hslide : t ≫ E₁ ◁ x₂ - koszulSign p p • (x₁ ▷ E₂ ≫ t) = 𝟙 (E₁ ≫ E₂))
    {XA XB YA YB : b ⟶ b}
    (inA : XA ⟶ F₁ ≫ E₁) (inB : XB ⟶ F₁ ≫ E₁)
    (outA : E₂ ≫ F₂ ⟶ YA) (outB : E₂ ≫ F₂ ⟶ YB)
    (xA : End XA) (xB wB : End XB) (yA : End YA) (yB zB : End YB)
    (hxA : inA ≫ (F₁ ◁ x₁) = xA ≫ inA)
    (hxB : inB ≫ (F₁ ◁ x₁) = xB ≫ inB)
    (hyA : (x₂ ▷ F₂) ≫ outA = outA ≫ yA)
    (hyB : (x₂ ▷ F₂) ≫ outB = outB ≫ yB)
    (hwB : wB ≫ xB = 𝟙 XB) (hzB : yB ≫ zB = 𝟙 YB)
    (uA : ℕ → (𝟙 b ⟶ YA)) (vA : ℕ → (XA ⟶ 𝟙 b))
    (uB : ℤ → (𝟙 b ⟶ YB)) (vB : ℤ → (XB ⟶ 𝟙 b))
    (hC : inB ≫ (A₁.counit ≫ A₂.unit) ≫ outA = vB 0 ≫ uA 0)
    (hD : inA ≫ (A₁.counit ≫ A₂.unit) ≫ outB = vA 0 ≫ uB 0)
    (nC nD : ℕ) (hnC : yA ^ nC = 0) (hnD : xA ^ nD = 0)
    (huA : ∀ r < nC, uA r = uA 0 ≫ (yA ^ r))
    (hvB : ∀ r < nC, vB (-(r : ℤ) - 1) = (wB ^ (r + 1)) ≫ vB 0)
    (hvA : ∀ r < nD, vA r = (xA ^ r) ≫ vA 0)
    (huB : ∀ r < nD, uB (-(r : ℤ) - 1) = uB 0 ≫ (zB ^ (r + 1))) :
    SuperRouquierLoc.MateProjectionFormula A₁ A₂ t p
      inA inB outA outB uA vA uB vB nC nD := by
  have hs := rouquierMate_normalized_slide A₁ A₂ x₁ x₂ t p hslide
  have hc := mate_slide_projection _ _ _ _ _ hs inB outA xB yA hxB hyA
  have hd := mate_slide_projection _ _ _ _ _ hs inA outB xA yB hxA hyB
  rw [hC] at hc
  rw [hD] at hd
  have ec := mate_series_probe_source xB wB yA (vB 0 ≫ uA 0) _
    (koszulSign p p) hc hwB nC hnC
  have ed := mate_series_probe_target xA yB zB (vA 0 ≫ uB 0) _
    (koszulSign p p) (koszulSign_mul_self p p) hd hzB nD hnD
  constructor
  · refine ec.trans ?_
    apply Finset.sum_congr rfl
    intro r hr
    rw [huA r (Finset.mem_range.mp hr), hvB r (Finset.mem_range.mp hr)]
    simp only [Category.assoc]
  · refine ed.trans ?_
    congr 1
    apply Finset.sum_congr rfl
    intro r hr
    rw [hvA r (Finset.mem_range.mp hr), huB r (Finset.mem_range.mp hr)]
    simp only [Category.assoc]

end OddMath.SKM
