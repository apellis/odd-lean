import OddMath.SKM.RouquierMate

/-!
# The separated-sector mate projection formula

This states the super replacement for `rouqSig_eq` in
`Categorification/TwoRep/RouqCoproduct.lean`, with the normalization of
`docs/Nondegeneracy/SeparatedFactorInversion.md`, equation (2).
Its downstream consumer is normalized bubble transport for the reservoir–probe
Hom family. This module states an obligation, not a proof of fusion.

Composition is bottom to top: `v ≫ u` denotes the ordered map `u v`.
The raw cup–crossing–cap mate is multiplied by `-q`, where `q = (-1)^p`.
Thus the normalization is trivial for an odd colour and changes both blocks
for an even colour. The negative probe indices are integers, not truncated
natural subtraction. The sector inclusions and projections must eventually
be supplied by the content-shifted Hom construction; they are explicit inputs
here, not inferred from an independently chosen block matrix.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
open scoped BigOperators
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

/-- The two ordered off-diagonal projection identities for one cup–crossing–cap
mate. This is an unproved hypothesis for separated fusion, with no inversion
assumed. `nC` and `nD` are truncation bounds for the two reservoir dots.
The supplied sector comparison maps include all content-dependent parity lines.
The coefficients `uA`, `vA`, `uB`, `vB` are the corresponding dotted factor
units and counits; their identification with factor maps remains an obligation. -/
def SuperRouquierLoc.MateProjectionFormula
    {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
    {E₂ : b ⟶ c} {F₂ : c ⟶ b}
    (A₁ : SuperAdjunction (k := k) E₁ F₁)
    (A₂ : SuperAdjunction (k := k) E₂ F₂)
    (t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) (p : ZMod 2)
    {XA XB YA YB : b ⟶ b}
    (inA : XA ⟶ F₁ ≫ E₁) (inB : XB ⟶ F₁ ≫ E₁)
    (outA : E₂ ≫ F₂ ⟶ YA) (outB : E₂ ≫ F₂ ⟶ YB)
    (uA : ℕ → (𝟙 b ⟶ YA)) (vA : ℕ → (XA ⟶ 𝟙 b))
    (uB : ℤ → (𝟙 b ⟶ YB)) (vB : ℤ → (XB ⟶ 𝟙 b))
    (nC nD : ℕ) : Prop :=
  (inB ≫ (-(koszulSign p p) • rouquierMate A₁ A₂ t) ≫ outA =
    ∑ r ∈ Finset.range nC, (koszulSign p p) ^ r • (vB (-(r : ℤ) - 1) ≫ uA r)) ∧
  (inA ≫ (-(koszulSign p p) • rouquierMate A₁ A₂ t) ≫ outB =
    -(∑ r ∈ Finset.range nD,
      (koszulSign p p) ^ (r + 1) • (vA r ≫ uB (-(r : ℤ) - 1))))

end OddMath.SKM
