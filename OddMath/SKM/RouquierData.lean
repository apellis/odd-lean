import OddMath.SKM.Basic
import StringDiagrams.Super.Bicategory

/-!
# Super Rouquier generator data

Ports the interfaces in `Categorification/TwoRep/RouqSl2.lean` and
`Categorification/TwoRep/RouqModel.lean`, with boundary coefficients from
`Categorification/TwoRep/RouqBoundary.lean`, to the super conventions of
Brundan–Ellis, Definition 1.5, (1.10)–(1.14).

The ambient structure is `TwoSupercategory`, not an ordinary bicategory.
Homogeneous inverse entries encode parity-shifted summands: a row of parity
`p` is an even row into the formal summand `Π^p`. In particular the common
`FE` summand has shift `|i|`, and identity summand `n` has shift `n |i|`.
No parity shift is silently identified with the identity functor.

`RouquierFamily` is generator and local-inversion data, NOT a representation
of the complete presentation: the multicolour quadratic, braid and mixed
inversion relations must still be verified. Its local inverses are legitimate
inputs for a factor action, never hypotheses of a separated-fusion theorem.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory

universe u v w r
variable {k : Type r} [CommRing k]

/-- A parity-indexed inverse matrix, without choosing biproduct objects.
The profile records the shifts making every component an even map. -/
structure SuperSumInvTo {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear k C] [Supercategory k C] {A B Z : C}
    (f : A ⟶ B) (g : ℕ → (A ⟶ Z)) (p : ZMod 2) (q : ℕ → ZMod 2) (n : ℕ) where
  f' : B ⟶ A
  g' : ℕ → (Z ⟶ A)
  f_mem : f ∈ parity (R := k) A B p
  g_mem : ∀ m, g m ∈ parity (R := k) A Z (q m)
  f'_mem : f' ∈ parity (R := k) B A p
  g'_mem : ∀ m, g' m ∈ parity (R := k) Z A (q m)
  total : f ≫ f' + ∑ m ∈ Finset.range n, g m ≫ g' m = 𝟙 A
  ff : f' ≫ f = 𝟙 B
  fg : ∀ m, m < n → f' ≫ g m = 0
  gf : ∀ m, m < n → g' m ≫ f = 0
  gg : ∀ m l, m < n → l < n → g' m ≫ g l = if m = l then 𝟙 Z else 0

/-- The column version of the parity-indexed inverse matrix. -/
structure SuperSumInvFrom {C : Type u} [Category.{v} C] [Preadditive C]
    [Linear k C] [Supercategory k C] {A B Z : C}
    (f : B ⟶ A) (g : ℕ → (Z ⟶ A)) (p : ZMod 2) (q : ℕ → ZMod 2) (n : ℕ) where
  f' : A ⟶ B
  g' : ℕ → (A ⟶ Z)
  f_mem : f ∈ parity (R := k) B A p
  g_mem : ∀ m, g m ∈ parity (R := k) Z A (q m)
  f'_mem : f' ∈ parity (R := k) A B p
  g'_mem : ∀ m, g' m ∈ parity (R := k) A Z (q m)
  total : f' ≫ f + ∑ m ∈ Finset.range n, g' m ≫ g m = 𝟙 A
  ff : f ≫ f' = 𝟙 B
  fg : ∀ m, m < n → f ≫ g' m = 0
  gf : ∀ m, m < n → g m ≫ f' = 0
  gg : ∀ m l, m < n → l < n → g m ≫ g' l = if m = l then 𝟙 Z else 0

variable {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]

/-- Right adjunction with even unit and counit in a 2-supercategory. -/
structure SuperAdjunction {a b : B} (E : a ⟶ b) (F : b ⟶ a) where
  unit : 𝟙 a ⟶ E ≫ F
  counit : F ≫ E ⟶ 𝟙 b
  unit_mem : unit ∈ parity (R := k) _ _ 0
  counit_mem : counit ∈ parity (R := k) _ _ 0
  left_triangle : (leftUnitor E).inv ≫ unit ▷ E ≫ (associator E F E).hom ≫
    E ◁ counit ≫ (rightUnitor E).hom = 𝟙 E
  right_triangle : (rightUnitor F).inv ≫ F ◁ unit ≫ (associator F E F).inv ≫
    counit ▷ F ≫ (leftUnitor F).hom = 𝟙 F

/-- Vertical powers; their order is fixed, including for an odd dot. -/
def rouquierPower {a b : B} {E : a ⟶ b} (x : E ⟶ E) : ℕ → (E ⟶ E)
  | 0 => 𝟙 E
  | n + 1 => rouquierPower x n ≫ x

/-- The actual ordered cup–crossing–cap mate, not an independently chosen map. -/
def rouquierMate {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
    {E₂ : b ⟶ c} {F₂ : c ⟶ b}
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)
    (t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂) : F₁ ≫ E₁ ⟶ E₂ ≫ F₂ :=
  (rightUnitor (F₁ ≫ E₁)).inv ≫ (F₁ ≫ E₁) ◁ A₂.unit ≫
  (associator F₁ E₁ (E₂ ≫ F₂)).hom ≫
  F₁ ◁ (associator E₁ E₂ F₂).inv ≫ F₁ ◁ (t ▷ F₂) ≫
  (associator F₁ (E₁ ≫ E₂) F₂).inv ≫
  (associator F₁ E₁ E₂).inv ▷ F₂ ≫
  (A₁.counit ▷ E₂) ▷ F₂ ≫ (leftUnitor E₂).hom ▷ F₂

/-- Local rank-one data with signed slides and homogeneous inverse components. -/
structure SuperRouquierLoc {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a}
    {E₂ : b ⟶ c} {F₂ : c ⟶ b}
    (A₁ : SuperAdjunction (k := k) E₁ F₁) (A₂ : SuperAdjunction (k := k) E₂ F₂)
    (x₁ : E₁ ⟶ E₁) (x₂ : E₂ ⟶ E₂) (t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂)
    (p : ZMod 2) (h : ℤ) where
  dot₁_mem : x₁ ∈ parity (R := k) _ _ p
  dot₂_mem : x₂ ∈ parity (R := k) _ _ p
  cross_mem : t ∈ parity (R := k) _ _ p
  slide_left : E₁ ◁ x₂ ≫ t - koszulSign p p • (t ≫ x₁ ▷ E₂) = 𝟙 _
  slide_right : t ≫ E₁ ◁ x₂ - koszulSign p p • (x₁ ▷ E₂ ≫ t) = 𝟙 _
  invPos : 0 ≤ h → SuperSumInvTo (k := k) (rouquierMate A₁ A₂ t)
    (fun n => F₁ ◁ rouquierPower x₁ n ≫ A₁.counit) p (fun n => n * p) h.toNat
  invNeg : h ≤ 0 → SuperSumInvFrom (k := k) (rouquierMate A₁ A₂ t)
    (fun n => A₂.unit ≫ rouquierPower x₂ n ▷ F₂) p (fun n => n * p) (-h).toNat

variable {I X : Type*} [AddCommGroup X] (D : Datum I X)

/-- Weight-indexed upward generators with their prescribed super parities. -/
structure RouquierData where
  supercategory : TwoSupercategory k B := by infer_instance
  obj : X → B
  E : ∀ (i : I) {x y : X}, x + D.α i = y → (obj x ⟶ obj y)
  dot : ∀ (i : I) {x y : X} (h : x + D.α i = y), E i h ⟶ E i h
  dot_mem : ∀ (i : I) {x y : X} (h : x + D.α i = y),
    dot i h ∈ parity (R := k) _ _ (D.parity i)
  cross : ∀ (i j : I) {a b c d : X} (h₁ : a + D.α j = b)
    (h₂ : b + D.α i = d) (h₃ : a + D.α i = c) (h₄ : c + D.α j = d),
    E j h₁ ≫ E i h₂ ⟶ E i h₃ ≫ E j h₄
  cross_mem : ∀ (i j : I) {a b c d : X} (h₁ : a + D.α j = b)
    (h₂ : b + D.α i = d) (h₃ : a + D.α i = c) (h₄ : c + D.α j = d),
    cross i j h₁ h₂ h₃ h₄ ∈ parity (R := k) _ _ (D.parity i * D.parity j)

/-- Factor-action interface. Affine multicolour coherence is a separate obligation. -/
structure RouquierFamily extends RouquierData (k := k) (B := B) D where
  F : ∀ (i : I) {x y : X}, x + D.α i = y → (obj y ⟶ obj x)
  adj : ∀ (i : I) {x y : X} (h : x + D.α i = y), SuperAdjunction (k := k) (E i h) (F i h)
  square : ∀ (i : I) {a b c : X} (h₁ : a + D.α i = b) (h₂ : b + D.α i = c),
    cross i i h₁ h₂ h₁ h₂ ≫ cross i i h₁ h₂ h₁ h₂ = 0
  braid : ∀ (i : I) {a b c d : X} (h₁ : a + D.α i = b)
    (h₂ : b + D.α i = c) (h₃ : c + D.α i = d),
    let t₁ := (associator (E i h₁) (E i h₂) (E i h₃)).inv ≫
      cross i i h₁ h₂ h₁ h₂ ▷ E i h₃ ≫
      (associator (E i h₁) (E i h₂) (E i h₃)).hom
    let t₂ := E i h₁ ◁ cross i i h₂ h₃ h₂ h₃
    t₂ ≫ t₁ ≫ t₂ = t₁ ≫ t₂ ≫ t₁
  loc : ∀ (i : I) {a b c : X} (h₁ : a + D.α i = b) (h₂ : b + D.α i = c),
    SuperRouquierLoc (adj i h₁) (adj i h₂) (dot i h₁) (dot i h₂)
      (cross i i h₁ h₂ h₁ h₂) (D.parity i) (D.h i b)

namespace SuperRouquierLoc
variable {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}
  {A₁ : SuperAdjunction (k := k) E₁ F₁} {A₂ : SuperAdjunction (k := k) E₂ F₂}
  {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂}
  {p : ZMod 2} {h : ℤ} (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t p h)

/-- Boundary coefficients at positive height, formed from the prescribed inverse. -/
def boundaryPos (hh : 0 ≤ h) (m n : ℕ) : 𝟙 b ⟶ 𝟙 b :=
  (L.invPos hh).g' m ≫ (F₁ ◁ rouquierPower x₁ n ≫ A₁.counit)

/-- Boundary coefficients at negative height, in the opposite order. -/
def boundaryNeg (hh : h ≤ 0) (m n : ℕ) : 𝟙 b ⟶ 𝟙 b :=
  (A₂.unit ≫ rouquierPower x₂ m ▷ F₂) ≫ (L.invNeg hh).g' n

omit [TwoSupercategory k B] in
/-- A boundary consumer: the inverse gives the normalized Kronecker window. -/
theorem boundaryPos_eq (hh : 0 ≤ h) (m n : ℕ) (hm : m < h.toNat) (hn : n < h.toNat) :
    L.boundaryPos hh m n = if m = n then 𝟙 (𝟙 b) else 0 :=
  (L.invPos hh).gg m n hm hn

omit [TwoSupercategory k B] in
/-- The negative-height consumer uses cup followed by inverse cap. -/
theorem boundaryNeg_eq (hh : h ≤ 0) (m n : ℕ)
    (hm : m < (-h).toNat) (hn : n < (-h).toNat) :
    L.boundaryNeg hh m n = if m = n then 𝟙 (𝟙 b) else 0 :=
  (L.invNeg hh).gg m n hm hn

omit [TwoSupercategory k B] in
/-- At height two the two inverse columns are orthogonal, including for an odd colour. -/
example (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t p 2) :
    L.boundaryPos (by decide) 0 1 = 0 := by
  simpa using L.boundaryPos_eq (by decide) 0 1 (by decide) (by decide)

end SuperRouquierLoc
end OddMath.SKM
