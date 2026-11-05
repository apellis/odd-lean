import OddMath.SKM.RouquierHomBendMonomials

/-! # Weight equality charts for the ordered mixed-bend words

SwappedHomInversion §3 (4)–(5): changing a presentation of the two
input weights transports the prescribed negative pre-cap and post-unit.
The charts use equality induction, retaining both endpoint functors.
-/
noncomputable section
set_option quotPrecheck false
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {I X : Type*} [AddCommGroup X] {D : Datum I X}
  (T W : RouquierFamily (k := k) (B := B) D)
  {a a' b b' : X} (ha : a = a') (hb : b = b')

/-- Change only the presentations of the two Hom weights. -/
def homWeightEquivalence : homWeightSector T.obj W.obj a b ≌
    homWeightSector T.obj W.obj a' b' :=
  Pi.eqToEquivalence (fun p : X × X => homWeightSector T.obj W.obj p.1 p.2)
    (show (a, b) = (a', b') from Prod.ext ha hb)

instance : (homWeightEquivalence T W ha hb).functor.Additive := by
  subst a'
  subst b'
  change (𝟭 (homWeightSector T.obj W.obj a b)).Additive
  infer_instance

variable (i : I) {c d : X} (hp : -a + D.α i = -c) (hr : b + D.α i = d)
  (β : I →₀ ℕ) (Z : homWeightSector T.obj W.obj a b)
local notation "K" => (homWeightEquivalence T W ha hb).functor
local notation "hp'" => (show -a' + D.α i = -c from ha ▸ hp)
local notation "hr'" => (show b' + D.α i = d from hb ▸ hr)
local notation "S" => (homContentPreE T W.obj i b hp).obj
  ((homContentPreF T W.obj i b hp).obj Z)
local notation "S'" => (homContentPreE T W.obj i b' hp').obj
  ((homContentPreF T W.obj i b' hp').obj ((K).obj Z))
local notation "Q" => (homContentPostF T.obj W i β a hr).obj
  ((homContentPostE T.obj W i β a hr).obj Z)
local notation "Q'" => (homContentPostF T.obj W i β a' hr').obj
  ((homContentPostE T.obj W i β a' hr').obj ((K).obj Z))

/-- The source chart changes the weight presentations of the same
normalized precomposition adjunction. -/
def homPreWeightIso : (K).obj S ≅ S' := by
  subst a'
  subst b'
  exact Iso.refl _

/-- The target chart changes the weight presentations of the same
shifted postcomposition pair. -/
def homPostWeightIso : (K).obj Q ≅ Q' := by
  subst a'
  subst b'
  exact Iso.refl _

section Pullback
variable (Z' : homWeightSector T.obj W.obj a' b')
local notation "Zₚ" => (homWeightEquivalence T W ha hb).inverse.obj Z'

/-- The source chart for a given input pulled back along the weight equivalence. -/
def homPreWeightPullbackIso :
    (K).obj ((homContentPreE T W.obj i b hp).obj
      ((homContentPreF T W.obj i b hp).obj Zₚ)) ≅
    (homContentPreE T W.obj i b' hp').obj
      ((homContentPreF T W.obj i b' hp').obj Z') := by
  subst a'
  subst b'
  exact Iso.refl _

/-- The target chart for a given input pulled back along the weight equivalence. -/
def homPostWeightPullbackIso :
    (K).obj ((homContentPostF T.obj W i β a hr).obj
      ((homContentPostE T.obj W i β a hr).obj Zₚ)) ≅
    (homContentPostF T.obj W i β a' hr').obj
      ((homContentPostE T.obj W i β a' hr').obj Z') := by
  subst a'
  subst b'
  exact Iso.refl _

/-- The literal word on the pulled-back input uses the given word on the
normalized input, through precisely its source and target equality charts. -/
theorem homCapCup_weight_pullback_square
    (hdot : ∀ {x y : X} (h : x + D.α i = y), IsIso (T.dot i h)) (n s : ℕ) :
    (K).map (letI := hdot hp;
      homPreNegativeCap T W.obj i b hp n Zₚ ≫
        homContentPostCup T.obj W i β a hr s Zₚ) ≫
      (homPostWeightPullbackIso T W ha hb i hr β Z').hom =
    (homPreWeightPullbackIso T W ha hb i hp Z').hom ≫
      (letI := hdot hp';
        homPreNegativeCap T W.obj i b' hp' n Z' ≫
          homContentPostCup T.obj W i β a' hr' s Z') := by
  subst a'
  subst b'
  change (letI := hdot hp;
    homPreNegativeCap T W.obj i b hp n Z' ≫ homContentPostCup T.obj W i β a hr s Z') ≫ 𝟙 _ =
    𝟙 _ ≫ (letI := hdot hp;
      homPreNegativeCap T W.obj i b hp n Z' ≫ homContentPostCup T.obj W i β a hr s Z')
  simp only [Category.comp_id, Category.id_comp]
end Pullback

end OddMath.SKM
