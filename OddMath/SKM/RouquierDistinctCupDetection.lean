import OddMath.SKM.RouquierDistinctCapDetection

/-! # Detecting the distinct cup pitchfork at nonnegative height

The bicategorical form of `Lemma71Cup.ext_EEF`, used in Brundan–Ellis
Lemma 7.1 (7.2). The actual distinct right mate transports into the
left-whiskered positive augmented inverse. Testing its principal and
finite cap rows detects the whole map; the tests themselves remain to
be evaluated in the cap-pitchfork proof.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  {I X : Type*} [AddCommGroup X] {D : Datum I X} {Sc : Scalars D k}
  (T : RouquierFamily (k := k) (B := B) D) (M : RouquierMulticolour T Sc)
namespace RouquierFamily

/-- The prescribed sideways crossing on the target of the cup test. -/
def distinctCupTarget {i j : I} {a b c d : X}
    (hi : a + D.α i = b) (hj : a + D.α j = c)
    (hij : b + D.α j = d) (hji : c + D.α i = d) :
    (T.F i hi ≫ T.E j hj) ≫ T.E i hji ⟶
      T.E j hij ≫ (T.F i hji ≫ T.E i hji) :=
  crossMate (T.adj i hi) (T.adj i hji) (T.cross i j hj hji hi hij) ▷ T.E i hji ≫
    (associator (T.E j hij) (T.F i hji) (T.E i hji)).hom

include M in
/-- The target comparison uses only the distinct right-mate inverse. -/
theorem distinctCupTarget_isIso {i j : I} (hne : i ≠ j) {a b c d : X}
    (hi : a + D.α i = b) (hj : a + D.α j = c)
    (hij : b + D.α j = d) (hji : c + D.α i = d) :
    IsIso (T.distinctCupTarget hi hj hij hji) := by
  have := M.invNe i j hne hj hji hi hij
  have : IsIso (crossMate (T.adj i hi) (T.adj i hji)
      (T.cross i j hj hji hi hij) ▷ T.E i hji) :=
    ((homPost (k := k) (T.E i hji)).mapIso
      (asIso (crossMate (T.adj i hi) (T.adj i hji) (T.cross i j hj hji hi hij)))).isIso_hom
  unfold distinctCupTarget
  infer_instance

include M in
/-- The principal test and all finite cap-row tests determine the whole
cup-target map at nonnegative shifted height. -/
theorem distinctCup_hom_ext_of_nonneg {i j : I} (hne : i ≠ j)
    {a b c d e : X} (hi : a + D.α i = b) (hj : a + D.α j = c)
    (hij : b + D.α j = d) (hji : c + D.α i = d)
    (hnext : d + D.α i = e) (hh : 0 ≤ D.h i d)
    {Z : T.obj b ⟶ T.obj d}
    (f g : Z ⟶ (T.F i hi ≫ T.E j hj) ≫ T.E i hji)
    (hprincipal : f ≫ T.distinctCupTarget hi hj hij hji ≫
        T.E j hij ◁ (T.loc i hji hnext).sig =
      g ≫ T.distinctCupTarget hi hj hij hji ≫ T.E j hij ◁ (T.loc i hji hnext).sig)
    (hrow : ∀ n, n < (D.h i d).toNat →
      f ≫ T.distinctCupTarget hi hj hij hji ≫ T.E j hij ◁ (T.loc i hji hnext).capD n =
      g ≫ T.distinctCupTarget hi hj hij hji ≫ T.E j hij ◁ (T.loc i hji hnext).capD n) :
    f = g := by
  have := T.distinctCupTarget_isIso M hne hi hj hij hji
  apply (cancel_mono (T.distinctCupTarget hi hj hij hji)).mp
  apply (T.loc i hji hnext).whiskerLeft_hom_ext_of_nonneg hh (T.E j hij)
  · simpa only [Category.assoc] using hprincipal
  · intro n hn
    simpa only [Category.assoc] using hrow n hn

end RouquierFamily
end OddMath.SKM
