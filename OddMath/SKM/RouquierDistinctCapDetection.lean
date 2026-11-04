import OddMath.SKM.RouquierPitchfork
import OddMath.SKM.RouquierMulticolour
import OddMath.SKM.RouquierHom

/-! # Detecting the distinct cap pitchfork at nonpositive height

This is the bicategorical version of `Lemma71.ext_FEE`, used in the
nonpositive-height proof of Brundan–Ellis Lemma 7.1. The negative local
augmented inverse detects maps after the distinct sideways crossing.
The latter is the prescribed right mate and is invertible by the
multicolour inversion relation. No left-mate or cap-pitchfork hypothesis
is introduced.
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

/-- The exact right-mate transport between the two source bracketings in
`Lemma71.ext_FEE`. -/
def distinctCapSource {i j : I} {a b c d : X}
    (hi : a + D.α i = b) (hj : a + D.α j = c)
    (hij : b + D.α j = d) (hji : c + D.α i = d) :
    (T.E i hi ≫ T.F i hi) ≫ T.E j hj ⟶
      (T.E i hi ≫ T.E j hij) ≫ T.F i hji :=
  (associator (T.E i hi) (T.F i hi) (T.E j hj)).hom ≫
    T.E i hi ◁ crossMate (T.adj i hi) (T.adj i hji) (T.cross i j hj hji hi hij) ≫
    (associator (T.E i hi) (T.E j hij) (T.F i hji)).inv

include M in
/-- Only the distinct right-mate inversion relation is needed here. -/
theorem distinctCapSource_isIso {i j : I} (hne : i ≠ j) {a b c d : X}
    (hi : a + D.α i = b) (hj : a + D.α j = c)
    (hij : b + D.α j = d) (hji : c + D.α i = d) :
    IsIso (T.distinctCapSource hi hj hij hji) := by
  have := M.invNe i j hne hj hji hi hij
  have : IsIso (T.E i hi ◁ crossMate (T.adj i hi) (T.adj i hji)
      (T.cross i j hj hji hi hij)) :=
    ((homPre (k := k) (T.E i hi)).mapIso
      (asIso (crossMate (T.adj i hi) (T.adj i hji) (T.cross i j hj hji hi hij)))).isIso_hom
  unfold distinctCapSource
  infer_instance

include M in
/-- At nonpositive height the principal test and every finite cup-column
test determine the entire distinct-cap source map, as in Lemma 7.1. -/
theorem distinctCap_hom_ext_of_nonpos {i j : I} (hne : i ≠ j)
    {a₀ a b c d : X} (h₀ : a₀ + D.α i = a)
    (hi : a + D.α i = b) (hj : a + D.α j = c)
    (hij : b + D.α j = d) (hji : c + D.α i = d) (hh : D.h i a ≤ 0)
    {Z : T.obj a ⟶ T.obj c}
    (f g : (T.E i hi ≫ T.E j hij) ≫ T.F i hji ⟶ Z)
    (hprincipal : (T.loc i h₀ hi).sig ▷ T.E j hj ≫
        T.distinctCapSource hi hj hij hji ≫ f =
      (T.loc i h₀ hi).sig ▷ T.E j hj ≫ T.distinctCapSource hi hj hij hji ≫ g)
    (hcolumn : ∀ n, n < (-D.h i a).toNat →
      (T.loc i h₀ hi).cupD n ▷ T.E j hj ≫ T.distinctCapSource hi hj hij hji ≫ f =
      (T.loc i h₀ hi).cupD n ▷ T.E j hj ≫ T.distinctCapSource hi hj hij hji ≫ g) :
    f = g := by
  have := T.distinctCapSource_isIso M hne hi hj hij hji
  apply (cancel_epi (T.distinctCapSource hi hj hij hji)).mp
  exact (T.loc i h₀ hi).whiskerRight_hom_ext_of_nonpos hh (T.E j hj)
    (T.distinctCapSource hi hj hij hji ≫ f)
    (T.distinctCapSource hi hj hij hji ≫ g) hprincipal hcolumn

end RouquierFamily
end OddMath.SKM
