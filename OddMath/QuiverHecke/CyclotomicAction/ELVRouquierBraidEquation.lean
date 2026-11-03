import OddMath.SKM.RouquierMulticolour

/-! # The uncorrected multicolour braid equation of Rouquier data

Brundan--Ellis (1.9). Capture the literal RouquierMulticolour.braid formula
before specializing large chosen action data.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.QuiverHecke.ELVOld
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)]
  {I X : Type r} [AddCommGroup X] (D : SKM.Datum I X)
  (R : SKM.RouquierData (k := k) (B := B) D) (i j l : I)
  {a bl bj bi clj cli cji d : X}
  (hal : a + D.α l = bl) (haj : a + D.α j = bj) (hai : a + D.α i = bi)
  (hlj : bl + D.α j = clj) (hli : bl + D.α i = cli) (hjl : bj + D.α l = clj)
  (hji : bj + D.α i = cji) (hil : bi + D.α l = cli) (hij : bi + D.α j = cji)
  (hd₁ : clj + D.α i = d) (hd₂ : cli + D.α j = d) (hd₃ : cji + D.α l = d)

/-- Exactly the uncorrected multicolour braid field, with every chosen
crossing and associator retained. -/
def rouquierMulticolourBraidEquation : Prop :=
    R.E l hal ◁ R.cross i j hlj hd₁ hli hd₂ ≫
        (associator (R.E l hal) (R.E i hli) (R.E j hd₂)).inv ≫
        R.cross i l hal hli hai hil ▷ R.E j hd₂ ≫
        (associator (R.E i hai) (R.E l hil) (R.E j hd₂)).hom ≫
        R.E i hai ◁ R.cross j l hil hd₂ hij hd₃ =
      (associator (R.E l hal) (R.E j hlj) (R.E i hd₁)).inv ≫
        R.cross j l hal hlj haj hjl ▷ R.E i hd₁ ≫
        (associator (R.E j haj) (R.E l hjl) (R.E i hd₁)).hom ≫
        R.E j haj ◁ R.cross i l hjl hd₁ hji hd₃ ≫
        (associator (R.E j haj) (R.E i hji) (R.E l hd₃)).inv ≫
        R.cross i j haj hji hai hij ▷ R.E l hd₃ ≫
        (associator (R.E i hai) (R.E j hij) (R.E l hd₃)).hom

local notation "a₀" => R.E l hal ◁ R.cross i j hlj hd₁ hli hd₂
local notation "a₁" => Iso.inv (associator (R.E l hal) (R.E i hli) (R.E j hd₂)) ≫
  R.cross i l hal hli hai hil ▷ R.E j hd₂ ≫
  Iso.hom (associator (R.E i hai) (R.E l hil) (R.E j hd₂))
local notation "a₂" => R.E i hai ◁ R.cross j l hil hd₂ hij hd₃
local notation "b₀" => Iso.inv (associator (R.E l hal) (R.E j hlj) (R.E i hd₁)) ≫
  R.cross j l hal hlj haj hjl ▷ R.E i hd₁ ≫
  Iso.hom (associator (R.E j haj) (R.E l hjl) (R.E i hd₁))
local notation "b₁" => R.E j haj ◁ R.cross i l hjl hd₁ hji hd₃
local notation "b₂" => Iso.inv (associator (R.E j haj) (R.E i hji) (R.E l hd₃)) ≫
  R.cross i j haj hji hai hij ▷ R.E l hd₃ ≫
  Iso.hom (associator (R.E i hai) (R.E j hij) (R.E l hd₃))

/-- Reassociate the six given crossing paths to the literal data field,
before any chosen large action is substituted. -/
theorem rouquierMulticolourBraidEquation_of_paths
    (h : a₀ ≫ a₁ ≫ a₂ = b₀ ≫ b₁ ≫ b₂) :
    rouquierMulticolourBraidEquation D R i j l hal haj hai hlj hli hjl hji hil hij hd₁ hd₂ hd₃ := by
  simpa only [rouquierMulticolourBraidEquation, Category.assoc] using h

end OddMath.QuiverHecke.ELVOld
