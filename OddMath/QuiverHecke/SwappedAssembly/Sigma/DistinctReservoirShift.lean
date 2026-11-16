import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.InterchangePostPair
import OddMath.SKM.RouquierHomDistinctPostShift
/-! # Parity comparison for the distinct reservoir crossing

Brundan–Ellis (1.11), MixedColourBlockCompletion §2 (3)–(4):
the prescribed even beta/xi comparison agrees with the shifted
factor crossing used in the pure reservoir mate. The comparison
retains the forced homogeneous naturality sign.
-/
noncomputable section
open CategoryTheory StringDiagrams BicategoryStruct Supercategory OddMath.SKM
namespace OddMath.QuiverHecke.SwappedAssembly
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]

/-- The even pair comparison transports a homogeneous factor crossing
by the successive parity removals, with the forced naturality sign. -/
theorem postPairCrossing_eq {a b c d x : B} {E₁ : a ⟶ b} {E₂ : d ⟶ c}
    {E₃ : a ⟶ d} {E₄ : b ⟶ c} {r : ZMod 2} (p q : ZMod 2)
    (t : E₃ ≫ E₂ ⟶ E₁ ≫ E₄) (ht : t ∈ parity (R := k) _ _ r) (Z : x ⟶ a) :
    (ProbeReservoir.postPairIso (k := k) E₂ Z E₃ p q).hom ≫
      (homParityShift (k := k) (q + p)).map
        ((associator Z E₃ E₂).hom ≫ Z ◁ t ≫ (associator Z E₁ E₄).inv) ≫
      eqToHom (by rw [add_comm]) ≫
      (ProbeReservoir.postPairIso (k := k) E₄ Z E₁ q p).inv =
    sign k ((q + p) * r) • homShiftedPostCrossing p q t Z := by
  rw [postPairIso_cross_remove E₃ E₂ E₁ E₄ q p Z ht]
  simp only [homPostPairRemoval, Iso.trans_hom, Iso.trans_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, homPost, homShiftedPostCrossing, Category.assoc]

end OddMath.QuiverHecke.SwappedAssembly
