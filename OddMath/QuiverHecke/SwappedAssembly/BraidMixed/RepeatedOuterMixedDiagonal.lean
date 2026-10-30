/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.RepeatedOuterOtherPlacements

/-! # Single-edge coefficients for the repeated-outer mixed diagonal

Supporting the `Pᵢ Pⱼ Rᵢ` diagonal in Brundan–Ellis (1.9). The actual probe
edge transports conjugated coefficients. Removing the last mixed comparison
from the proved adjacent rectangle cancels only an isomorphism, never a probe
crossing or Q. The underlying coefficient rectangle uses the supplied inverse
identities and the established denominator unit. This is not yet the diagonal
finite-sum correction equation.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u

private lemma single_coeff {C : Type u} [Category C]
    {A B T V W : C} (J : A ≅ B) (H : V ≅ W) (K : T ≅ V)
    (a : End B) (b : End W) (M : B ⟶ W) (f : A ⟶ T)
    (ha : a ≫ M = M ≫ b) (hj : J.hom ≫ M = (f ≫ K.hom) ≫ H.hom) :
    (J.hom ≫ a ≫ J.inv) ≫ f =
      f ≫ (K.hom ≫ H.hom ≫ b ≫ H.inv ≫ K.inv) := by
  have hu := ProbeReservoir.splitMatrix_inv_rectangle J H M (f ≫ K.hom) hj
  have hu' := congrArg (fun g => g ≫ H.hom) hu
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hu'
  apply (cancel_mono (K.hom ≫ H.hom)).1
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hu', ha, ← Category.assoc J.hom, hj]
  simp only [Category.assoc]

private lemma normalized_signed_slide {k : Type u} [CommRing k]
    {C : Type u} [Category C] [Preadditive C] [Linear k C]
    {A B : C} (a : End A) (b : End B) (f : A ⟶ B) (q ε : k)
    (hε : ε * ε = 1) (h : a ≫ f = f ≫ b) :
    (q • a) ≫ f = ε • (f ≫ ((ε * q) • b)) := by
  rw [Linear.smul_comp, h, Linear.comp_smul, smul_smul, ← mul_assoc, hε, one_mul]

variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc) (i j : I) (s : Sector I)
  (hR : StepValid (true, i) false s)
  (hs₀ : nextSector (true, i) true (nextSector (true, j) true s) =
    nextSector (true, j) true (nextSector (true, i) true s))
  (hs : nextSector (true, i) true (nextSector (true, j) true (nextSector (true, i) false s)) =
    nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s)))
  (Z : P.H (nextSector (true, j) true (nextSector (true, i) true (nextSector (true, i) false s))))

/-- The unsigned conjugated coefficient at the adjacent source `Pⱼ Pᵢ Rᵢ`. -/
def repeatedOuterMixedAdjacentCoeff (c : P.CrossCoeff Sc) :=
  (P.step (true, j) true s trivial).map
    (P.mixedJ i i (nextSector (true, j) true s) hR ((P.castH hs).obj Z)).hom ≫
  (P.step (true, j) true s trivial).map
    (c.a i (nextSector (true, j) true s) hR ((P.castH hs).obj Z)) ≫
  (P.step (true, j) true s trivial).map
    (P.mixedJ i i (nextSector (true, j) true s) hR ((P.castH hs).obj Z)).inv

/-- The unsigned conjugated coefficient on the separated strands `Pᵢ Pⱼ Rᵢ`. -/
def repeatedOuterMixedSeparatedCoeff (c : P.CrossCoeff Sc) :=
  (P.distinctProbeFirstIso i j i s hR Z).hom ≫
    (P.mixedJ i i s hR ((P.step (true, j) true _ trivial).obj Z)).hom ≫
    c.a i s hR ((P.step (true, j) true _ trivial).obj Z) ≫
    (P.mixedJ i i s hR ((P.step (true, j) true _ trivial).obj Z)).inv ≫
    (P.distinctProbeFirstIso i j i s hR Z).inv

/-- One actual probe edge, with its explicit terminal transport, carries the
raw conjugated coefficient. No coefficient slide or braid is assumed. -/
theorem repeatedOuterMixed_probe_coeff (c : P.CrossCoeff Sc) (hc : c.IsInverse)
    (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    P.repeatedOuterMixedAdjacentCoeff i j s hR hs Z c ≫
        P.adjacentReverseProbeCross i j s hR hs₀ Z =
      P.adjacentReverseProbeCross i j s hR hs₀ Z ≫
        P.repeatedOuterMixedSeparatedCoeff i j s hR Z c := by
  let K := P.distinctProbeFirstIso i j i s hR Z
  have he := P.adjacentReverseMove_coeff c hc h i j s hR hs Z hij
  have hj := (P.adjacentReverse_J_rectangle i j s hR hs₀ hs Z).trans
    (Category.assoc _ _ _).symm
  let J := (P.step (true, j) true s trivial).mapIso
    (P.mixedJ i i (nextSector (true, j) true s) hR ((P.castH hs).obj Z))
  let A := (P.step (true, j) true s trivial).map
    (c.a i (nextSector (true, j) true s) hR ((P.castH hs).obj Z))
  let H := P.mixedJ i i s hR ((P.step (true, j) true _ trivial).obj Z)
  let B := c.a i s hR ((P.step (true, j) true _ trivial).obj Z)
  have he' := single_coeff J H K A B (P.adjacentReverseMove i j s hR hs Z)
    (P.adjacentReverseProbeCross i j s hR hs₀ Z) he hj
  exact he'

/-- With the physical-dot normalization, the single edge has the Koszul sign.
The source normalization is `(-1)^pᵢ`, and the separated target normalization
is `(-1)^(pᵢ+pᵢpⱼ)`. Both total parities are retained. -/
theorem repeatedOuterMixed_probe_coeff_signed (c : P.CrossCoeff Sc) (hc : c.IsInverse)
    (h : P.CrossCoeffInputs) (hij : i ≠ j) :
    (zsign k (D.parity i) • P.repeatedOuterMixedAdjacentCoeff i j s hR hs Z c) ≫
        P.adjacentReverseProbeCross i j s hR hs₀ Z =
      zsign k (D.parity i * D.parity j) •
        (P.adjacentReverseProbeCross i j s hR hs₀ Z ≫
          ((zsign k (D.parity i * D.parity j) * zsign k (D.parity i)) •
            P.repeatedOuterMixedSeparatedCoeff i j s hR Z c)) := by
  exact normalized_signed_slide _ _ _ _ _ (zsign_mul_self' _)
    (P.repeatedOuterMixed_probe_coeff i j s hR hs₀ hs Z c hc h hij)

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
