/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.PsiCrossings
import OddMath.SKM.PsiAdjunctions

/-!
# Inverse coefficients and double shifts for ψ

Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2,
Proposition 9.4 and Lemma 9.1. The inverse upward assignments use the opposite
square root: the coefficients for `t` and `-t` cancel, whereas repeating `t`
produces a parity sign. We check this on the existing dot-power and crossing
assignments. The signed shift assignment is an involution on the existing
1-morphisms of `Uqπ`, compatible with their identity and composition.

The odd shift structure also needs attention: applying `oddSOpIso` twice
negates both structure maps. These calculations are inputs to the literal
inverse comparison for Proposition 9.4, not identities of assembled
2-superfunctors. We also compute the complete parity-shift conjugation and its
action on the assigned cups/caps. The remaining inverse comparison still needs
the forward functor on the original left cups/caps, the integer-shift portion,
and the identification of these structure maps with the full extension.
-/

noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Supercategory
universe u v w

/-- Changing the sign of the chosen square root preserves its defining equation. -/
theorem psi_neg_sq {k : Type w} [CommRing k] {t : k} (ht : t ^ 2 = -1) :
    (-t) ^ 2 = -1 := by simpa using ht

/-- The inverse coefficient uses the opposite square root. -/
theorem psiCoeff_neg_mul {k : Type w} [CommRing k] {t : k} (ht : t ^ 2 = -1)
    (p : ZMod 2) : psiCoeff (-t) p * psiCoeff t p = 1 := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp [← pow_two, ht]

/-- Using the same square root twice leaves the parity sign. -/
theorem psiCoeff_mul_self {k : Type w} [CommRing k] {t : k} (ht : t ^ 2 = -1)
    (p : ZMod 2) : psiCoeff t p * psiCoeff t p = sign k p := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    simp [← pow_two, ht]

variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

/-- The shift assignment of Proposition 9.4, forgetting the super-opposite wrapper.
This is a map of 1-morphisms only, not an assumed 2-superfunctor. -/
def psiShift {a b : Uqπ D Sc sy hc} (f : a ⟶ b) : a ⟶ b :=
  ⟨f.par + psiParity f.obj.obj, ⟨-f.obj.shift, f.obj.obj⟩⟩

/-- The shift assignment agrees with the unshifted word assignment already used by ψ. -/
theorem psiShift_word {a b : UGr D Sc sy hc} (f : a ⟶ b) :
    psiShift (Envelope.mk 0 (QEnvelope.mk 0 f) :
      (⟨⟨a⟩⟩ : Uqπ D Sc sy hc) ⟶ ⟨⟨b⟩⟩) = SOp.unop (psiMap f) := by
  simp only [psiShift, psiMap, zero_add, neg_zero]

/-- Integer shifts and the downward-word parity shifts both cancel on repetition. -/
@[simp] theorem psiShift_involutive {a b : Uqπ D Sc sy hc} (f : a ⟶ b) :
    psiShift (psiShift f) = f := by
  rcases f with ⟨p, m, f⟩
  simp only [psiShift, neg_neg]
  have hp : psiParity f + psiParity f = 0 := by
    rcases parity_eq_zero_or_one (psiParity f) with h | h <;> simp [h, show (1 : ZMod 2) + 1 = 0 from rfl]
  simp only [add_assoc, hp, add_zero]

@[simp] theorem psiShift_id (a : Uqπ D Sc sy hc) : psiShift (𝟙 a) = 𝟙 a := by
  rfl

/-- Composition compatibility on the existing envelope words. -/
theorem psiShift_comp {a b c : Uqπ D Sc sy hc} (f : a ⟶ b) (g : b ⟶ c) :
    psiShift (f ≫ g) = psiShift f ≫ psiShift g := by
  change Envelope.mk ((f.par + g.par) + psiParity (f.obj.obj ≫ g.obj.obj))
      (QEnvelope.mk (-(f.obj.shift + g.obj.shift)) (f.obj.obj ≫ g.obj.obj)) =
    Envelope.mk ((f.par + psiParity f.obj.obj) + (g.par + psiParity g.obj.obj))
      (QEnvelope.mk (-f.obj.shift + -g.obj.shift) (f.obj.obj ≫ g.obj.obj))
  rw [psiParity_comp, neg_add]
  congr 1
  abel

/-- The parity factor in the envelope composition comparison after two shift
assignments. The remaining factor records the downward-word parity; it must
not be discarded when comparing the extended 2-superfunctors. -/
theorem psiShift_comparison_sign {a b c : Uqπ D Sc sy hc}
    (f : a ⟶ b) (g : b ⟶ c) :
    sign k ((psiShift f).par * (psiShift g).par) * sign k (f.par * g.par) =
      sign k (f.par * psiParity g.obj.obj + psiParity f.obj.obj * g.par +
        psiParity f.obj.obj * psiParity g.obj.obj) := by
  change sign k ((f.par + psiParity f.obj.obj) * (g.par + psiParity g.obj.obj)) *
    sign k (f.par * g.par) = _
  have he : (f.par + psiParity f.obj.obj) * (g.par + psiParity g.obj.obj) =
      f.par * g.par + (f.par * psiParity g.obj.obj + psiParity f.obj.obj * g.par +
        psiParity f.obj.obj * psiParity g.obj.obj) := by ring
  rw [he, sign_add]
  rw [mul_right_comm, sign_mul_self, one_mul]

/-- Both choices of square root undo the other on every assigned dot power.
The equation is in the original target hom space after unwrapping the reversal. -/
theorem psiDots_inverse_coeff (t : k) (ht : t ^ 2 = -1) (μ : X) (i : I) (n : ℕ) :
    psiCoeff (-t) (n * D.parity i) •
      SOp.unsop (psiDots (Sc := Sc) (sy := sy) (hc := hc) t μ i n) =
    cl D Sc μ [up i] [up i] (dotsL [] i [] n) := by
  change psiCoeff (-t) (n * D.parity i) •
    (psiCoeff t (n * D.parity i) • _) = _
  rw [smul_smul, psiCoeff_neg_mul ht, one_smul]

/-- Repeating the same upward dot coefficient gives the parity automorphism,
not the identity formula required of an inverse. -/
theorem psiDots_same_coeff (t : k) (ht : t ^ 2 = -1) (μ : X) (i : I) (n : ℕ) :
    psiCoeff t (n * D.parity i) •
      SOp.unsop (psiDots (Sc := Sc) (sy := sy) (hc := hc) t μ i n) =
    sign k (n * D.parity i) • cl D Sc μ [up i] [up i] (dotsL [] i [] n) := by
  change psiCoeff t (n * D.parity i) •
    (psiCoeff t (n * D.parity i) • _) = _
  rw [smul_smul, psiCoeff_mul_self ht]

/-- Inverse coefficient cancellation for the assigned reverse crossing. -/
theorem psiCross_inverse_coeff (t : k) (ht : t ^ 2 = -1) (ν μ : X) (i j : I)
    (h : wt D μ [up i, up j] = ν) :
    psiCoeff (-t) (D.parity i * D.parity j) •
      SOp.unsop (psiCross (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j h) =
    cl D Sc μ [up j, up i] [up i, up j] (crossL [] j i []) := by
  change psiCoeff (-t) (D.parity i * D.parity j) •
    (psiCoeff t (D.parity i * D.parity j) • _) = _
  rw [smul_smul, psiCoeff_neg_mul ht, one_smul]

section OddShift
variable {C : Type*} [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
  {A B : C} (e : A ≅ B) (he : e.hom ∈ parity (R := k) A B 1)

/-- The twice-reversed odd shift has negative underlying forward map.
The canonical double-super-opposite unwrapping alone does not remove this sign. -/
theorem oddSOpIso_twice_hom :
    SOp.unsop (SOp.unsop
      (oddSOpIso (oddSOpIso e he) (by
        exact SOp.mem_parity_iff.mpr (inv_mem e he))).hom) = -e.hom := rfl

/-- The inverse map of the twice-reversed odd shift has the same correction. -/
theorem oddSOpIso_twice_inv :
    SOp.unsop (SOp.unsop
      (oddSOpIso (oddSOpIso e he) (by
        exact SOp.mem_parity_iff.mpr (inv_mem e he))).inv) = -e.inv := rfl

end OddShift

/-- For the target of ψ itself, twice reversing the Π structure negates ζ.
This is the structure correction needed in the envelope inverse comparison. -/
theorem psiEnvelope_twice_zeta_hom (a : Uqπ D Sc sy hc) :
    SOp.unsop (SOp.unsop
      (PiTwoSupercategory.ζ (R := k)
        (⟨⟨a⟩⟩ : TwoSOp k (TwoSOp k (Uqπ D Sc sy hc)))).hom) =
      -(PiTwoSupercategory.ζ (R := k) a).hom :=
  oddSOpIso_twice_hom _ (PiTwoSupercategory.ζ_hom_mem a)

/-- The inverse Π structure map has the same double-reversal correction. -/
theorem psiEnvelope_twice_zeta_inv (a : Uqπ D Sc sy hc) :
    SOp.unsop (SOp.unsop
      (PiTwoSupercategory.ζ (R := k)
        (⟨⟨a⟩⟩ : TwoSOp k (TwoSOp k (Uqπ D Sc sy hc)))).inv) =
      -(PiTwoSupercategory.ζ (R := k) a).inv :=
  oddSOpIso_twice_inv _ (PiTwoSupercategory.ζ_hom_mem a)

section PiCorrection
open BicategoryStruct

variable {a b : UGr D Sc sy hc}
local instance : PiSupercategory k (psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) :=
  PiTwoSupercategory.homPiLeft _ _

/-- The actual Π-shift isomorphism in the hom Π-category used by Lemma 9.1. -/
def psiPiIso (p : ZMod 2) (f : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) :=
  Envelope.ζPow k p f

private theorem psiPiIso_hom (p : ZMod 2)
    (f : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) :
    HEq (QPiTwoEnvelope.toHom (SOp.unsop (psiPiIso p f).hom))
      (𝟙 (SOp.unop f).obj.obj) := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rfl
  · change HEq (QPiTwoEnvelope.toHom (SOp.unsop
      (f ◁ (PiTwoSupercategory.ζ (R := k) (psiObj b)).hom ≫
        (rightUnitor f).hom))) _
    rw [SOp.comp_of_mem (SOp.mem_parity_iff.mp (TwoSupercategory.whiskerLeft_mem f
      (PiTwoSupercategory.ζ_hom_mem _))) (SOp.mem_parity_iff.mp
        (TwoSupercategory.rightUnitor_hom_mem f))]
    simp only [mul_zero, sign_zero, one_smul, TwoSOp.unsop_rightUnitor_hom,
      TwoSOp.unsop_whiskerLeft]
    change HEq (QEnvelope.toHom (Envelope.toHom
      ((rightUnitor (SOp.unop f)).inv ≫ (SOp.unop f) ◁
        (show PiTwoSupercategory.pi (R := k) (⟨⟨b⟩⟩ : Uqπ D Sc sy hc) ⟶ 𝟙 _ from
          (PiTwoSupercategory.ζ (R := k) (⟨⟨b⟩⟩ : Uqπ D Sc sy hc)).inv)))) _
    change HEq (QEnvelope.toHom ((rightUnitor (SOp.unop f).obj).inv ≫
      (SOp.unop f).obj ◁ twist k (SOp.unop f).par (𝟙 _))) _
    rw [twist_id]
    change HEq ((rightUnitor (SOp.unop f).obj.obj).inv ≫
      (SOp.unop f).obj.obj ◁ 𝟙 _) _
    erw [TwoSupercategory.whiskerLeft_id (R := k), Category.comp_id]
    exact eqToHom_heq_id_dom _ _ (congrArg (pres D Sc).obj (Obj.tensor_nil _ _).symm)

/-- The shift adds only an empty word, with its literal boundary equality. -/
theorem psiPiIso_obj (p : ZMod 2)
    (f : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) :
    (SOp.unop (Envelope.piPow (B := psiObj a ⟶ psiObj b) k p f)).obj.obj.obj = (SOp.unop f).obj.obj.obj := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · rfl
  · exact Obj.tensor_nil _ _

/-- Unwrapping the forward Π-shift leaves its boundary transport, with no sign. -/
theorem psiPiIso_hom_eq (p : ZMod 2)
    (f : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) :
    QPiTwoEnvelope.toHom (SOp.unsop (psiPiIso p f).hom) =
      eqToHom (congrArg (pres D Sc).obj (psiPiIso_obj p f).symm) := by
  exact eq_of_heq ((psiPiIso_hom p f).trans (eqToHom_heq_id_dom (C := (pres D Sc).Presented) _ _
    (congrArg (pres D Sc).obj (psiPiIso_obj p f).symm)).symm)

/-- Unwrapping the inverse Π-shift contributes the parity sign. -/
theorem psiPiIso_inv_eq (p : ZMod 2)
    (f : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b) :
    QPiTwoEnvelope.toHom (SOp.unsop (psiPiIso p f).inv) =
      sign k p • eqToHom (congrArg (pres D Sc).obj (psiPiIso_obj p f)) := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · simp only [sign_zero, one_smul]
    rfl
  · change QPiTwoEnvelope.toHom (SOp.unsop
      ((rightUnitor f).inv ≫ f ◁ (PiTwoSupercategory.ζ (R := k) (psiObj b)).inv)) = _
    rw [SOp.comp_of_mem (SOp.mem_parity_iff.mp (inv_mem (rightUnitor f) (TwoSupercategory.rightUnitor_hom_mem f)))
      (SOp.mem_parity_iff.mp (TwoSupercategory.whiskerLeft_mem f
        (PiTwoSupercategory.ζ_inv_mem _)))]
    simp only [zero_mul, sign_zero, one_smul, TwoSOp.unsop_rightUnitor_inv,
      TwoSOp.unsop_whiskerLeft]
    change QEnvelope.toHom ((SOp.unop f).obj ◁
      twist k (SOp.unop f).par (-𝟙 _) ≫ (rightUnitor (SOp.unop f).obj).hom) = _
    rw [map_neg, twist_id]
    change ((SOp.unop f).obj.obj ◁ (-𝟙 _) ≫ (rightUnitor (SOp.unop f).obj.obj).hom) = _
    erw [TwoSupercategory.whiskerLeft_neg (R := k),
      TwoSupercategory.whiskerLeft_id (R := k), Preadditive.neg_comp, Category.id_comp]
    simp only [sign_one, neg_one_smul]
    rfl

/-- Conjugation by the actual Π-shift structure maps in the ψ target.
This is the parity-shift portion of the envelope extension, not a new functor. -/
def psiPiConjugate (p q : ZMod 2)
    {f g : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b} (x : f ⟶ g) :=
  (psiPiIso p f).hom ≫ x ≫ (psiPiIso q g).inv

/-- Complete sign and boundary transports for the parity-shift conjugation. -/
theorem psiPiConjugate_eq (p q r : ZMod 2)
    {f g : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b}
    {x : f ⟶ g} (hx : x ∈ parity (R := k) _ _ r) :
    QPiTwoEnvelope.toHom (SOp.unsop (psiPiConjugate p q x)) =
      sign k (p * r + (p + r) * q + q) •
        (eqToHom (congrArg (pres D Sc).obj (psiPiIso_obj q g)) ≫
          QPiTwoEnvelope.toHom (SOp.unsop x) ≫
          eqToHom (congrArg (pres D Sc).obj (psiPiIso_obj p f).symm)) := by
  have hp := Envelope.ζPow_hom_mem (R := k) p f
  have hq := Envelope.ζPow_inv_mem (R := k) q g
  unfold psiPiConjugate
  rw [← Category.assoc]
  erw [SOp.comp_of_mem (SOp.mem_parity_iff.mp (comp_mem hp hx))
    (SOp.mem_parity_iff.mp hq), SOp.comp_of_mem (SOp.mem_parity_iff.mp hp)
    (SOp.mem_parity_iff.mp hx)]
  change sign k ((p + r) * q) •
    (QPiTwoEnvelope.toHom (SOp.unsop (psiPiIso q g).inv) ≫
      (sign k (p * r) • (QPiTwoEnvelope.toHom (SOp.unsop x) ≫
        QPiTwoEnvelope.toHom (SOp.unsop (psiPiIso p f).hom)))) = _
  rw [psiPiIso_inv_eq, psiPiIso_hom_eq, Linear.smul_comp, Linear.comp_smul,
    smul_smul, smul_smul]
  rw [← sign_add, ← sign_add]
  congr 2
  abel

private theorem smul_transport_heq {C : Type*} [Category C] [Preadditive C] [Linear k C]
    {A B A' B' : C} (hA : A' = A) (hB : B = B') (x : A ⟶ B) (c : k) :
    HEq (c • (eqToHom hA ≫ x ≫ eqToHom hB)) (c • x) := by
  subst hA
  subst hB
  simp

/-- The same formula with the word-boundary transports removed by heterogeneous equality. -/
theorem psiPiConjugate_heq (p q r : ZMod 2)
    {f g : psiObj (Sc := Sc) (sy := sy) (hc := hc) a ⟶ psiObj b}
    {x : f ⟶ g} (hx : x ∈ parity (R := k) _ _ r) :
    HEq (QPiTwoEnvelope.toHom (SOp.unsop (psiPiConjugate p q x)))
      (sign k (p * r + (p + r) * q + q) • QPiTwoEnvelope.toHom (SOp.unsop x)) :=
  (heq_of_eq (psiPiConjugate_eq p q r hx)).trans (smul_transport_heq _ _ _ _)

/-- Applied to the actual cup assignment, the correction is `(-1)^(pq+q)`
on the left cap. In particular a target shift alone contributes its parity sign. -/
theorem psiCup_piConjugate (cs : CScalars Sc) (μ : X) (i : I) (p q : ZMod 2) :
    HEq (QPiTwoEnvelope.toHom (SOp.unsop
      (psiPiConjugate p q (psiCup (sy := sy) (hc := hc) cs μ i))))
      (sign k (p * q + q) • epsP cs i μ) := by
  have h := psiPiConjugate_heq p q 0 (psiCup_mem_parity (sy := sy) (hc := hc) cs μ i)
  change HEq _ (sign k (p * 0 + (p + 0) * q + q) • epsP cs i μ) at h
  simpa only [mul_zero, add_zero, zero_add] using h

/-- Applied to the actual cap assignment, the correction is `(-1)^(pq+q+ipar)`
on the left cup, including the coefficient of Proposition 9.4. -/
theorem psiCap_piConjugate (cs : CScalars Sc) (μ : X) (i : I) (p q : ZMod 2) :
    HEq (QPiTwoEnvelope.toHom (SOp.unsop
      (psiPiConjugate p q (psiCap (sy := sy) (hc := hc) cs μ i))))
      (sign k (p * q + q + ipar D i μ) • etaP cs i μ) := by
  have h := psiPiConjugate_heq p q 0 (psiCap_mem_parity (sy := sy) (hc := hc) cs μ i)
  change HEq _ (sign k (p * 0 + (p + 0) * q + q) •
    (sign k (ipar D i μ) • etaP cs i μ)) at h
  simpa only [mul_zero, add_zero, zero_add, smul_smul, ← sign_add] using h

end PiCorrection
end OddMath.SKM
