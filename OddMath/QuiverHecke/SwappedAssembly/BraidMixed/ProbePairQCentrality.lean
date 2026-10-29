/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.QWeightedPolynomial
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.QWeightedEvaluation
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.QCentralRealization

/-! Compressed-dot realization and reverse probe-pair Q-product centrality.
The ordinary End slides have correction 1 for even probe colour and x₁ - x₂
for odd probe colour. The correction need not commute with the crossing. -/

noncomputable section
namespace QCompressedDots
open StringDiagrams Supercategory
variable {R : Type*} [Ring R]
def compress (p : ZMod 2) (x : R) : R := if p = 1 then x ^ 2 else x

theorem square_commute_of_neg (x y : R) (h : y * x = -(x * y)) :
    Commute (x ^ 2) y := by
  change x ^ 2 * y = y * x ^ 2
  rw [pow_two]
  linear_combination (norm := noncomm_ring) x * h - h * x

theorem compress_commute (p q : ZMod 2) (x y : R)
    (h : y * x = koszulSign p q • (x * y)) :
    Commute (compress p x) (compress q y) := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one q with rfl | rfl
  · simpa [compress, koszulSign, Commute, SemiconjBy] using h.symm
  · simpa [compress] using (show Commute x y from by
      simpa [koszulSign, Commute, SemiconjBy] using h.symm).pow_right 2
  · simpa [compress] using (show Commute x y from by
      simpa [koszulSign, Commute, SemiconjBy] using h.symm).pow_left 2
  · simp [koszulSign] at h
    simpa [compress] using (square_commute_of_neg x y h).pow_right 2

theorem commute_compress (p q : ZMod 2) (x y : R)
    (h : y * x = koszulSign p q • (x * y)) :
    Commute x (compress q y) := by
  rcases parity_eq_zero_or_one p with rfl | rfl <;>
    rcases parity_eq_zero_or_one q with rfl | rfl
  · simpa [compress, koszulSign, Commute, SemiconjBy] using h.symm
  · simpa [compress] using (show Commute x y from by
      simpa [koszulSign, Commute, SemiconjBy] using h.symm).pow_right 2
  · simpa [compress, koszulSign, Commute, SemiconjBy] using h.symm
  · have h' : x * y = -(y * x) := by
      have h : y * x = -(x * y) := by simpa [koszulSign] using h
      rw [h, neg_neg]
    simpa [compress] using (square_commute_of_neg y x h').symm

theorem compress_slides (p : ZMod 2) (ψ x z : R)
    (h₁ : ψ * x - koszulSign p p • (z * ψ) = 1)
    (h₂ : x * ψ - koszulSign p p • (ψ * z) = 1) :
    ψ * compress p x = compress p z * ψ + (if p = 1 then x - z else 1) ∧
    ψ * compress p z = compress p x * ψ - (if p = 1 then x - z else 1) := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · simp [compress, koszulSign] at h₁ h₂ ⊢
    constructor
    · linear_combination (norm := noncomm_ring) h₁
    · linear_combination (norm := noncomm_ring) -h₂
  · have hx : ψ * x + z * ψ = 1 := by simpa [koszulSign] using h₁
    have hz : x * ψ + ψ * z = 1 := by simpa [koszulSign] using h₂
    simpa [compress, pow_two] using QWeightedDraft.odd_square_slides ψ x z hx hz

theorem correction_commute (p : ZMod 2) (x z : R)
    (h : z * x = koszulSign p p • (x * z)) :
    Commute (compress p x) (if p = 1 then x - z else 1) ∧
    Commute (compress p z) (if p = 1 then x - z else 1) := by
  rcases parity_eq_zero_or_one p with rfl | rfl
  · simp [compress]
  · have h : z * x = -(x * z) := by simpa [koszulSign] using h
    have h' : x * z = -(z * x) := by rw [h, neg_neg]
    constructor
    · simpa [compress] using ((Commute.refl x).pow_left 2).sub_right
        (square_commute_of_neg x z h)
    · simpa [compress] using (square_commute_of_neg z x h').sub_right
        ((Commute.refl z).pow_left 2)
end QCompressedDots

namespace OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir
open CategoryTheory StringDiagrams OddMath.SKM QCompressedDots Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  {D : Datum I X} (Sc : Scalars D k)

/-- The Q norm of two supercommuting dots commutes with their divided-difference crossing.
The commutative realization is generated inside the endomorphism algebra. -/
theorem qExpr_pair_central
    {C : Type*} [Category C] [Preadditive C] [Linear k C] {A : C}
    (i r : I) (ψ x z y : End A)
    (hxz : z * x = koszulSign (D.parity i) (D.parity i) • (x * z))
    (hxy : y * x = koszulSign (D.parity i) (D.parity r) • (x * y))
    (hzy : y * z = koszulSign (D.parity i) (D.parity r) • (z * y))
    (hψy : y * ψ = koszulSign (D.parity i) (D.parity r) • (ψ * y))
    (h₁ : ψ * x - koszulSign (D.parity i) (D.parity i) • (z * ψ) = 1)
    (h₂ : x * ψ - koszulSign (D.parity i) (D.parity i) • (ψ * z) = 1) :
    Commute ψ (qExpr Sc x y i r ≫ qExpr Sc z y i r : End A) := by
  let a := compress (D.parity i) x
  let b := compress (D.parity i) z
  let v := compress (D.parity r) y
  let d := if D.parity i = 1 then x - z else 1
  have hab : Commute a b := compress_commute _ _ _ _ hxz
  have hav : Commute a v := compress_commute _ _ _ _ hxy
  have hbv : Commute b v := compress_commute _ _ _ _ hzy
  obtain ⟨had, hbd⟩ := correction_commute _ _ _ hxz
  have hvd : Commute v d := by
    dsimp [d]
    split_ifs
    · exact ((commute_compress _ _ _ _ hxy).symm).sub_right
        (commute_compress _ _ _ _ hzy).symm
    · exact Commute.one_right v
  let := QCentralRealization.commRing (k := k) a b v d hab hav had hbv hbd hvd
  let S := QCentralRealization.carrier (k := k) a b v d
  let φ : S →ₐ[k] End A := (QCentralRealization.carrier (k := k) a b v d).val
  let c : Polynomial k →ₐ[k] S := Polynomial.aeval (QCentralRealization.spectator k a b v d)
  let a' := QCentralRealization.pointA k a b v d
  let b' := QCentralRealization.pointB k a b v d
  let d' := QCentralRealization.correction k a b v d
  have hc (f : Polynomial k) : ψ * φ (c f) = φ (c f) * ψ :=
    (QCentralRealization.commute_coefficients k a b v d ψ
      (commute_compress _ _ _ _ hψy) f).eq
  obtain ⟨ha, hb⟩ := compress_slides _ _ _ _ h₁ h₂
  have hnorm := QWeightedDraft.polynomial_norm c.toRingHom φ.toRingHom ψ a' b' d'
    hc ha hb (qCoefficientPolynomial Sc i r (Polynomial.X : Polynomial k))
  rw [qExpr_pair_eq_eval_product Sc c φ i r Polynomial.X a' b' x z y rfl rfl
    (by change φ ((Polynomial.aeval _) Polynomial.X) = _
        rw [Polynomial.aeval_X]
        rfl)]
  rw [mul_comm ((qCoefficientPolynomial Sc i r Polynomial.X).eval₂ c.toRingHom b'), map_mul]
  exact hnorm

section ProbePair
variable {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  (P : ProbeReservoir k B D Sc) (i r : I) (s : Sector I)
  (hR : StepValid (true, r) false s)
  (Z : P.H (nextSector (true, r) false
    (nextSector (true, i) true (nextSector (true, i) true s))))

/-- The transported reverse probe-pair Q product commutes with the same-colour crossing.
No Q value is inverted and no commutative realization or centrality is assumed. -/
theorem probePairQProduct_central :
    Commute
      (P.preCrossSame i s ((P.step (true, r) false
        (nextSector (true, i) true (nextSector (true, i) true s)) hR).obj Z))
      (((P.probePairFirstIso i r s hR Z).hom ≫
        P.mixedQ i r s hR ((P.step (true, i) true
          (nextSector (true, r) false (nextSector (true, i) true s)) trivial).obj Z) ≫
        (P.probePairFirstIso i r s hR Z).inv) ≫
        (P.step (true, i) true s trivial).map
          (P.mixedQ i r (nextSector (true, i) true s) hR Z)) := by
  rw [P.probePairFirstIso_conj_mixedQ, P.probePair_map_mixedQ]
  apply qExpr_pair_central Sc i r
  · exact TwoSupercategory.super_interchange (R := k) (P.T.dot_mem i _)
      (TwoSupercategory.whiskerRight_mem _ (P.T.dot_mem i _))
  · exact P.ppLeftDot_comp_probePairSpectatorDot i r s hR Z
  · exact P.ppRightDot_comp_probePairSpectatorDot i r s hR Z
  · exact P.preCrossSame_comp_probePairSpectatorDot i r s hR Z
  · exact (P.preCrossSame_slides i s _).1
  · exact (P.preCrossSame_slides i s _).2
end ProbePair
end OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir

