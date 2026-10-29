/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.ReservoirPairDots
/-! Centrality of the two Q factors for the reverse reservoir-pair braid. -/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir
open CategoryTheory StringDiagrams OddMath.SKM QCompressedDots Supercategory
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  {D : Datum I X} (Sc : Scalars D k)

/-- The Q norm of two supercommuting dots commutes with their divided-difference crossing.
The commutative realization is generated inside the endomorphism algebra. -/
theorem qExpr_pair_central_reversed
    {C : Type*} [Category C] [Preadditive C] [Linear k C] {A : C}
    (i r : I) (ψ x z y : End A)
    (hxz : z * x = koszulSign (D.parity i) (D.parity i) • (x * z))
    (hxy : y * x = koszulSign (D.parity i) (D.parity r) • (x * y))
    (hzy : y * z = koszulSign (D.parity i) (D.parity r) • (z * y))
    (hψy : y * ψ = koszulSign (D.parity i) (D.parity r) • (ψ * y))
    (h₁ : ψ * x - koszulSign (D.parity i) (D.parity i) • (z * ψ) = 1)
    (h₂ : x * ψ - koszulSign (D.parity i) (D.parity i) • (ψ * z) = 1) :
    Commute ψ (qExpr Sc z y i r ≫ qExpr Sc x y i r : End A) := by
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
  rw [qExpr_pair_eq_eval_product Sc c φ i r Polynomial.X b' a' z x y rfl rfl
    (by change φ ((Polynomial.aeval _) Polynomial.X) = _
        rw [Polynomial.aeval_X]
        rfl)]
  rw [map_mul]
  exact hnorm

section ReservoirPair
variable {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  (P : ProbeReservoir k B D Sc) (i r : I) (t : Sector I)
  (hv : StepValid (true, r) false t)
  (hw : StepValid (true, r) false (nextSector (true, r) false t))
  (Z : P.H (nextSector (true, r) false (nextSector (true, r) false
    (nextSector (true, i) true t))))

/-- The transported two-factor Q weight commutes with the prescribed reservoir crossing. -/
theorem reservoirPairQProduct_central :
    Commute (P.reservoirPairCross i r t hv hw Z)
      (((P.reservoirPairFirstIso i r t hv hw Z).hom ≫
        (P.step (true, r) false t hv).map
          (P.mixedQ i r (nextSector (true, r) false t) hw Z) ≫
        (P.reservoirPairFirstIso i r t hv hw Z).inv) ≫
        P.mixedQ i r t hv (P.reservoirPairRest i r t hw Z)) := by
  let x := P.prPostDot i r t hv (P.reservoirPairRest i r t hw Z)
  let z := P.reservoirPairLastDot i r t hv hw Z
  let y := P.prPreDot i r t hv (P.reservoirPairRest i r t hw Z)
  let ψ := P.reservoirPairCross i r t hv hw Z
  have hxz : z * x = koszulSign (D.parity r) (D.parity r) • (x * z) := by
    have h := P.reservoirPairLastDot_comp_prPostDot i r t hv hw Z
    change x ≫ z = koszulSign (D.parity r) (D.parity r) • (z ≫ x)
    rw [h, smul_smul, koszulSign_mul_self, one_smul]
  have hxy : y * x = koszulSign (D.parity r) (D.parity i) • (x * y) := by
    simpa only [x, y, End.mul_def, koszulSign_comm] using P.reservoirPairFirstDot_comp_probeDot i r t hv hw Z
  have hzy : y * z = koszulSign (D.parity r) (D.parity i) • (z * y) := by
    simpa only [z, y, End.mul_def, koszulSign_comm] using P.reservoirPairLastDot_comp_prPreDot i r t hv hw Z
  have hψy : y * ψ = koszulSign (D.parity r) (D.parity i) • (ψ * y) := by
    simpa only [ψ, y, End.mul_def, koszulSign_comm] using P.reservoirPairCross_comp_prPreDot i r t hv hw Z
  have swap (a : End (P.reservoirPairObj i r t hv hw Z))
      (h : y * a = koszulSign (D.parity r) (D.parity i) • (a * y)) :
      qExpr Sc y a i r = qExpr Sc a y r i := by
    apply qExpr_swap Sc y a i r (zsign k (D.parity i * D.parity r))
    · simpa only [koszulSign_smul_eq_zsign (k := k), mul_comm] using h
    · exact fun n hn => zsign_pow_of_mul_eq_zero _ _ n hn
  rw [P.reservoirPairFirstIso_conj_mixedQ]
  change Commute ψ (qExpr Sc y z i r ≫ qExpr Sc y x i r)
  rw [swap z hzy, swap x hxy]
  exact qExpr_pair_central_reversed Sc r i ψ x z y hxz hxy hzy hψy
    (P.reservoirPairCross_slides i r t hv hw Z).1
    (P.reservoirPairCross_slides i r t hv hw Z).2
end ReservoirPair
end OddMath.QuiverHecke.SwappedAssembly.ProbeReservoir
