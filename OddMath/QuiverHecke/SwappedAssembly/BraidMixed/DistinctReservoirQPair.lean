/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.DistinctReservoirQ
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.DistinctQTransport

/-! # Two Q factors with a shared probe spectator -/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly
open CategoryTheory StringDiagrams OddMath.SKM BicategoryStruct Supercategory
universe u
variable {I X : Type u} [AddCommGroup X] {k : Type u} [CommRing k]
  {B : Type u} [BicategoryStruct.{u, u} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
  [∀ a b : B, PiSupercategory k (a ⟶ b)]
  {D : Datum I X} {Sc : Scalars D k}
namespace ProbeReservoir
variable (P : ProbeReservoir k B D Sc)
variable (i r q : I) (s : Sector I)
  (hr : StepValid (true, r) false s)
  (hq : StepValid (true, q) false (nextSector (true, r) false s))
  (Z : P.H (nextSector (true, q) false (nextSector (true, r) false (nextSector (true, i) true s))))

/-- Both reservoir dots supercommute with the single probe spectator. -/
theorem distinctReservoir_dots_probe :
    let x := P.prPreDot i r s hr (P.distinctReservoirRest i r q s hq Z)
    let y := P.prPostDot i r s hr (P.distinctReservoirRest i r q s hq Z)
    let z := P.distinctReservoirLastDot i r q s hr hq Z
    (y ≫ x = zsign k (D.parity i * D.parity r) • (x ≫ y)) ∧
    (z ≫ x = zsign k (D.parity i * D.parity q) • (x ≫ z)) := by
  have hy := (homContentPostDot_power_supernatural (k := k) P.T.obj P.W r
    (nextSector (true, i) true s).1 (P.muP (nextSector (true, i) true s))
    (P.muM_postE (t := nextSector (true, i) true s) r hr) 1).mem
      (P.distinctReservoirRest i r q s hq Z)
  have hz := (homContentPostDot_power_supernatural (k := k) P.T.obj P.W q
    (nextSector (true, r) false (nextSector (true, i) true s)).1
    (P.muP (nextSector (true, r) false (nextSector (true, i) true s)))
    (P.muM_postE (t := nextSector (true, r) false (nextSector (true, i) true s)) q hq) 1).mem Z
  simp only [Nat.cast_one, one_mul, pow_one] at hy hz
  have hz' := IsSuperfunctor.map_mem (R := k)
    (F := P.step (true, r) false (nextSector (true, i) true s) hr) hz
  constructor
  · have h := TwoSupercategory.super_interchange (R := k) (P.T.dot_mem i (P.muP_preE i s)) hy
    rw [koszulSign_smul_eq_zsign (k := k)] at h
    have h' := congrArg (fun f => zsign k (D.parity i * D.parity r) • f) h
    simp only [smul_smul, zsign_mul_self', one_smul] at h'
    exact h'.symm
  · have h := TwoSupercategory.super_interchange (R := k) (P.T.dot_mem i (P.muP_preE i s)) hz'
    rw [koszulSign_smul_eq_zsign (k := k)] at h
    have h' := congrArg (fun f => zsign k (D.parity i * D.parity q) • f) h
    simp only [smul_smul, zsign_mul_self', one_smul] at h'
    exact h'.symm

/-- The two different reservoir dots supercommute. -/
theorem distinctReservoir_dots_reservoir :
    P.distinctReservoirLastDot i r q s hr hq Z ≫
        P.prPostDot i r s hr (P.distinctReservoirRest i r q s hq Z) =
      zsign k (D.parity q * D.parity r) •
        (P.prPostDot i r s hr (P.distinctReservoirRest i r q s hq Z) ≫
          P.distinctReservoirLastDot i r q s hr hq Z) := by
  have hz := (homContentPostDot_power_supernatural (k := k) P.T.obj P.W q
    (nextSector (true, r) false (nextSector (true, i) true s)).1
    (P.muP (nextSector (true, r) false (nextSector (true, i) true s)))
    (P.muM_postE (t := nextSector (true, r) false (nextSector (true, i) true s)) q hq) 1).mem Z
  simp only [Nat.cast_one, one_mul, pow_one] at hz
  have hy := homContentPostDot_power_supernatural (k := k) P.T.obj P.W r
    (nextSector (true, i) true s).1 (P.muP (nextSector (true, i) true s))
    (P.muM_postE (t := nextSector (true, i) true s) r hr) 1
  simp only [Nat.cast_one, one_mul, pow_one] at hy
  have h := hy.naturality hz
  rw [← koszulSign_smul (R := k), koszulSign_smul_eq_zsign (k := k)] at h
  have h' := congrArg (P.step (true, i) true s trivial).map h
  simp only [Functor.map_comp, Functor.map_smul] at h'
  rw [mul_comm (D.parity r)] at h'
  exact h'

/-- The prescribed Q factors commute, sharing exactly one probe dot. -/
theorem distinctReservoir_qExpr_comm :
    let x := P.prPreDot i r s hr (P.distinctReservoirRest i r q s hq Z)
    let y := P.prPostDot i r s hr (P.distinctReservoirRest i r q s hq Z)
    let z := P.distinctReservoirLastDot i r q s hr hq Z
    qExpr Sc x z i q ≫ qExpr Sc x y i r = qExpr Sc x y i r ≫ qExpr Sc x z i q := by
  dsimp only
  obtain ⟨hy, hz⟩ := P.distinctReservoir_dots_probe i r q s hr hq Z
  rw [qExpr_swap Sc _ _ i q (zsign k (D.parity i * D.parity q)) hz
      (zsign_pow_of_mul_eq_zero _ _),
    qExpr_swap Sc _ _ i r (zsign k (D.parity i * D.parity r)) hy
      (zsign_pow_of_mul_eq_zero _ _)]
  exact qExpr_pair_comp_comm Sc _ _ _ q r i
    (P.distinctReservoir_dots_reservoir i r q s hr hq Z)
    (by simpa only [mul_comm] using hz) (by simpa only [mul_comm] using hy)

/-- The Q factor of the last reservoir moves to the first reservoir position. -/
theorem postCrossNe_qExpr_inner
    (hq' : StepValid (true, q) false s)
    (hr' : StepValid (true, r) false (nextSector (true, q) false s))
    (hrq : r ≠ q)
    (hsP : nextSector (true, q) false (nextSector (true, r) false (nextSector (true, i) true s)) =
      nextSector (true, r) false (nextSector (true, q) false (nextSector (true, i) true s)))
    (Y : P.H (nextSector (true, r) false (nextSector (true, q) false (nextSector (true, i) true s)))) :
    qExpr Sc (P.prPreDot i r s hr (P.distinctReservoirRest i r q s hq (hsP ▸ Y)))
        (P.distinctReservoirLastDot i r q s hr hq (hsP ▸ Y)) i q ≫
        (P.step (true, i) true s trivial).map
          (P.postCrossNe r q (nextSector (true, i) true s) hr hq hq' hr' hsP Y) =
      (P.step (true, i) true s trivial).map
          (P.postCrossNe r q (nextSector (true, i) true s) hr hq hq' hr' hsP Y) ≫
        P.mixedQ i q s hq' (P.distinctReservoirRest i q r s hr' Y) := by
  symm
  apply comp_qExpr (Sc := Sc) _ _ _ _ _ i q
    (zsign k (D.parity i * (D.parity r * D.parity q)))
    (zsign k (D.parity q * D.parity r))
  · have hθ := (P.postCrossNe_supernatural r q (nextSector (true, i) true s)
      hr hq hq' hr' hsP).mem Y
    have h := TwoSupercategory.super_interchange (R := k) (P.T.dot_mem i (P.muP_preE i s)) hθ
    rw [koszulSign_smul_eq_zsign (k := k)] at h
    have h' := congrArg (fun f => zsign k (D.parity i * (D.parity r * D.parity q)) • f) h
    simp only [smul_smul, zsign_mul_self', one_smul] at h'
    exact h'.symm
  · have h := congrArg (P.step (true, i) true s trivial).map
      (P.postCrossNe_slideR r q hrq (nextSector (true, i) true s) hr hq hq' hr' hsP Y)
    simp only [Functor.map_comp, Functor.map_smul] at h
    rw [mul_comm (D.parity r)] at h
    exact h
  · exact zsign_pow_of_mul_eq_zero _ _
  · exact zsign_pow_of_mul_eq_zero _ _

/-- Both different Q factors cross together, in reversed reservoir order. -/
theorem postCrossNe_qExpr_pair
    (hq' : StepValid (true, q) false s)
    (hr' : StepValid (true, r) false (nextSector (true, q) false s))
    (hrq : r ≠ q)
    (hsP : nextSector (true, q) false (nextSector (true, r) false (nextSector (true, i) true s)) =
      nextSector (true, r) false (nextSector (true, q) false (nextSector (true, i) true s)))
    (Y : P.H (nextSector (true, r) false (nextSector (true, q) false (nextSector (true, i) true s)))) :
    (qExpr Sc (P.prPreDot i r s hr (P.distinctReservoirRest i r q s hq (hsP ▸ Y)))
        (P.distinctReservoirLastDot i r q s hr hq (hsP ▸ Y)) i q ≫
      P.mixedQ i r s hr (P.distinctReservoirRest i r q s hq (hsP ▸ Y))) ≫
        (P.step (true, i) true s trivial).map
          (P.postCrossNe r q (nextSector (true, i) true s) hr hq hq' hr' hsP Y) =
      (P.step (true, i) true s trivial).map
          (P.postCrossNe r q (nextSector (true, i) true s) hr hq hq' hr' hsP Y) ≫
        (qExpr Sc (P.prPreDot i q s hq' (P.distinctReservoirRest i q r s hr' Y))
          (P.distinctReservoirLastDot i q r s hq' hr' Y) i r ≫
          P.mixedQ i q s hq' (P.distinctReservoirRest i q r s hr' Y)) := by
  rw [Category.assoc, P.postCrossNe_qExpr_outer i r q s hr hq hq' hr' hrq hsP Y,
    ← Category.assoc, P.postCrossNe_qExpr_inner i r q s hr hq hq' hr' hrq hsP Y,
    Category.assoc]
  congr 1
  exact (P.distinctReservoir_qExpr_comm i q r s hq' hr' Y).symm

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
