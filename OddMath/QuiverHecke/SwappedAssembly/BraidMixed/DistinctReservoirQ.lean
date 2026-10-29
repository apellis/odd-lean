/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.DistinctReservoirSector
import OddMath.QuiverHecke.SwappedAssembly.BraidMixed.ReservoirPairDots

/-! # Q transport for unequal reservoir colours

The mixed comparison and the reservoir crossing retain their prescribed signs.
Supported powers of the parameter polynomial remove these signs; no polynomial
or reservoir crossing is cancelled.
-/
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

/-- The last reservoir object on the path with the probe first. -/
abbrev distinctReservoirRest :=
  (P.step (true, q) false (nextSector (true, r) false (nextSector (true, i) true s)) hq).obj Z

/-- The first mixed comparison on the unequal-reservoir path. -/
def distinctReservoirFirstIso := P.mixedJ i r s hr (P.distinctReservoirRest i r q s hq Z)

/-- The last reservoir dot, with the probe and first reservoir as spectators. -/
def distinctReservoirLastDot : End (P.prObj i r s hr (P.distinctReservoirRest i r q s hq Z)) :=
  (P.step (true, i) true s trivial).map
    ((P.step (true, r) false (nextSector (true, i) true s) hr).map
      (P.dotDiag q false (nextSector (true, r) false (nextSector (true, i) true s)) hq Z))

/-- The last dot passes through the mixed comparison with its full triple parity. -/
theorem distinctReservoirLastDot_comp_firstIso :
    P.distinctReservoirLastDot i r q s hr hq Z ≫ (P.distinctReservoirFirstIso i r q s hr hq Z).hom =
      koszulSign (D.parity i * D.parity r) (D.parity q) •
        ((P.distinctReservoirFirstIso i r q s hr hq Z).hom ≫
          (P.step (true, r) false s hr).map
            (P.prPostDot i q (nextSector (true, r) false s) hq Z)) := by
  have hθ := (homContentPostDot_power_supernatural (k := k) P.T.obj P.W q
    (nextSector (true, r) false (nextSector (true, i) true s)).1
    (P.muP (nextSector (true, r) false (nextSector (true, i) true s)))
    (P.muM_postE (t := nextSector (true, r) false (nextSector (true, i) true s)) q hq) 1).mem Z
  simp only [Nat.cast_one, one_mul, pow_one] at hθ
  have h := (P.mixedJ_supernatural i r s hr).naturality hθ
  rw [← koszulSign_smul (R := k)] at h
  exact h

/-- Conjugation preserves the Q factor of the second reservoir colour. -/
theorem distinctReservoirFirstIso_conj_mixedQ :
    (P.distinctReservoirFirstIso i r q s hr hq Z).hom ≫
      (P.step (true, r) false s hr).map
        (P.mixedQ i q (nextSector (true, r) false s) hq Z) ≫
      (P.distinctReservoirFirstIso i r q s hr hq Z).inv =
    qExpr Sc (P.prPreDot i r s hr (P.distinctReservoirRest i r q s hq Z))
      (P.distinctReservoirLastDot i r q s hr hq Z) i q := by
  let J := P.distinctReservoirFirstIso i r q s hr hq Z
  let ε := zsign k (D.parity i * D.parity r)
  let δ := zsign k (D.parity q * (D.parity i * D.parity r))
  have hx := P.prPreDot_comp_mixedJ_ne i r s hr (P.distinctReservoirRest i r q s hq Z)
  have hx' := congrArg (fun f => ε • f) hx
  simp only [ε, smul_smul, zsign_mul_self', one_smul] at hx'
  have hy := P.distinctReservoirLastDot_comp_firstIso i r q s hr hq Z
  rw [koszulSign_smul_eq_zsign (k := k), mul_comm (D.parity i * D.parity r)] at hy
  have hy' := congrArg (fun f => δ • f) hy
  simp only [δ, smul_smul, zsign_mul_self', one_smul] at hy'
  have hmap : (P.step (true, r) false s hr).map
      (P.mixedQ i q (nextSector (true, r) false s) hq Z) =
      qExpr Sc ((P.step (true, r) false s hr).map
        (P.prPreDot i q (nextSector (true, r) false s) hq Z))
        ((P.step (true, r) false s hr).map
        (P.prPostDot i q (nextSector (true, r) false s) hq Z)) i q :=
    qExpr_map Sc (functorAlg (k := k) (P.step (true, r) false s hr) _) _ _ i q
  rw [hmap]
  have hQ := comp_qExpr (Sc := Sc) J.hom _ _ _ _ i q ε δ hx'.symm hy'.symm
    (fun n hn => zsign_pow_of_mul_eq_zero _ _ n hn)
    (fun n hn => zsign_pow_of_mul_eq_zero _ _ n hn)
  have h := congrArg (fun f => f ≫ J.inv) hQ
  have hpre : (P.step (true, r) false s hr).map
      (P.T.dot i (P.muP_preE i s) ▷ P.distinctReservoirRest i r q s hq Z) =
      (P.step (true, r) false s hr).map
        (P.prPreDot i q (nextSector (true, r) false s) hq Z) := by rfl
  rw [hpre] at h
  simpa only [J, Category.assoc, Iso.hom_inv_id, Category.comp_id] using h

/-- The first mixed Q factor passes across the unequal reservoir crossing. -/
theorem postCrossNe_qExpr_outer
    (hq' : StepValid (true, q) false s)
    (hr' : StepValid (true, r) false (nextSector (true, q) false s))
    (hrq : r ≠ q)
    (hsP : nextSector (true, q) false (nextSector (true, r) false (nextSector (true, i) true s)) =
      nextSector (true, r) false (nextSector (true, q) false (nextSector (true, i) true s)))
    (Y : P.H (nextSector (true, r) false (nextSector (true, q) false (nextSector (true, i) true s)))) :
    P.mixedQ i r s hr (P.distinctReservoirRest i r q s hq (hsP ▸ Y)) ≫
        (P.step (true, i) true s trivial).map
          (P.postCrossNe r q (nextSector (true, i) true s) hr hq hq' hr' hsP Y) =
      (P.step (true, i) true s trivial).map
          (P.postCrossNe r q (nextSector (true, i) true s) hr hq hq' hr' hsP Y) ≫
        qExpr Sc (P.prPreDot i q s hq' (P.distinctReservoirRest i q r s hr' Y))
          (P.distinctReservoirLastDot i q r s hq' hr' Y) i r := by
  symm
  apply comp_qExpr (Sc := Sc) _ _ _ _ _ i r
    (zsign k (D.parity i * (D.parity r * D.parity q)))
    (zsign k (D.parity r * D.parity q))
  · have hθ := (P.postCrossNe_supernatural r q (nextSector (true, i) true s)
      hr hq hq' hr' hsP).mem Y
    have h := TwoSupercategory.super_interchange (R := k) (P.T.dot_mem i (P.muP_preE i s)) hθ
    rw [koszulSign_smul_eq_zsign (k := k)] at h
    have h' := congrArg (fun f => zsign k (D.parity i * (D.parity r * D.parity q)) • f) h
    simp only [smul_smul, zsign_mul_self', one_smul] at h'
    exact h'.symm
  · have h := congrArg (P.step (true, i) true s trivial).map
      (P.postCrossNe_slideL r q hrq (nextSector (true, i) true s) hr hq hq' hr' hsP Y)
    simp only [Functor.map_comp, Functor.map_smul] at h
    have h' := congrArg (fun f => zsign k (D.parity r * D.parity q) • f) h
    simp only [smul_smul, zsign_mul_self', one_smul] at h'
    exact h'.symm
  · exact zsign_pow_of_mul_eq_zero _ _
  · exact zsign_pow_of_mul_eq_zero _ _

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
