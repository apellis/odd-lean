/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.QuadNe
import OddMath.QuiverHecke.SwappedAssembly.Supernatural.Cross

/-! Spectator transport for the reverse probe-pair sector.
The reservoir colour is arbitrary. All Q expressions retain their original parity support.
Composition is categorical; multiplication in End has the reverse order.
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
variable (P : ProbeReservoir k B D Sc) (i r : I) (s : Sector I)
  (hR : StepValid (true, r) false s)
  (Z : P.H (nextSector (true, r) false
    (nextSector (true, i) true (nextSector (true, i) true s))))

/-- The reservoir dot on the third letter of PPR. -/
def probePairSpectatorDot :
    End ((P.step (true, i) true s trivial).obj ((P.step (true, i) true _ trivial).obj
      ((P.step (true, r) false
      (nextSector (true, i) true (nextSector (true, i) true s)) hR).obj Z))) :=
  (P.step (true, i) true s trivial).map
    (P.prPostDot i r (nextSector (true, i) true s) hR Z)

/-- The comparison from PPR to PRP, for arbitrary reservoir colour. -/
def probePairFirstIso :=
  (P.step (true, i) true s trivial).mapIso
    (P.mixedJ i r (nextSector (true, i) true s) hR Z)

/-- The outer probe dot supercommutes with the spectator dot. -/
theorem ppLeftDot_comp_probePairSpectatorDot :
    P.ppLeftDot i s ((P.step (true, r) false
      (nextSector (true, i) true (nextSector (true, i) true s)) hR).obj Z) ≫
        P.probePairSpectatorDot i r s hR Z =
      koszulSign (D.parity i) (D.parity r) •
        (P.probePairSpectatorDot i r s hR Z ≫
          P.ppLeftDot i s ((P.step (true, r) false
      (nextSector (true, i) true (nextSector (true, i) true s)) hR).obj Z)) :=
  TwoSupercategory.super_interchange (R := k) (P.T.dot_mem i _)
    ((P.prPostDot_supernatural i r (nextSector (true, i) true s) hR).mem Z)

/-- The inner probe dot supercommutes with the spectator dot. -/
theorem ppRightDot_comp_probePairSpectatorDot :
    P.ppRightDot i s ((P.step (true, r) false
      (nextSector (true, i) true (nextSector (true, i) true s)) hR).obj Z) ≫
        P.probePairSpectatorDot i r s hR Z =
      koszulSign (D.parity i) (D.parity r) •
        (P.probePairSpectatorDot i r s hR Z ≫
          P.ppRightDot i s ((P.step (true, r) false
      (nextSector (true, i) true (nextSector (true, i) true s)) hR).obj Z)) := by
  have hθ := (homContentPostDot_power_supernatural (k := k) P.T.obj P.W r
    (nextSector (true, i) true (nextSector (true, i) true s)).1
    (P.muP (nextSector (true, i) true (nextSector (true, i) true s)))
    (P.muM_postE r hR) 1).mem Z
  simp only [Nat.cast_one, one_mul, pow_one] at hθ
  have h := TwoSupercategory.super_interchange (R := k)
    (P.T.dot_mem i (P.muP_preE i (nextSector (true, i) true s))) hθ
  have h' := congrArg (P.step (true, i) true s trivial).map h
  simp only [Functor.map_comp, Functor.map_zsmul] at h'
  exact h'

/-- The same-colour probe crossing supercommutes with an arbitrary spectator colour. -/
theorem preCrossSame_comp_probePairSpectatorDot :
    P.preCrossSame i s ((P.step (true, r) false
      (nextSector (true, i) true (nextSector (true, i) true s)) hR).obj Z) ≫
        P.probePairSpectatorDot i r s hR Z =
      koszulSign (D.parity i) (D.parity r) •
        (P.probePairSpectatorDot i r s hR Z ≫
          P.preCrossSame i s ((P.step (true, r) false
      (nextSector (true, i) true (nextSector (true, i) true s)) hR).obj Z)) := by
  have hθ := (homContentPostDot_power_supernatural (k := k) P.T.obj P.W r
    (nextSector (true, i) true (nextSector (true, i) true s)).1
    (P.muP (nextSector (true, i) true (nextSector (true, i) true s)))
    (P.muM_postE r hR) 1).mem Z
  simp only [Nat.cast_one, one_mul, pow_one] at hθ
  have h : P.probePairSpectatorDot i r s hR Z ≫
      P.preCrossSame i s ((P.step (true, r) false
      (nextSector (true, i) true (nextSector (true, i) true s)) hR).obj Z) =
    koszulSign (D.parity i) (D.parity r) •
      (P.preCrossSame i s ((P.step (true, r) false
      (nextSector (true, i) true (nextSector (true, i) true s)) hR).obj Z) ≫
        P.probePairSpectatorDot i r s hR Z) := by
    have h₀ := (P.preCrossSame_supernatural i s).naturality hθ
    rw [SKM.zmod2_mul_self, ← koszulSign_smul (R := k)] at h₀
    exact h₀
  rw [h, smul_smul, koszulSign_mul_self, one_smul]

/-- The right Q factor is Q in the inner probe dot and the spectator dot. -/
theorem probePair_map_mixedQ :
    (P.step (true, i) true s trivial).map
        (P.mixedQ i r (nextSector (true, i) true s) hR Z) =
      qExpr Sc (P.ppRightDot i s ((P.step (true, r) false
      (nextSector (true, i) true (nextSector (true, i) true s)) hR).obj Z))
        (P.probePairSpectatorDot i r s hR Z) i r :=
  qExpr_map Sc (functorAlg (k := k) (P.step (true, i) true s trivial) _)
    _ _ i r

/-- The spectator comparison transports the outer probe dot with the mixed sign. -/
theorem ppLeftDot_comp_probePairFirstIso :
    P.ppLeftDot i s ((P.step (true, r) false
      (nextSector (true, i) true (nextSector (true, i) true s)) hR).obj Z) ≫
        (P.probePairFirstIso i r s hR Z).hom =
      zsign k (D.parity i * D.parity r) •
        ((P.probePairFirstIso i r s hR Z).hom ≫
          P.prPreDot i r s hR ((P.step (true, i) true
            (nextSector (true, r) false (nextSector (true, i) true s)) trivial).obj Z)) := by
  have h := TwoSupercategory.super_interchange (R := k) (P.T.dot_mem i (P.muP_preE i s))
    (homMixedInterchange_mem (k := k) _ _ _ _ _ :
      (P.mixedJ i r (nextSector (true, i) true s) hR Z).hom ∈ parity (R := k) _ _ _)
  have hs : homContentShift D r
      (nextSector (true, i) true (nextSector (true, i) true s)).1 +
      homContentShift D r (nextSector (true, i) true s).1 =
      D.parity i * D.parity r := by
    change homContentShift D r ((nextSector (true, i) true s).1 + Finsupp.single i 1) +
      homContentShift D r (nextSector (true, i) true s).1 = _
    rw [homContentShift_add_single]
    generalize homContentShift D r (nextSector (true, i) true s).1 = a
    generalize D.parity i = p
    generalize D.parity r = q
    fin_cases a <;> fin_cases p <;> fin_cases q <;> decide
  rw [hs, koszulSign_smul_eq_zsign (k := k), ← mul_assoc, SKM.zmod2_mul_self] at h
  exact h

/-- The middle-path reservoir dot conjugates to the signed PPR spectator dot. -/
theorem probePairFirstIso_conj_prPostDot :
    (P.probePairFirstIso i r s hR Z).hom ≫
      P.prPostDot i r s hR ((P.step (true, i) true
        (nextSector (true, r) false (nextSector (true, i) true s)) trivial).obj Z) ≫
      (P.probePairFirstIso i r s hR Z).inv =
    zsign k (D.parity i * D.parity r) • P.probePairSpectatorDot i r s hR Z := by
  have h := congrArg (fun f => f ≫ (P.mixedJ i r (nextSector (true, i) true s) hR Z).inv)
    (P.prPostDot_comp_mixedJ_ne i r (nextSector (true, i) true s) hR Z)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Linear.smul_comp] at h
  have h' := congrArg (fun f => zsign k (D.parity i * D.parity r) • f) h
  simp only [smul_smul, zsign_mul_self', one_smul] at h'
  have hm := congrArg (P.step (true, i) true s trivial).map h'.symm
  simp only [Functor.map_comp, Functor.map_smul] at hm
  exact hm

/-- The transported left Q factor is Q in the outer probe dot and the SAME spectator dot.
The signed-dot transport disappears only on the parity-allowed exponents of Q. -/
theorem probePairFirstIso_conj_mixedQ :
    (P.probePairFirstIso i r s hR Z).hom ≫
      P.mixedQ i r s hR ((P.step (true, i) true
        (nextSector (true, r) false (nextSector (true, i) true s)) trivial).obj Z) ≫
      (P.probePairFirstIso i r s hR Z).inv =
    qExpr Sc (P.ppLeftDot i s ((P.step (true, r) false
      (nextSector (true, i) true (nextSector (true, i) true s)) hR).obj Z))
      (P.probePairSpectatorDot i r s hR Z) i r := by
  let J := P.probePairFirstIso i r s hR Z
  let ε := zsign k (D.parity i * D.parity r)
  have hx := congrArg (fun f => ε • f) (P.ppLeftDot_comp_probePairFirstIso i r s hR Z)
  simp only [ε, smul_smul, zsign_mul_self', one_smul] at hx
  have hy := congrArg (fun f => f ≫ J.hom)
    (P.probePairFirstIso_conj_prPostDot i r s hR Z)
  simp only [J, Category.assoc, Iso.inv_hom_id, Category.comp_id] at hy
  have hy' : J.hom ≫ P.prPostDot i r s hR ((P.step (true, i) true
      (nextSector (true, r) false (nextSector (true, i) true s)) trivial).obj Z) =
      ε • (P.probePairSpectatorDot i r s hR Z ≫ J.hom) := by
    rw [hy]
    change (ε • (P.probePairSpectatorDot i r s hR Z : _ ⟶ _)) ≫ J.hom = _
    rw [Linear.smul_comp]
  have hQ := comp_qExpr (Sc := Sc) J.hom _ _ _ _ i r ε ε hx.symm hy'
    (fun n hn => zsign_pow_of_mul_eq_zero _ _ n hn)
    (fun n hn => by
      change zsign k (D.parity i * D.parity r) ^ n = 1
      rw [mul_comm]
      exact zsign_pow_of_mul_eq_zero _ _ n hn)
  have h := congrArg (fun f => f ≫ J.inv) hQ
  simpa only [J, mixedQ, qExpr, prPreDot, prPostDot, Category.assoc,
    Iso.hom_inv_id, Category.comp_id] using h

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
