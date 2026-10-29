/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.QuadNe
import OddMath.QuiverHecke.SwappedAssembly.Supernatural.Cross

/-! Dot identifications for mixed braid sectors with arbitrary probe colours.
The two mixed Q factors on `Pᵢ Pⱼ Rᵣ` use the same reservoir spectator dot.
No inequality between colours is required. The signed transports become unsigned
on the parity-supported powers occurring in Q.
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
variable (P : ProbeReservoir k B D Sc) (i j r : I) (s : Sector I)
  (hR : StepValid (true, r) false s)
  (Z : P.H (nextSector (true, r) false
    (nextSector (true, j) true (nextSector (true, i) true s))))

/-- The outer probe dot on `Pᵢ Pⱼ Rᵣ`. -/
def distinctProbeOuterDot :
    End ((P.step (true, i) true s trivial).obj ((P.step (true, j) true _ trivial).obj
      ((P.step (true, r) false
        (nextSector (true, j) true (nextSector (true, i) true s)) hR).obj Z))) :=
  P.T.dot i (P.muP_preE i s) ▷ ((P.step (true, j) true _ trivial).obj
    ((P.step (true, r) false
      (nextSector (true, j) true (nextSector (true, i) true s)) hR).obj Z))

/-- The inner probe dot on `Pᵢ Pⱼ Rᵣ`. -/
def distinctProbeInnerDot :
    End ((P.step (true, i) true s trivial).obj ((P.step (true, j) true _ trivial).obj
      ((P.step (true, r) false
        (nextSector (true, j) true (nextSector (true, i) true s)) hR).obj Z))) :=
  (P.step (true, i) true s trivial).map
    (P.prPreDot j r (nextSector (true, i) true s) hR Z)

/-- The reservoir spectator dot on `Pᵢ Pⱼ Rᵣ`. -/
def distinctProbeSpectatorDot :
    End ((P.step (true, i) true s trivial).obj ((P.step (true, j) true _ trivial).obj
      ((P.step (true, r) false
        (nextSector (true, j) true (nextSector (true, i) true s)) hR).obj Z))) :=
  (P.step (true, i) true s trivial).map
    (P.prPostDot j r (nextSector (true, i) true s) hR Z)

/-- The first comparison `Pᵢ Pⱼ Rᵣ ≅ Pᵢ Rᵣ Pⱼ`. -/
def distinctProbeFirstIso :=
  (P.step (true, i) true s trivial).mapIso
    (P.mixedJ j r (nextSector (true, i) true s) hR Z)

/-- The inner mixed Q factor is Q in the inner and spectator dots. -/
theorem distinctProbe_map_mixedQ :
    (P.step (true, i) true s trivial).map
        (P.mixedQ j r (nextSector (true, i) true s) hR Z) =
      qExpr Sc (P.distinctProbeInnerDot i j r s hR Z)
        (P.distinctProbeSpectatorDot i j r s hR Z) j r :=
  qExpr_map Sc (functorAlg (k := k) (P.step (true, i) true s trivial) _)
    _ _ j r

/-- The outer dot crosses the first comparison with sign `pᵢ pⱼ pᵣ`. -/
theorem distinctProbeOuterDot_comp_firstIso :
    P.distinctProbeOuterDot i j r s hR Z ≫
        (P.distinctProbeFirstIso i j r s hR Z).hom =
      zsign k (D.parity i * D.parity j * D.parity r) •
        ((P.distinctProbeFirstIso i j r s hR Z).hom ≫
          P.prPreDot i r s hR ((P.step (true, j) true
            (nextSector (true, r) false (nextSector (true, i) true s)) trivial).obj Z)) := by
  have h := TwoSupercategory.super_interchange (R := k) (P.T.dot_mem i (P.muP_preE i s))
    (homMixedInterchange_mem (k := k) _ _ _ _ _ :
      (P.mixedJ j r (nextSector (true, i) true s) hR Z).hom ∈ parity (R := k) _ _ _)
  have hs : homContentShift D r
      (nextSector (true, j) true (nextSector (true, i) true s)).1 +
      homContentShift D r (nextSector (true, i) true s).1 =
      D.parity j * D.parity r := by
    change homContentShift D r ((nextSector (true, i) true s).1 + Finsupp.single j 1) +
      homContentShift D r (nextSector (true, i) true s).1 = _
    rw [homContentShift_add_single]
    generalize homContentShift D r (nextSector (true, i) true s).1 = a
    generalize D.parity j = p
    generalize D.parity r = q
    fin_cases a <;> fin_cases p <;> fin_cases q <;> decide
  rw [hs, koszulSign_smul_eq_zsign (k := k), ← mul_assoc] at h
  exact h

/-- The reservoir dot conjugates with sign `pⱼ pᵣ`, independently of the outer probe. -/
theorem distinctProbeFirstIso_conj_prPostDot :
    (P.distinctProbeFirstIso i j r s hR Z).hom ≫
      P.prPostDot i r s hR ((P.step (true, j) true
        (nextSector (true, r) false (nextSector (true, i) true s)) trivial).obj Z) ≫
      (P.distinctProbeFirstIso i j r s hR Z).inv =
    zsign k (D.parity j * D.parity r) •
      P.distinctProbeSpectatorDot i j r s hR Z := by
  have h := congrArg (fun f => f ≫ (P.mixedJ j r (nextSector (true, i) true s) hR Z).inv)
    (P.prPostDot_comp_mixedJ_ne j r (nextSector (true, i) true s) hR Z)
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id, Linear.smul_comp] at h
  have h' := congrArg (fun f => zsign k (D.parity j * D.parity r) • f) h
  simp only [smul_smul, zsign_mul_self', one_smul] at h'
  have hm := congrArg (P.step (true, i) true s trivial).map h'.symm
  simp only [Functor.map_comp, Functor.map_smul] at hm
  exact hm

/-- The conjugated outer mixed Q factor uses the outer dot and the same spectator dot.
Parity support for colour `i` kills the outer transport sign; support for colour `r`
kills the reservoir transport sign. -/
theorem distinctProbeFirstIso_conj_mixedQ :
    (P.distinctProbeFirstIso i j r s hR Z).hom ≫
      P.mixedQ i r s hR ((P.step (true, j) true
        (nextSector (true, r) false (nextSector (true, i) true s)) trivial).obj Z) ≫
      (P.distinctProbeFirstIso i j r s hR Z).inv =
    qExpr Sc (P.distinctProbeOuterDot i j r s hR Z)
      (P.distinctProbeSpectatorDot i j r s hR Z) i r := by
  let J := P.distinctProbeFirstIso i j r s hR Z
  let ε := zsign k (D.parity i * D.parity j * D.parity r)
  let η := zsign k (D.parity j * D.parity r)
  have hx := congrArg (fun f => ε • f)
    (P.distinctProbeOuterDot_comp_firstIso i j r s hR Z)
  simp only [ε, smul_smul, zsign_mul_self', one_smul] at hx
  have hy := congrArg (fun f => f ≫ J.hom)
    (P.distinctProbeFirstIso_conj_prPostDot i j r s hR Z)
  simp only [J, Category.assoc, Iso.inv_hom_id, Category.comp_id] at hy
  have hy' : J.hom ≫ P.prPostDot i r s hR ((P.step (true, j) true
      (nextSector (true, r) false (nextSector (true, i) true s)) trivial).obj Z) =
      η • (P.distinctProbeSpectatorDot i j r s hR Z ≫ J.hom) := by
    rw [hy]
    change (η • (P.distinctProbeSpectatorDot i j r s hR Z : _ ⟶ _)) ≫ J.hom = _
    rw [Linear.smul_comp]
  have hQ := comp_qExpr (Sc := Sc) J.hom _ _ _ _ i r ε η hx.symm hy'
    (fun n hn => by
      change zsign k (D.parity i * D.parity j * D.parity r) ^ n = 1
      rw [mul_assoc]
      exact zsign_pow_of_mul_eq_zero _ _ n hn)
    (fun n hn => by
      change zsign k (D.parity j * D.parity r) ^ n = 1
      rw [mul_comm]
      exact zsign_pow_of_mul_eq_zero _ _ n hn)
  have h := congrArg (fun f => f ≫ J.inv) hQ
  simpa only [J, mixedQ, qExpr, prPreDot, prPostDot, Category.assoc,
    Iso.hom_inv_id, Category.comp_id] using h

end ProbeReservoir
end OddMath.QuiverHecke.SwappedAssembly
