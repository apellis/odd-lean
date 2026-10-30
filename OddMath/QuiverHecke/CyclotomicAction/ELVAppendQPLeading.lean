/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.AppendQPTransport
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendNormRegularity
/-! # Highest append-PBW coefficients of the actual signed QP factors

`appendQPFactor_top` identifies the literal unit highest coefficient, including
disconnected colours and repeated-even signs. `appendQPFactor_above` proves
the accompanying degree bound. Finite maximal append support then proves
`appendProjection_qpProduct_regular` for the actual all-word ordered product.
These are direct append-side inputs to `DeformedBoundaryDivision.md` §3,
not a transported prepend regularity or the full reverse-chain norm.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem appendQP_monomial_above (i : I) (v w : List I)
    (b : ℕ) (hb : b < v.length) (a e : ℕ) (hep : e • D.parity i = 0)
    (h : hom D Sc cutoff (v ++ [i]) w) (x : AppendIdx i v w)
    (hbound : ∀ t ∈ (appendOldCoordinateEquiv D Sc cutoff 0 i v w
      (appendProjection D Sc cutoff i v w h)).support, e + t.1.1 < x.1.1) :
    appendOldCoordinate D Sc cutoff 0 x
      (appendProjection D Sc cutoff i v w
        (affineUnit D Sc cutoff _ _
          (dotE D Sc (v ++ [i]) v.length ^ e * dotE D Sc (v ++ [i]) b ^ a) ≫ h)) = 0 := by
  rw [End.mul_def, affineUnit_comp, Category.assoc,
    appendProjection_old_dotPower D Sc cutoff i v w b a hb]
  have H := appendOldSource_movingPower_above D Sc cutoff 0 x e hep
    (sourceDotPower D Sc cutoff v b a)
    (appendOldCoordinateEquiv D Sc cutoff 0 i v w (appendProjection D Sc cutoff i v w h)) hbound
  rw [appendOldReconstruct_coordinateEquiv] at H
  exact H

/-- The actual unequal QP factor has its prescribed unit coefficient at
maximal moving support, without transporting prepend regularity. -/
theorem appendQP_qPoly_top (i j : I) (hij : i ≠ j) (v w : List I)
    (b : ℕ) (hb : b < v.length) (h : hom D Sc cutoff (v ++ [i]) w)
    (q : AppendIdx.Tail i v w)
    (hmax : ∀ t ∈ (appendOldCoordinateEquiv D Sc cutoff 0 i v w
      (appendProjection D Sc cutoff i v w h)).support, t.1.1 ≤ q.1.1) :
    appendOldCoordinate D Sc cutoff 0 (q.representative.shift (D.dn i j))
      (appendProjection D Sc cutoff i v w
        (affineUnit D Sc cutoff _ _
          (qPoly D Sc (dotE D Sc (v ++ [i]) v.length) (dotE D Sc (v ++ [i]) b) i j) ≫ h)) =
    (Sc.t i j : k) •
      (appendOldCoordinateEquiv D Sc cutoff 0 i v w
        (appendProjection D Sc cutoff i v w h)) q := by
  let f := appendOldCoordinateEquiv D Sc cutoff 0 i v w
    (appendProjection D Sc cutoff i v w h)
  change _ = (Sc.t i j : k) • (f q : Old D Sc cutoff v
    (q.representative.shift (D.dn i j)).oldTarget)
  have hpar : D.dn i j • D.parity i = 0 := by
    simpa only [nsmul_eq_mul] using dn_mul_parity D i j
  have hm := appendMovingPower_coordinate_shift D Sc cutoff 0 q (D.dn i j) hpar f
  rw [appendOldReconstruct_coordinateEquiv] at hm
  change appendOldCoordinate D Sc cutoff 0 (q.representative.shift (D.dn i j))
    (appendProjection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (dotE D Sc (v ++ [i]) v.length ^ D.dn i j) ≫ h)) = f q at hm
  by_cases hd : D.d i j = 0
  · have hn : D.dn i j = 0 := by have hc := D.dn_cast hij; omega
    rw [qPoly, ite_eq_left hd, map_smul, Linear.smul_comp, map_smul, map_smul]
    simp only [hn, pow_zero] at hm
    exact congrArg (fun y : Old D Sc cutoff v q.representative.oldTarget =>
      (Sc.t i j : k) • y) hm
  have hpos : 0 < D.dn i j := by have hc := D.dn_cast hij; omega
  have hlow (a e : ℕ) (he : e < D.dn i j) (hep : e • D.parity i = 0) :
      appendOldCoordinate D Sc cutoff 0 (q.representative.shift (D.dn i j))
        (appendProjection D Sc cutoff i v w
          (affineUnit D Sc cutoff _ _
            (dotE D Sc (v ++ [i]) v.length ^ e * dotE D Sc (v ++ [i]) b ^ a) ≫ h)) = 0 := by
    apply appendQP_monomial_above D Sc cutoff i v w b hb a e hep h
    intro t ht
    have hh := hmax t ht
    have hk := congrArg Prod.fst q.representative_tailKey
    change q.representative.1.1 = q.1.1 at hk
    change e + t.1.1 < D.dn i j + q.representative.1.1
    omega
  have hold : appendOldCoordinate D Sc cutoff 0 (q.representative.shift (D.dn i j))
      (appendProjection D Sc cutoff i v w
        (affineUnit D Sc cutoff _ _ (dotE D Sc (v ++ [i]) b ^ D.dn j i) ≫ h)) = 0 := by
    simpa only [pow_zero, one_mul] using hlow (D.dn j i) 0 hpos (by simp)
  rw [qPoly, ite_eq_right hd]
  simp only [map_add, map_sum, map_smul, Preadditive.add_comp, Preadditive.sum_comp,
    Linear.smul_comp]
  have hl : (∑ e ∈ Finset.Ioo 0 (D.dn i j), ∑ a ∈ Finset.Ioo 0 (D.dn j i),
      Sc.s i j e a • appendOldCoordinate D Sc cutoff 0 (q.representative.shift (D.dn i j))
        (appendProjection D Sc cutoff i v w
          (affineUnit D Sc cutoff _ _
            (dotE D Sc (v ++ [i]) v.length ^ e * dotE D Sc (v ++ [i]) b ^ a) ≫ h))) = 0 := by
    apply Finset.sum_eq_zero
    intro e he
    apply Finset.sum_eq_zero
    intro a _
    by_cases hs : Sc.s i j e a = 0
    · rw [hs, zero_smul]
    · have hep : e • D.parity i = 0 := by
        rw [nsmul_eq_mul]
        apply zmod_two_eq_zero_of_ne_one
        exact fun hp => hs (Sc.s_eq_zero i j e a hp)
      rw [hlow a e (Finset.mem_Ioo.mp he).2 hep, smul_zero]
  rw [hl, hold, smul_zero, add_zero, zero_add]
  exact congrArg (fun y : Old D Sc cutoff v (q.representative.shift (D.dn i j)).oldTarget =>
    (Sc.t i j : k) • y) hm
theorem appendQP_qPoly_above (i j : I) (v w : List I)
    (b : ℕ) (hb : b < v.length) (h : hom D Sc cutoff (v ++ [i]) w)
    (x : AppendIdx i v w)
    (hbound : ∀ t ∈ (appendOldCoordinateEquiv D Sc cutoff 0 i v w
      (appendProjection D Sc cutoff i v w h)).support, D.dn i j + t.1.1 < x.1.1) :
    appendOldCoordinate D Sc cutoff 0 x
      (appendProjection D Sc cutoff i v w
        (affineUnit D Sc cutoff _ _
          (qPoly D Sc (dotE D Sc (v ++ [i]) v.length) (dotE D Sc (v ++ [i]) b) i j) ≫ h)) = 0 := by
  have hlow (a e : ℕ) (he : e ≤ D.dn i j) (hep : e • D.parity i = 0) :
      appendOldCoordinate D Sc cutoff 0 x
        (appendProjection D Sc cutoff i v w
          (affineUnit D Sc cutoff _ _
            (dotE D Sc (v ++ [i]) v.length ^ e * dotE D Sc (v ++ [i]) b ^ a) ≫ h)) = 0 := by
    apply appendQP_monomial_above D Sc cutoff i v w b hb a e hep h x
    intro t ht
    have hh := hbound t ht
    omega
  have hold : appendOldCoordinate D Sc cutoff 0 x
      (appendProjection D Sc cutoff i v w
        (affineUnit D Sc cutoff _ _ (dotE D Sc (v ++ [i]) b ^ D.dn j i) ≫ h)) = 0 := by
    simpa only [pow_zero, one_mul] using hlow (D.dn j i) 0 (Nat.zero_le _) (by simp)
  have hm : appendOldCoordinate D Sc cutoff 0 x
      (appendProjection D Sc cutoff i v w
        (affineUnit D Sc cutoff _ _ (dotE D Sc (v ++ [i]) v.length ^ D.dn i j) ≫ h)) = 0 := by
    simpa only [pow_zero, mul_one] using hlow 0 (D.dn i j) le_rfl
      (by simpa only [nsmul_eq_mul] using dn_mul_parity D i j)
  unfold qPoly
  split_ifs
  · simp only [map_smul, Linear.smul_comp]
    have hz := hlow 0 0 (Nat.zero_le _) (by simp)
    simp only [pow_zero, mul_one] at hz
    rw [hz, smul_zero]
  · simp only [map_add, map_sum, map_smul, Preadditive.add_comp, Preadditive.sum_comp,
      Linear.smul_comp, hold, hm, smul_zero, add_zero]
    apply Finset.sum_eq_zero
    intro e he
    apply Finset.sum_eq_zero
    intro a _
    by_cases hs : Sc.s i j e a = 0
    · rw [hs, zero_smul]
    · have hep : e • D.parity i = 0 := by
        rw [nsmul_eq_mul]
        apply zmod_two_eq_zero_of_ne_one
        exact fun hp => hs (Sc.s_eq_zero i j e a hp)
      rw [hlow a e (Nat.le_of_lt (Finset.mem_Ioo.mp he).2) hep, smul_zero]

def appendQPDegree (i j : I) : ℕ :=
  if j = i then if D.parity i = 1 then 2 else 0 else D.dn i j

def appendQPUnit (i j : I) : kˣ :=
  if j = i then if D.parity i = 1 then 1 else -1 else Sc.t i j

/-- The actual QP factor at a repeated odd strand, at maximal append support. -/
theorem appendQP_odd_top (i : I) (hi : D.parity i = 1) (v w : List I)
    (b : ℕ) (hb : b < v.length) (hx : v.getD b i = i)
    (h : hom D Sc cutoff (v ++ [i]) w) (q : AppendIdx.Tail i v w)
    (hmax : ∀ t ∈ (appendOldCoordinateEquiv D Sc cutoff 0 i v w
      (appendProjection D Sc cutoff i v w h)).support, t.1.1 ≤ q.1.1) :
    appendOldCoordinate D Sc cutoff 0 (q.representative.shift 2)
      (appendProjection D Sc cutoff i v w
        (affineUnit D Sc cutoff _ _ (appendQPFactor D Sc i v i b) ≫ h)) =
      (appendOldCoordinateEquiv D Sc cutoff 0 i v w
        (appendProjection D Sc cutoff i v w h)) q := by
  have hm := appendMovingPower_coordinate_shift D Sc cutoff 0 q 2
    ((by decide : ∀ p : ZMod 2, (2 : ℕ) • p = 0) (D.parity i))
    (appendOldCoordinateEquiv D Sc cutoff 0 i v w (appendProjection D Sc cutoff i v w h))
  rw [appendOldReconstruct_coordinateEquiv] at hm
  have hold : appendOldCoordinate D Sc cutoff 0 (q.representative.shift 2)
      (appendProjection D Sc cutoff i v w
        (affineUnit D Sc cutoff _ _ (dotE D Sc (v ++ [i]) b ^ 2) ≫ h)) = 0 := by
    have hh := appendQP_monomial_above D Sc cutoff i v w b hb 2 0 (by simp)
      h (q.representative.shift 2)
    simp only [pow_zero, one_mul] at hh
    apply hh
    intro t ht
    have H := hmax t ht
    have hk := congrArg Prod.fst q.representative_tailKey
    change q.representative.1.1 = q.1.1 at hk
    change 0 + t.1.1 < 2 + q.representative.1.1
    omega
  rw [appendQPFactor_odd D Sc i hi v b hb hx, map_add, Preadditive.add_comp,
    map_add, map_add, hold, zero_add]
  exact hm

/-- Highest moving coefficient of each actual QP factor; all old coefficients
are retained, including the full exterior quotient. -/
theorem appendQPFactor_top (i : I) (v w : List I)
    (b : ℕ) (hb : b < v.length) (h : hom D Sc cutoff (v ++ [i]) w)
    (q : AppendIdx.Tail i v w)
    (hmax : ∀ t ∈ (appendOldCoordinateEquiv D Sc cutoff 0 i v w
      (appendProjection D Sc cutoff i v w h)).support, t.1.1 ≤ q.1.1) :
    appendOldCoordinate D Sc cutoff 0 (q.representative.shift (appendQPDegree D i (v.getD b i)))
      (appendProjection D Sc cutoff i v w
        (affineUnit D Sc cutoff _ _ (appendQPFactor D Sc i v (v.getD b i) b) ≫ h)) =
    (appendQPUnit D Sc i (v.getD b i) : k) •
      (appendOldCoordinateEquiv D Sc cutoff 0 i v w
        (appendProjection D Sc cutoff i v w h)) q := by
  by_cases hx : v.getD b i = i
  · by_cases hi : D.parity i = 1
    · have hd : appendQPDegree D i (v.getD b i) = 2 := by rw [appendQPDegree, ite_eq_left hx]; simp only [hi, ↓reduceIte]
      have hu : (appendQPUnit D Sc i (v.getD b i) : k) = 1 := by
        rw [appendQPUnit, ite_eq_left hx, ite_eq_left hi, Units.val_one]
      rw [hd, hu, one_smul]
      simpa only [hx] using appendQP_odd_top D Sc cutoff i hi v w b hb hx h q hmax
    · have hd : appendQPDegree D i (v.getD b i) = 0 := by rw [appendQPDegree, ite_eq_left hx]; simp only [hi, ↓reduceIte]
      have hu : (appendQPUnit D Sc i (v.getD b i) : k) = -1 := by rw [appendQPUnit, ite_eq_left hx]; simp only [hi, ↓reduceIte, Units.val_one, Units.val_neg]
      have ha : appendQPFactor D Sc i v (v.getD b i) b = -1 := by rw [appendQPFactor, ite_eq_left hx, ite_eq_right hi]
      rw [hd, hu, ha, neg_one_smul, map_neg, Preadditive.neg_comp, map_neg, map_neg]
      have hm := appendMovingPower_coordinate_shift D Sc cutoff 0 q 0 (by simp)
        (appendOldCoordinateEquiv D Sc cutoff 0 i v w (appendProjection D Sc cutoff i v w h))
      rw [appendOldReconstruct_coordinateEquiv] at hm
      change appendOldCoordinate D Sc cutoff 0 (q.representative.shift 0)
        (appendProjection D Sc cutoff i v w
          (affineUnit D Sc cutoff _ _ (1 : End _) ≫ h)) = _ at hm
      exact congrArg (fun y : Old D Sc cutoff v q.representative.oldTarget => -y) hm
  · have hd : appendQPDegree D i (v.getD b i) = D.dn i (v.getD b i) := by rw [appendQPDegree, ite_eq_right hx]
    have hu : (appendQPUnit D Sc i (v.getD b i) : k) = Sc.t i (v.getD b i) := by rw [appendQPUnit, ite_eq_right hx]
    rw [hd, hu, appendQPFactor, ite_eq_right hx]
    exact appendQP_qPoly_top D Sc cutoff i (v.getD b i) (Ne.symm hx) v w b hb h q hmax

theorem appendQPFactor_above (i : I) (v w : List I)
    (b : ℕ) (hb : b < v.length) (h : hom D Sc cutoff (v ++ [i]) w)
    (x : AppendIdx i v w)
    (hbound : ∀ t ∈ (appendOldCoordinateEquiv D Sc cutoff 0 i v w
      (appendProjection D Sc cutoff i v w h)).support,
      appendQPDegree D i (v.getD b i) + t.1.1 < x.1.1) :
    appendOldCoordinate D Sc cutoff 0 x
      (appendProjection D Sc cutoff i v w
        (affineUnit D Sc cutoff _ _ (appendQPFactor D Sc i v (v.getD b i) b) ≫ h)) = 0 := by
  by_cases hx : v.getD b i = i
  · by_cases hi : D.parity i = 1
    · simp only [appendQPDegree, ite_eq_left hx, ite_eq_left hi] at hbound
      have hold := appendQP_monomial_above D Sc cutoff i v w b hb 2 0 (by simp) h x
      have hm := appendQP_monomial_above D Sc cutoff i v w b hb 0 2 ((by decide : ∀ p : ZMod 2, (2 : ℕ) • p = 0) (D.parity i)) h x hbound
      simp only [pow_zero, one_mul] at hold
      simp only [pow_zero, mul_one] at hm
      rw [hx, appendQPFactor_odd D Sc i hi v b hb hx, map_add, Preadditive.add_comp,
        map_add, map_add, hm, add_zero]
      apply hold
      intro t ht
      have hh := hbound t ht
      omega
    · simp only [appendQPDegree, ite_eq_left hx, ite_eq_right hi] at hbound
      have hz := appendQP_monomial_above D Sc cutoff i v w b hb 0 0 (by simp) h x hbound
      simp only [pow_zero, mul_one] at hz
      rw [appendQPFactor, ite_eq_left hx, ite_eq_right hi,
        map_neg, Preadditive.neg_comp, map_neg, map_neg, hz, neg_zero]
  · simp only [appendQPDegree, ite_eq_right hx] at hbound
    rw [appendQPFactor, ite_eq_right hx]
    exact appendQP_qPoly_above D Sc cutoff i (v.getD b i) v w b hb h x hbound

/-- Direct finite maximal append support cancels every actual signed QP factor. -/
theorem appendProjection_qpFactor_regular (i : I) (v w : List I)
    (b : ℕ) (hb : b < v.length) (h : hom D Sc cutoff (v ++ [i]) w)
    (hh : appendProjection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (appendQPFactor D Sc i v (v.getD b i) b) ≫ h) = 0) :
    appendProjection D Sc cutoff i v w h = 0 := by
  let f := appendOldCoordinateEquiv D Sc cutoff 0 i v w
    (appendProjection D Sc cutoff i v w h)
  suffices hf : f = 0 by
    exact (appendOldCoordinateEquiv D Sc cutoff 0 i v w).injective
      (hf.trans (map_zero _).symm)
  by_contra hn
  obtain ⟨q, hq, hmax⟩ := f.support.exists_max_image (fun q => q.1.1)
    (Finset.nonempty_iff_ne_empty.mpr (fun he => hn (DFinsupp.support_eq_empty.mp he)))
  have he := appendQPFactor_top D Sc cutoff i v w b hb h q hmax
  rw [hh, map_zero] at he
  exact (DFinsupp.mem_support_iff.mp hq)
    ((appendQPUnit D Sc i (v.getD b i)).isUnit.smul_eq_zero.mp he.symm)

/-- The independently evaluated ordered append QP product is regular.
The proof uses its actual highest append-PBW coefficients, not prepend transport
or the different full reverse-chain norm. -/
theorem appendProjection_qpProduct_regular (i : I) (v w : List I)
    (h : hom D Sc cutoff (v ++ [i]) w)
    (hh : appendProjection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫ h) = 0) :
    appendProjection D Sc cutoff i v w h = 0 := by
  have H (l : List ℕ) (hl : ∀ b ∈ l, b < v.length)
      (h : hom D Sc cutoff (v ++ [i]) w)
      (hh : appendProjection D Sc cutoff i v w
        (affineUnit D Sc cutoff _ _
          ((l.map fun b => appendQPFactor D Sc i v (v.getD b i) b).prod) ≫ h) = 0) :
      appendProjection D Sc cutoff i v w h = 0 := by
    induction l generalizing h with
    | nil =>
      simpa only [List.map_nil, List.prod_nil, End.one_def, affineUnit_id, Category.id_comp] using hh
    | cons b l ih =>
      simp only [List.map_cons, List.prod_cons, End.mul_def, affineUnit_comp, Category.assoc] at hh
      exact appendProjection_qpFactor_regular D Sc cutoff i v w b (hl b (by simp)) h
        (ih (fun c hc => hl c (by simp [hc])) _ hh)
  exact H (List.range v.length) (fun b hb => List.mem_range.mp hb) h hh

end OddMath.QuiverHecke.ELVOld
