/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVQPNumerator
/-! # Signed old-Hom division by the ordered endpoint–QP numerator

`endpointQP_top` and `endpointQP_above` assemble the actual unit highest action,
including the full old-Hom twist. `endpointQP_division` uses these statements
and finite support to divide every old-only append target by the prescribed
chronological numerator, leaving support strictly below its moving degree.
No arbitrary polynomial-evaluation multiplicativity or output S identity is used.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped TensorProduct DirectSum Classical
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem appendOldCoordinate_heq (p : ZMod 2) {i : I} {v w : List I}
    (x z : AppendIdx i v w) (hk : x.tailKey = z.tailKey)
    (a : AppendTarget D Sc cutoff i v w) :
    HEq (appendOldCoordinate D Sc cutoff p x a)
      (appendOldCoordinate D Sc cutoff p z a) := by
  obtain ⟨h, rfl⟩ := appendProjection_surjective D Sc cutoff i v w a
  simp only [appendOldCoordinate_projection]
  have ht := x.oldTarget_eq_of_tailKey_eq z hk
  have hn := congrArg Prod.fst hk
  have hd := congrArg Prod.snd hk
  change x.1.1 = z.1.1 at hn
  change x.1.2.2.2 = z.1.2.2.2 at hd
  have hp : appendTailParity D x = appendTailParity D z := by
    unfold appendTailParity
    rw [ht, hn, hd]
  have hr (y : NFIdx v x.oldTarget) :
      x.replaceOld y = z.replaceOld (ht ▸ y) := by
    apply Subtype.ext
    have hv {t t' : List I} (e : t = t') (b : NFIdx v t) :
        (e ▸ b : NFIdx v t').val = b.val := by cases e; rfl
    simp only [AppendIdx.replaceOld, hv, hn, hd]
  have H {t t' : List I} (e : t = t')
      (f : NFIdx v t → AppendIdx i v w) (g : NFIdx v t' → AppendIdx i v w)
      (hf : Function.Injective f) (hg : Function.Injective g)
      (he : ∀ y, f y = g (e ▸ y)) (s : ZMod 2) :
      HEq (((ideal D Sc cutoff v t).mkQ.comp ((twist k p).comp
        ((oldAffineEquiv D Sc cutoff v t).symm.toLinearMap.comp
        ((Finsupp.mapRange.linearMap (coefficientTwist D cutoff s)).comp
        ((Finsupp.lcomapDomain f hf).comp
        (appendAffineEquiv D Sc cutoff i v w).toLinearMap))))) h)
      (((ideal D Sc cutoff v t').mkQ.comp ((twist k p).comp
        ((oldAffineEquiv D Sc cutoff v t').symm.toLinearMap.comp
        ((Finsupp.mapRange.linearMap (coefficientTwist D cutoff s)).comp
        ((Finsupp.lcomapDomain g hg).comp
        (appendAffineEquiv D Sc cutoff i v w).toLinearMap))))) h) := by
    subst t'
    have : f = g := funext he
    subst g
    rfl
  unfold appendExtractOldQuotient appendExtractOld
  rw [hp]
  exact H ht x.replaceOld z.replaceOld x.replaceOld_injective z.replaceOld_injective hr _

theorem appendOldCoefficient_smul_heq {v t t' : List I} (e : t = t') (a : k)
    {b : Old D Sc cutoff v t} {c : Old D Sc cutoff v t'} (h : HEq b c) :
    HEq (a • b) (a • c) := by
  subst t'
  cases h
  rfl

theorem appendQPFactor_top_at (i : I) (v w : List I) (b : ℕ) (hb : b < v.length)
    (h : hom D Sc cutoff (v ++ [i]) w) (x : AppendIdx i v w)
    (hm : ∀ t ∈ (appendOldCoordinateEquiv D Sc cutoff 0 i v w
      (appendProjection D Sc cutoff i v w h)).support, t.1.1 ≤ x.1.1) :
    appendOldCoordinate D Sc cutoff 0 (x.shift (appendQPDegree D i (v.getD b i)))
      (appendProjection D Sc cutoff i v w
        (affineUnit D Sc cutoff _ _ (appendQPFactor D Sc i v (v.getD b i) b) ≫ h)) =
    (appendQPUnit D Sc i (v.getD b i) : k) •
      appendOldCoordinate D Sc cutoff 0 x (appendProjection D Sc cutoff i v w h) := by
  let q : AppendIdx.Tail i v w := ⟨x.tailKey, x, rfl⟩
  have hk : q.representative.tailKey = x.tailKey := q.representative_tailKey
  have hs : (q.representative.shift (appendQPDegree D i (v.getD b i))).tailKey =
      (x.shift (appendQPDegree D i (v.getD b i))).tailKey := by
    exact congrArg (fun z => (appendQPDegree D i (v.getD b i) + z.1, z.2)) hk
  have H := appendQPFactor_top D Sc cutoff i v w b hb h q hm
  rw [appendOldCoordinateEquiv_apply] at H
  apply eq_of_heq
  exact (appendOldCoordinate_heq D Sc cutoff 0 _ _ hs _).symm.trans
    ((heq_of_eq H).trans (appendOldCoefficient_smul_heq D Sc cutoff
      (q.representative.oldTarget_eq_of_tailKey_eq x hk) _
      (appendOldCoordinate_heq D Sc cutoff 0 _ _ hk _)))

theorem appendQPOrdered_above (i : I) (v w : List I)
    (l : List ℕ) (hl : ∀ b ∈ l, b < v.length)
    (h : hom D Sc cutoff (v ++ [i]) w) (x : AppendIdx i v w)
    (hm : ∀ t ∈ (appendOldCoordinateEquiv D Sc cutoff 0 i v w
      (appendProjection D Sc cutoff i v w h)).support,
      (l.map (fun b => appendQPDegree D i (v.getD b i))).sum + t.1.1 < x.1.1) :
    appendOldCoordinate D Sc cutoff 0 x
      (appendProjection D Sc cutoff i v w
        (affineUnit D Sc cutoff _ _
          ((l.map fun b => appendQPFactor D Sc i v (v.getD b i) b).prod) ≫ h)) = 0 := by
  induction l generalizing h with
  | nil =>
    simp only [List.map_nil, List.prod_nil, End.one_def, affineUnit_id, Category.id_comp]
    let q : AppendIdx.Tail i v w := ⟨x.tailKey, x, rfl⟩
    have hz : (appendOldCoordinateEquiv D Sc cutoff 0 i v w
        (appendProjection D Sc cutoff i v w h)) q = 0 := by
      apply not_not.mp
      intro hn
      have hq := DFinsupp.mem_support_iff.mpr hn
      have H := hm q hq
      simp only [List.map_nil, List.sum_nil, zero_add] at H
      exact (Nat.lt_irrefl x.1.1) H
    rw [appendOldCoordinateEquiv_apply] at hz
    have hh := appendOldCoordinate_heq D Sc cutoff 0 q.representative x q.representative_tailKey
      (appendProjection D Sc cutoff i v w h)
    rw [hz] at hh
    have ht := q.representative.oldTarget_eq_of_tailKey_eq x q.representative_tailKey
    have H {t t' : List I} (e : t = t') {c : Old D Sc cutoff v t'}
        (hc : HEq (0 : Old D Sc cutoff v t) c) : c = 0 := by
      subst t'; exact (eq_of_heq hc).symm
    exact H ht hh
  | cons b l ih =>
    simp only [List.map_cons, List.prod_cons, End.mul_def, affineUnit_comp, Category.assoc]
    apply ih (fun c hc => hl c (List.mem_cons_of_mem b hc))
    intro t ht
    by_contra hn
    have hz := appendQPFactor_above D Sc cutoff i v w b (hl b (List.mem_cons_self)) h
      t.representative (by
        intro s hs
        have H := hm s hs
        have hk := congrArg Prod.fst t.representative_tailKey
        change t.representative.1.1 = t.1.1 at hk
        simp only [List.map_cons, List.sum_cons] at H
        omega)
    exact (DFinsupp.mem_support_iff.mp ht) (by
      rw [appendOldCoordinateEquiv_apply]
      exact hz)

theorem appendQPOrdered_top (i : I) (v w : List I)
    (l : List ℕ) (hl : ∀ b ∈ l, b < v.length)
    (h : hom D Sc cutoff (v ++ [i]) w) (x : AppendIdx i v w)
    (hm : ∀ t ∈ (appendOldCoordinateEquiv D Sc cutoff 0 i v w
      (appendProjection D Sc cutoff i v w h)).support, t.1.1 ≤ x.1.1) :
    appendOldCoordinate D Sc cutoff 0
      (x.shift (l.map (fun b => appendQPDegree D i (v.getD b i))).sum)
      (appendProjection D Sc cutoff i v w
        (affineUnit D Sc cutoff _ _
          ((l.map fun b => appendQPFactor D Sc i v (v.getD b i) b).prod) ≫ h)) =
    ((l.map (fun b => appendQPUnit D Sc i (v.getD b i))).prod : kˣ) •
      appendOldCoordinate D Sc cutoff 0 x (appendProjection D Sc cutoff i v w h) := by
  induction l generalizing h x with
  | nil =>
    have hx : x.shift 0 = x := by apply Subtype.ext; simp [AppendIdx.shift]
    simp only [List.map_nil, List.prod_nil, End.one_def,
      affineUnit_id, Category.id_comp, one_smul]
    exact eq_of_heq (appendOldCoordinate_heq D Sc cutoff 0 (x.shift 0) x
      (congrArg AppendIdx.tailKey hx) _)
  | cons b l ih =>
    let d := appendQPDegree D i (v.getD b i)
    have H := ih (fun c hc => hl c (List.mem_cons_of_mem b hc))
      (affineUnit D Sc cutoff _ _ (appendQPFactor D Sc i v (v.getD b i) b) ≫ h)
      (x.shift d) (by
        intro t ht
        by_contra hn
        have hz := appendQPFactor_above D Sc cutoff i v w b (hl b List.mem_cons_self) h
          t.representative (by
            intro s hs
            have Hs := hm s hs
            have hk := congrArg Prod.fst t.representative_tailKey
            change t.representative.1.1 = t.1.1 at hk
            change ¬ t.1.1 ≤ d + x.1.1 at hn
            dsimp only [d] at hn
            omega)
        exact (DFinsupp.mem_support_iff.mp ht) (by
          rw [appendOldCoordinateEquiv_apply]; exact hz))
    have hx : (x.shift d).shift (l.map (fun b => appendQPDegree D i (v.getD b i))).sum =
        x.shift ((b :: l).map (fun b => appendQPDegree D i (v.getD b i))).sum := by
      apply Subtype.ext
      simp only [AppendIdx.shift, List.map_cons, List.sum_cons]
      dsimp only [d]
      congr 1
      omega
    have hc := eq_of_heq (appendOldCoordinate_heq D Sc cutoff 0 _ _
      (congrArg AppendIdx.tailKey hx)
      (appendProjection D Sc cutoff i v w
        (affineUnit D Sc cutoff _ _
          ((l.map fun b => appendQPFactor D Sc i v (v.getD b i) b).prod) ≫
          affineUnit D Sc cutoff _ _ (appendQPFactor D Sc i v (v.getD b i) b) ≫ h)))
    rw [hc, appendQPFactor_top_at D Sc cutoff i v w b (hl b List.mem_cons_self) h x hm] at H
    change _ = ((l.map (fun b => appendQPUnit D Sc i (v.getD b i))).prod : k) •
      ((appendQPUnit D Sc i (v.getD b i) : k) •
        appendOldCoordinate D Sc cutoff 0 x (appendProjection D Sc cutoff i v w h)) at H
    rw [smul_smul, mul_comm] at H
    simp only [List.map_cons, List.prod_cons, End.mul_def, affineUnit_comp,
      Category.assoc, Units.smul_def, Units.val_mul]
    exact H

theorem appendQPProduct_top (i : I) (v w : List I)
    (h : hom D Sc cutoff (v ++ [i]) w) (x : AppendIdx i v w)
    (hm : ∀ t ∈ (appendOldCoordinateEquiv D Sc cutoff 0 i v w
      (appendProjection D Sc cutoff i v w h)).support, t.1.1 ≤ x.1.1) :
    appendOldCoordinate D Sc cutoff 0
      (x.shift ((List.range v.length).map (fun b => appendQPDegree D i (v.getD b i))).sum)
      (appendProjection D Sc cutoff i v w
        (affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫ h)) =
    (((List.range v.length).map (fun b => appendQPUnit D Sc i (v.getD b i))).prod : kˣ) •
      appendOldCoordinate D Sc cutoff 0 x (appendProjection D Sc cutoff i v w h) :=
  appendQPOrdered_top D Sc cutoff i v w _ (fun _ hb => List.mem_range.mp hb) h x hm

theorem endpointQP_top (i : I) (v w : List I)
    (h : hom D Sc cutoff (v ++ [i]) w) (q : AppendIdx.Tail i v w)
    (hm : ∀ t ∈ (appendOldCoordinateEquiv D Sc cutoff 0 i v w
      (appendProjection D Sc cutoff i v w h)).support, t.1.1 ≤ q.1.1) :
    appendOldCoordinate D Sc cutoff 0
      (q.representative.shift (cutoff i +
        ((List.range v.length).map (fun b => appendQPDegree D i (v.getD b i))).sum))
      (appendProjection D Sc cutoff i v w
        (affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫
          endpointELV D Sc cutoff i v ≫ h)) =
    (((List.range v.length).map (fun b => appendQPUnit D Sc i (v.getD b i))).prod : kˣ) •
      oldTwist D Sc cutoff (cutoff i • D.parity i) v q.representative.oldTarget
        ((appendOldCoordinateEquiv D Sc cutoff 0 i v w
          (appendProjection D Sc cutoff i v w h)) q) := by
  have H := appendQPProduct_top D Sc cutoff i v w
    (endpointELV D Sc cutoff i v ≫ h) (q.representative.shift (cutoff i)) (by
      intro t ht
      by_contra hn
      have hz := endpointELV_above D Sc cutoff i v w h t.representative (by
        intro s hs
        have Hs := hm s hs
        have hq := congrArg Prod.fst q.representative_tailKey
        have ht := congrArg Prod.fst t.representative_tailKey
        change q.representative.1.1 = q.1.1 at hq
        change t.representative.1.1 = t.1.1 at ht
        change ¬ t.1.1 ≤ cutoff i + q.representative.1.1 at hn
        omega)
      exact (DFinsupp.mem_support_iff.mp ht) (by
        rw [appendOldCoordinateEquiv_apply]; exact hz))
  rw [endpointELV_top D Sc cutoff i v w h q hm] at H
  have hk : ((q.representative.shift (cutoff i)).shift
      ((List.range v.length).map (fun b => appendQPDegree D i (v.getD b i))).sum).tailKey =
      (q.representative.shift (cutoff i +
        ((List.range v.length).map (fun b => appendQPDegree D i (v.getD b i))).sum)).tailKey := by
    apply Prod.ext
    · change _ + (cutoff i + _) = cutoff i + _ + _
      omega
    · rfl
  have hc := eq_of_heq (appendOldCoordinate_heq D Sc cutoff 0 _ _ hk
    (appendProjection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫
        endpointELV D Sc cutoff i v ≫ h)))
  rw [hc] at H
  exact H

theorem endpointQP_above (i : I) (v w : List I)
    (h : hom D Sc cutoff (v ++ [i]) w) (x : AppendIdx i v w)
    (hm : ∀ t ∈ (appendOldCoordinateEquiv D Sc cutoff 0 i v w
      (appendProjection D Sc cutoff i v w h)).support,
      cutoff i + ((List.range v.length).map
        (fun b => appendQPDegree D i (v.getD b i))).sum + t.1.1 < x.1.1) :
    appendOldCoordinate D Sc cutoff 0 x
      (appendProjection D Sc cutoff i v w
        (affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫
          endpointELV D Sc cutoff i v ≫ h)) = 0 := by
  apply appendQPOrdered_above D Sc cutoff i v w (List.range v.length)
    (fun _ hb => List.mem_range.mp hb) (endpointELV D Sc cutoff i v ≫ h) x
  intro t ht
  by_contra hn
  have hz := endpointELV_above D Sc cutoff i v w h t.representative (by
    intro s hs
    have Hs := hm s hs
    have hk := congrArg Prod.fst t.representative_tailKey
    change t.representative.1.1 = t.1.1 at hk
    omega)
  exact (DFinsupp.mem_support_iff.mp ht) (by
    rw [appendOldCoordinateEquiv_apply]; exact hz)

def endpointQPDegree (i : I) (v : List I) : ℕ := cutoff i +
  ((List.range v.length).map (fun b => appendQPDegree D i (v.getD b i))).sum

def appendQPProductUnit (i : I) (v : List I) : kˣ :=
  ((List.range v.length).map (fun b => appendQPUnit D Sc i (v.getD b i))).prod

theorem appendOldCoefficient_zero_heq {v t t' : List I} (e : t = t')
    {b : Old D Sc cutoff v t} {c : Old D Sc cutoff v t'}
    (h : HEq b c) (hb : b = 0) : c = 0 := by
  subst t'; exact (eq_of_heq h).symm.trans hb

/-- Actual signed single-tail cancellation, with a remainder strictly below
its original moving degree. The quotient is an actual append Hom. -/
theorem endpointQP_single_step (i : I) (v w : List I)
    (q : AppendIdx.Tail i v w) (z : AppendTarget D Sc cutoff i v w)
    (hz : ∀ x : AppendIdx i v w,
      x.tailKey ≠ (q.representative.shift (endpointQPDegree D cutoff i v)).tailKey →
      appendOldCoordinate D Sc cutoff 0 x z = 0) :
    ∃ (g : hom D Sc cutoff (v ++ [i]) w) (r : AppendTarget D Sc cutoff i v w),
      z = appendProjection D Sc cutoff i v w
        (affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫
          endpointELV D Sc cutoff i v ≫ g) + r ∧
      ∀ t ∈ (appendOldCoordinateEquiv D Sc cutoff 0 i v w r).support,
        t.1.1 < endpointQPDegree D cutoff i v + q.1.1 := by
  let N := endpointQPDegree D cutoff i v
  let U := appendQPProductUnit D Sc i v
  let E := appendOldCoordinateEquiv D Sc cutoff 0 i v w
  let b := appendOldCoordinate D Sc cutoff 0 (q.representative.shift N) z
  let c := (U⁻¹ : kˣ) • oldTwist D Sc cutoff (cutoff i • D.parity i)
    v q.representative.oldTarget b
  obtain ⟨g, hg⟩ := appendProjection_surjective D Sc cutoff i v w
    (E.symm (DFinsupp.single q c))
  have hgc : E (appendProjection D Sc cutoff i v w g) = DFinsupp.single q c := by
    rw [hg]; exact E.apply_symm_apply _
  have hbound : ∀ t ∈ (E (appendProjection D Sc cutoff i v w g)).support,
      t.1.1 ≤ q.1.1 := by
    intro t ht
    rw [hgc] at ht
    have htq : t = q := by
      by_contra h
      exact (DFinsupp.mem_support_iff.mp ht) (DFinsupp.single_eq_of_ne h)
    subst t; exact le_rfl
  let a := appendProjection D Sc cutoff i v w
    (affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫
      endpointELV D Sc cutoff i v ≫ g)
  have htop (s : AppendIdx.Tail i v w) (hs : q.1.1 ≤ s.1.1) :
      appendOldCoordinate D Sc cutoff 0 (s.representative.shift N) (z - a) = 0 := by
    have H := endpointQP_top D Sc cutoff i v w g s
      (fun t ht => (hbound t ht).trans hs)
    change appendOldCoordinate D Sc cutoff 0 (s.representative.shift N) a =
      (U : kˣ) • oldTwist D Sc cutoff (cutoff i • D.parity i)
        v s.representative.oldTarget (E (appendProjection D Sc cutoff i v w g) s) at H
    rw [hgc] at H
    rw [map_sub, H]
    by_cases hsq : s = q
    · subst s
      rw [DFinsupp.single_eq_same]
      change b - U • oldTwist D Sc cutoff _ _ _ (U⁻¹ • oldTwist D Sc cutoff _ _ _ b) = 0
      simp only [Units.smul_def, map_smul, oldTwist_twice, smul_smul,
        ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul, sub_self]
    · rw [DFinsupp.single_eq_of_ne hsq, map_zero, smul_zero]
      change appendOldCoordinate D Sc cutoff 0 (s.representative.shift N) z -
        (0 : Old D Sc cutoff v (s.representative.shift N).oldTarget) = 0
      rw [sub_zero]
      apply hz
      intro he
      apply hsq
      apply Subtype.ext
      have h1 := congrArg Prod.fst he
      have h2 := congrArg Prod.snd he
      have sk := s.representative_tailKey
      have qk := q.representative_tailKey
      apply Prod.ext
      · have sk1 := congrArg Prod.fst sk
        have qk1 := congrArg Prod.fst qk
        change N + s.representative.1.1 = N + q.representative.1.1 at h1
        change s.representative.1.1 = s.1.1 at sk1
        change q.representative.1.1 = q.1.1 at qk1
        omega
      · change s.representative.tailKey.2 = q.representative.tailKey.2 at h2
        exact (congrArg Prod.snd sk).symm.trans (h2.trans (congrArg Prod.snd qk))
  refine ⟨g, z - a, ?_, ?_⟩
  · change z = a + (z - a); abel
  · intro t ht
    by_contra hn
    let x := t.representative
    let y : AppendIdx i v w := ⟨(x.1.1 - N, x.1.2), x.2⟩
    let s : AppendIdx.Tail i v w := ⟨y.tailKey, y, rfl⟩
    have tx : x.1.1 = t.1.1 := congrArg Prod.fst t.representative_tailKey
    have hxy : (s.representative.shift N).tailKey = x.tailKey := by
      have sk := s.representative_tailKey
      apply Prod.ext
      · have sk1 := congrArg Prod.fst sk
        change s.representative.1.1 = x.1.1 - N at sk1
        change N + s.representative.1.1 = x.1.1
        change ¬ t.1.1 < N + q.1.1 at hn
        omega
      · change s.representative.tailKey.2 = s.val.2
        exact congrArg Prod.snd sk
    have hs : q.1.1 ≤ s.1.1 := by
      change q.1.1 ≤ x.1.1 - N
      change ¬ t.1.1 < N + q.1.1 at hn
      omega
    have H := appendOldCoordinate_heq D Sc cutoff 0 _ _ hxy (z - a)
    have Hzero := appendOldCoefficient_zero_heq D Sc cutoff
      ((s.representative.shift N).oldTarget_eq_of_tailKey_eq x hxy) H (htop s hs)
    exact (DFinsupp.mem_support_iff.mp ht) (by
      rw [appendOldCoordinateEquiv_apply]; exact Hzero)

/-- Every actual single old-Hom coordinate at degree at least N admits
one division step whose entire remainder has strictly smaller moving degree. -/
theorem endpointQP_single_division (i : I) (v w : List I)
    (t : AppendIdx.Tail i v w)
    (b : Old D Sc cutoff v t.representative.oldTarget)
    (hm : endpointQPDegree D cutoff i v ≤ t.1.1) :
    ∃ (g : hom D Sc cutoff (v ++ [i]) w) (r : AppendTarget D Sc cutoff i v w),
      (appendOldCoordinateEquiv D Sc cutoff 0 i v w).symm (DFinsupp.single t b) =
        appendProjection D Sc cutoff i v w
          (affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫
            endpointELV D Sc cutoff i v ≫ g) + r ∧
      ∀ s ∈ (appendOldCoordinateEquiv D Sc cutoff 0 i v w r).support, s.1.1 < t.1.1 := by
  let N := endpointQPDegree D cutoff i v
  let x := t.representative
  let y : AppendIdx i v w := ⟨(x.1.1 - N, x.1.2), x.2⟩
  let q : AppendIdx.Tail i v w := ⟨y.tailKey, y, rfl⟩
  have tx : x.1.1 = t.1.1 := congrArg Prod.fst t.representative_tailKey
  have hdeg : N + q.1.1 = t.1.1 := by
    change N + (x.1.1 - N) = t.1.1
    change N ≤ t.1.1 at hm
    omega
  have hkey : (q.representative.shift N).tailKey = t.val := by
    have hk := q.representative_tailKey
    apply Prod.ext
    · have hk1 := congrArg Prod.fst hk
      change q.representative.1.1 = q.1.1 at hk1
      change N + q.representative.1.1 = t.1.1
      omega
    · change q.representative.tailKey.2 = t.val.2
      have hq2 : q.val.2 = t.val.2 := by
        change t.representative.tailKey.2 = t.val.2
        exact congrArg Prod.snd t.representative_tailKey
      exact (congrArg Prod.snd hk).trans hq2
  let E := appendOldCoordinateEquiv D Sc cutoff 0 i v w
  obtain ⟨g, r, hr, hb⟩ := endpointQP_single_step D Sc cutoff i v w q
    (E.symm (DFinsupp.single t b)) (by
      intro a ha
      let s : AppendIdx.Tail i v w := ⟨a.tailKey, a, rfl⟩
      have hst : s ≠ t := by
        intro h
        apply ha
        exact (congrArg Subtype.val h).trans hkey.symm
      have hz : E (E.symm (DFinsupp.single t b)) s = 0 := by
        rw [E.apply_symm_apply]
        exact DFinsupp.single_eq_of_ne hst
      rw [appendOldCoordinateEquiv_apply] at hz
      exact appendOldCoefficient_zero_heq D Sc cutoff
        (s.representative.oldTarget_eq_of_tailKey_eq a s.representative_tailKey)
        (appendOldCoordinate_heq D Sc cutoff 0 _ _ s.representative_tailKey _) hz)
  refine ⟨g, r, hr, ?_⟩
  intro s hs
  have H := hb s hs
  change s.1.1 < N + q.1.1 at H
  exact hdeg ▸ H

/-- Signed right division in arbitrary old-Hom coordinates. -/
theorem endpointQP_division (i : I) (v w : List I)
    (z : AppendTarget D Sc cutoff i v w) :
    ∃ (g : hom D Sc cutoff (v ++ [i]) w) (r : AppendTarget D Sc cutoff i v w),
      z = appendProjection D Sc cutoff i v w
        (affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫
          endpointELV D Sc cutoff i v ≫ g) + r ∧
      ∀ t ∈ (appendOldCoordinateEquiv D Sc cutoff 0 i v w r).support,
        t.1.1 < endpointQPDegree D cutoff i v := by
  let E := appendOldCoordinateEquiv D Sc cutoff 0 i v w
  let A := fun g : hom D Sc cutoff (v ++ [i]) w =>
    appendProjection D Sc cutoff i v w
      (affineUnit D Sc cutoff _ _ (appendQPProduct D Sc i v) ≫
        endpointELV D Sc cutoff i v ≫ g)
  let P := fun a : AppendTarget D Sc cutoff i v w =>
    ∃ g r, a = A g + r ∧ ∀ t ∈ (E r).support, t.1.1 < endpointQPDegree D cutoff i v
  have A0 : A 0 = 0 := by simp [A]
  have Aadd (g h) : A (g + h) = A g + A h := by
    simp only [A, Preadditive.comp_add, map_add]
  have low (a) (ha : ∀ t ∈ (E a).support, t.1.1 < endpointQPDegree D cutoff i v) : P a := by
    exact ⟨0, a, by rw [A0, zero_add], ha⟩
  have padd (a b) (ha : P a) (hb : P b) : P (a + b) := by
    obtain ⟨g, r, hr, hdeg⟩ := ha
    obtain ⟨h, s, hs, hdeg'⟩ := hb
    refine ⟨g + h, r + s, ?_, ?_⟩
    · rw [hr, hs, Aadd]; abel
    · intro t ht
      rw [map_add] at ht
      rcases Finset.mem_union.mp (DFinsupp.support_add ht) with ht | ht
      · exact hdeg t ht
      · exact hdeg' t ht
  have bounded (n : ℕ) : ∀ a : AppendTarget D Sc cutoff i v w,
      (∀ t ∈ (E a).support, t.1.1 < n) → P a := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro a
      obtain ⟨f, rfl⟩ := E.symm.surjective a
      induction f using DFinsupp.induction with
      | h0 =>
        intro _
        apply low
        simp only [map_zero, DFinsupp.support_zero, Finset.notMem_empty, false_implies,
          implies_true]
      | @ha t b f hft hb hf =>
        intro hbound
        have htb : t.1.1 < n := hbound t (by
          rw [E.apply_symm_apply, DFinsupp.mem_support_iff]
          simpa only [DFinsupp.add_apply, DFinsupp.single_eq_same, hft, add_zero] using hb)
        have hfb : ∀ s ∈ f.support, s.1.1 < n := by
          intro s hs
          have hst : s ≠ t := by
            intro h; subst s; exact (DFinsupp.mem_support_iff.mp hs) hft
          apply hbound s
          rw [E.apply_symm_apply, DFinsupp.mem_support_iff]
          simpa only [DFinsupp.add_apply, DFinsupp.single_eq_of_ne hst, zero_add]
            using (DFinsupp.mem_support_iff.mp hs)
        have hsingle : P (E.symm (DFinsupp.single t b)) := by
          by_cases ht : endpointQPDegree D cutoff i v ≤ t.1.1
          · obtain ⟨g, r, hr, hdeg⟩ :=
              endpointQP_single_division D Sc cutoff i v w t b ht
            obtain ⟨h, s, hs, hds⟩ := ih t.1.1 htb r hdeg
            refine ⟨g + h, s, ?_, hds⟩
            change E.symm (DFinsupp.single t b) = A g + r at hr
            rw [hr, hs, Aadd]; abel
          · apply low
            intro s hs
            rw [E.apply_symm_apply] at hs
            have hst : s = t := Finset.mem_singleton.mp (DFinsupp.support_single_subset hs)
            subst s
            exact Nat.lt_of_not_ge ht
        rw [map_add]
        exact padd _ _ hsingle (hf (by simpa only [E.apply_symm_apply] using hfb))
  apply bounded ((E z).support.sup (fun t => t.1.1) + 1) z
  intro t ht
  exact Nat.lt_succ_of_le (Finset.le_sup (f := fun t => t.1.1) ht)

theorem appendQPInverseUnit_mul_productUnit (i : I) (v : List I) :
    appendQPInverseUnit D Sc i v * appendQPProductUnit D Sc i v = 1 := by
  unfold appendQPInverseUnit appendQPProductUnit
  have H (l : List ℕ) :
      ((l.map fun b => (appendQPUnit D Sc i (v.getD b i))⁻¹).prod) *
        ((l.map fun b => appendQPUnit D Sc i (v.getD b i)).prod) = 1 := by
    induction l with
    | nil => simp
    | cons b l ih =>
      simp only [List.map_cons, List.prod_cons]
      rw [mul_mul_mul_comm, inv_mul_cancel, one_mul, ih]
  exact H _

/-- The normalized literal numerator has precisely the invertible total old-Hom twist
as its highest action, not an assumed identity action on exterior coefficients. -/
theorem normalizedEndpointQPNumerator_top (i : I) (v w : List I)
    (h : hom D Sc cutoff (v ++ [i]) w) (q : AppendIdx.Tail i v w)
    (hm : ∀ t ∈ (appendOldCoordinateEquiv D Sc cutoff 0 i v w
      (appendProjection D Sc cutoff i v w h)).support, t.1.1 ≤ q.1.1) :
    appendOldCoordinate D Sc cutoff 0 (q.representative.shift (endpointQPDegree D cutoff i v))
      (appendProjection D Sc cutoff i v w
        (normalizedEndpointQPNumerator D Sc cutoff i v ≫ h)) =
      oldTwist D Sc cutoff (cutoff i • D.parity i) v q.representative.oldTarget
        ((appendOldCoordinateEquiv D Sc cutoff 0 i v w
          (appendProjection D Sc cutoff i v w h)) q) := by
  rw [normalizedEndpointQPNumerator_eq, Linear.smul_comp, map_smul, map_smul,
    Category.assoc]
  unfold endpointQPDegree
  rw [endpointQP_top D Sc cutoff i v w h q hm]
  change (appendQPInverseUnit D Sc i v : k) •
    ((appendQPProductUnit D Sc i v : k) •
      oldTwist D Sc cutoff (cutoff i • D.parity i) v q.representative.oldTarget
        ((appendOldCoordinateEquiv D Sc cutoff 0 i v w
          (appendProjection D Sc cutoff i v w h)) q)) = _
  rw [smul_smul, ← Units.val_mul, appendQPInverseUnit_mul_productUnit, Units.val_one, one_smul]

end OddMath.QuiverHecke.ELVOld
