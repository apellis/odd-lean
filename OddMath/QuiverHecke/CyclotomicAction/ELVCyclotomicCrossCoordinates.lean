/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVCyclotomicShortColumns
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendC0Candidate

/-! # Balanced crossing-column coordinates

`decode_comp_shortCross` proves a left inverse on every balanced class.
`range_shortCross` and `crossingEquiv` identify that independently prescribed
source with the original append crossing span. These are the crossing-column
prerequisites for the short-column diagram in `DeformedCyclotomicTopRow.md`.

The decoder takes values in the prescribed balanced short source. On a
nonidentity append tail it retains the crossing term of the triangular
crossing/dot identity, including its self-crossing sign. The polynomial
correction is killed only after its separate vanishing law is proved.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped Classical DirectSum TensorProduct
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
namespace ShortCrossCoordinates
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Insert a shorter crossing word with its unchanged old quotient coefficient. -/
def wordLift (i : I) (v q s t : List I) (hs : q = s ++ [i])
    (L : List PG) (m : ℕ) (ht : SChain (s ++ [i]) (pl (s ++ [i]) L) t) :
    Old D Sc cutoff v q →ₗ[k] ShortTarget D Sc cutoff i v t := by
  subst q
  exact (BalancedInduction.inclusion (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩ ⟨s⟩) ∘ₗ
      TensorProduct.mk k _ _ (appendMovingPower D Sc cutoff i s m ≫
        affineUnit D Sc cutoff _ _ (cl D Sc _ _ L ht))

/-- Decode the crossing part of a normalized append tail. -/
def data (i : I) (v q t : List I) (L : List PG) (m : ℕ) :
    Old D Sc cutoff v q →ₗ[k] ShortTarget D Sc cutoff i v t := by
  by_cases hL : L = []
  · exact 0
  · by_cases hs : q = q.dropLast ++ [i]
    · by_cases ht : SChain (q.dropLast ++ [i]) (pl (q.dropLast ++ [i]) L.tail) t
      · exact SKM.zsign k (D.parity i * D.parity i) ^ m •
          wordLift D Sc cutoff i v q q.dropLast t hs L.tail m ht
      · exact 0
    · exact 0

/-- Full old quotient coordinates are decoded without choosing representatives in the ideal. -/
def decode (i : I) (v t : List I) :
    AppendTarget D Sc cutoff i v (t ++ [i]) →ₗ[k] ShortTarget D Sc cutoff i v t :=
  (DirectSum.toModule k _ _ fun q : AppendIdx.Tail i v (t ++ [i]) =>
    data D Sc cutoff i v q.representative.oldTarget t
      (cw (Categorification.TypeA.canWord (v ++ [i]).length
        q.representative.1.2.2.2.1⁻¹)) q.representative.1.1) ∘ₗ
      (appendOldCoordinateEquiv D Sc cutoff 0 i v (t ++ [i])).toLinearMap

@[simp] theorem data_nil (i : I) (v q t : List I) (m : ℕ) :
    data D Sc cutoff i v q t [] m = 0 := by
  simp [data]

private theorem appendTailPair_transport {i : I} {v s s' w : List I}
    (e : s = s') (r : hom D Sc cutoff v s)
    (a : (pres D Sc).obj (ob D (s ++ [i])) ⟶ (pres D Sc).obj (ob D w))
    (b : (pres D Sc).obj (ob D (s' ++ [i])) ⟶ (pres D Sc).obj (ob D w))
    (hab : HEq a b) :
    appendPair D Sc cutoff 0 i (affineUnit D Sc cutoff _ _ a)
      ((ideal D Sc cutoff v s).mkQ r) =
    appendPair D Sc cutoff 0 i (affineUnit D Sc cutoff _ _ b)
      ((ideal D Sc cutoff v s').mkQ (e ▸ r)) := by
  subst s'
  cases hab
  rfl

private def appendIdentityShuffle (i : I) (v : List I) : AppendShuffle (appendLen v i) :=
  AppendShuffle.cast rfl (appendLen v i) (appendRun v.length (Fin.last v.length))

private theorem appendIdentityShuffle_word (i : I) (v : List I) :
    Categorification.TypeA.canWord (v ++ [i]).length (appendIdentityShuffle i v).1⁻¹ = [] := by
  rw [appendIdentityShuffle, AppendShuffle.canWord_cast, canWord_appendRun]
  simp

private def appendIdentityIndex (i : I) {v t : List I} (y : NFIdx v t) (m : ℕ) :
    AppendIdx i v (t ++ [i]) :=
  ⟨(m, y.1.1, y.1.2, appendIdentityShuffle i v), y.2.1, y.2.2.1, by
    have he := tgt_append_right [i] (t := v)
      (fits_cw (Categorification.TypeA.validWord_canWord v.length y.1.2))
    simpa only [appendCrossingWord, appendIdentityShuffle_word, List.append_nil,
      cw_append, tgt_append, cw, List.reverse_nil, List.map_nil,
      List.nil_append] using he.trans (congrArg (· ++ [i]) y.tgt_cw)⟩

private theorem appendIdentityIndex_target (i : I) {v t : List I} (y : NFIdx v t) (m : ℕ) :
    (appendIdentityIndex i y m).oldTarget = t := y.tgt_cw

private theorem append_cl_heq {s s' t t' : List I} {L L' : List PG}
    (hs : s = s') (ht : t = t') (hL : L = L')
    (h : SChain s (pl s L) t) (h' : SChain s' (pl s' L') t') :
    HEq (cl D Sc s t L h) (cl D Sc s' t' L' h') := by
  subst s'
  subst t'
  subst L'
  rfl

private theorem appendIdentityIndex_tail (i : I) {v t : List I}
    (y : NFIdx v t) (m : ℕ) :
    HEq (appendTail D Sc (appendIdentityIndex i y m))
      ((dotE D Sc (t ++ [i]) t.length) ^ m) := by
  have ht := appendIdentityIndex_target i y m
  have hl : v.length = t.length := by
    have he := congrArg List.length y.tgt_cw
    simpa only [length_tgt] using he
  unfold appendTail
  rw [dotE_pow]
  apply append_cl_heq D Sc (congrArg (· ++ [i]) ht) rfl
  simp only [appendIdentityIndex, appendIdentityShuffle_word, cw,
    List.reverse_nil, List.map_nil, List.append_nil, List.map_replicate, hl]


private theorem appendTail_cross_heq (i : I) (v s t : List I)
    (x : AppendIdx i v (t ++ [i])) (e : x.oldTarget = s ++ [i])
    (L : List PG)
    (hw : cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) =
      PG.cross s.length :: L)
    (hf : Fits (s ++ [i]).length L)
    (h : SChain (s ++ [i]) (pl (s ++ [i]) L) t) :
    HEq (appendTail D Sc x)
      (((dotE D Sc (s ++ [i] ++ [i]) (s.length + 1)) ^ x.1.1) ≫
        crossLast D Sc s i i ≫ affineRightContext D Sc [i] _ _ (cl D Sc _ _ L h)) := by
  have hl : v.length = s.length + 1 := by
    have hh := congrArg List.length e
    simpa only [AppendIdx.oldTarget, length_tgt, List.length_append,
      List.length_singleton] using hh
  change HEq (appendTail D Sc x)
    (_ ≫ crossLast D Sc s i i ≫ (cl D Sc _ _ L h ▷ (pres D Sc).obj (ob D [i])))
  rw [dotE_pow, crossLast, cl_whiskerRight D Sc _ _ [i] hf, cl_comp, cl_comp]
  unfold appendTail
  apply append_cl_heq D Sc (congrArg (· ++ [i]) e) rfl
  simp only [hw, hl, List.map_replicate, List.singleton_append]

private def appendShuffleSizeCast {n n' : ℕ} (e : n = n') :
    AppendShuffle (show n + 1 = n + 1 from rfl) ≃
      AppendShuffle (show n' + 1 = n' + 1 from rfl) := by
  subst n'
  exact Equiv.refl _

private theorem appendShuffleSizeCast_word {n n' : ℕ} (e : n = n')
    (d : AppendShuffle (show n + 1 = n + 1 from rfl)) :
    Categorification.TypeA.canWord (n' + 1) (appendShuffleSizeCast e d).1⁻¹ =
    Categorification.TypeA.canWord (n + 1) d.1⁻¹ := by
  subst n'
  rfl

private def appendIndexWithTail (i : I) {v u w : List I} (y : NFIdx v u)
    (d : AppendShuffle (appendLen v i)) (m : ℕ)
    (h : tgt (u ++ [i]) (cw (Categorification.TypeA.canWord (v ++ [i]).length d.1⁻¹)) = w) :
    AppendIdx i v w :=
  ⟨(m, y.1.1, y.1.2, d), y.2.1, y.2.2.1, by
    rw [appendCrossingWord, cw_append, tgt_append,
      tgt_append_right [i] (fits_cw (Categorification.TypeA.validWord_canWord v.length y.1.2)),
      y.tgt_cw]
    exact h⟩

private theorem appendIndexWithTail_target (i : I) {v u w : List I} (y : NFIdx v u)
    (d : AppendShuffle (appendLen v i)) (m : ℕ)
    (h : tgt (u ++ [i]) (cw (Categorification.TypeA.canWord (v ++ [i]).length d.1⁻¹)) = w) :
    (appendIndexWithTail i y d m h).oldTarget = u := y.tgt_cw

private theorem appendTail_cross_chain {i : I} {s t : List I} (z : AppendIdx i s t) :
    SChain (z.oldTarget ++ [i])
      (pl (z.oldTarget ++ [i]) (cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹))) t := by
  have hz := z.2.2.2
  rw [appendCrossingWord, cw_append, tgt_append,
    tgt_append_right [i] (fits_cw (Categorification.TypeA.validWord_canWord s.length z.1.2.2.1))] at hz
  change tgt (z.oldTarget ++ [i])
    (cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹)) = t at hz
  simpa only [hz] using sChain_pl (z.oldTarget ++ [i])
    (cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹))

private theorem appendTail_cross_fits {i : I} {s t : List I} (z : AppendIdx i s t) :
    Fits (z.oldTarget ++ [i]).length
      (cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹)) := by
  simpa only [AppendIdx.oldTarget, List.length_append, length_tgt] using
    fits_cw (Categorification.TypeA.validWord_canWord (s ++ [i]).length z.1.2.2.2.1⁻¹)

private theorem appendRunWord_castSucc (n : ℕ) (j : Fin (n + 1)) :
    cw (Categorification.TypeA.canWord (n + 2) (appendRun (n + 1) j.castSucc).1⁻¹) =
      PG.cross n :: cw (Categorification.TypeA.canWord (n + 1) (appendRun n j).1⁻¹) := by
  rw [canWord_appendRun, canWord_appendRun, Fin.val_castSucc]
  have hj : j.val ≤ n := Nat.lt_succ_iff.mp j.2
  rw [show n + 1 - j.val = (n - j.val) + 1 by omega, List.range'_concat, cw_append]
  simp only [cw, List.reverse_singleton, List.map_singleton, List.cons_append, List.nil_append]
  congr 2
  omega

private theorem appendCrossingShuffle_exists (i : I) (v s t : List I)
    (z : AppendIdx i s t) (hv : s.length + 1 = v.length) :
    ∃ d : AppendShuffle (appendLen v i),
      cw (Categorification.TypeA.canWord (v ++ [i]).length d.1⁻¹) =
        PG.cross s.length ::
          cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹) := by
  let d0 := AppendShuffle.cast (appendLen s i) rfl z.1.2.2.2
  let j := (appendRunEquiv s.length).symm d0
  let d1 := appendShuffleSizeCast hv (appendRun (s.length + 1) j.castSucc)
  refine ⟨AppendShuffle.cast rfl (appendLen v i) d1, ?_⟩
  rw [AppendShuffle.canWord_cast, appendShuffleSizeCast_word]
  rw [appendRunWord_castSucc]
  have hj : appendRun s.length j = d0 := (appendRunEquiv s.length).apply_symm_apply d0
  rw [hj, AppendShuffle.canWord_cast]

private theorem appendTail_power_cross (i : I) (s t : List I) (z : AppendIdx i s t) :
    affineUnit D Sc cutoff _ _ (appendTail D Sc z) =
      appendMovingPower D Sc cutoff i z.oldTarget z.1.1 ≫
        affineUnit D Sc cutoff _ _
          (cl D Sc _ _ (cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹))
            (appendTail_cross_chain z)) := by
  have hl : z.oldTarget.length = s.length := by simp only [AppendIdx.oldTarget, length_tgt]
  unfold appendMovingPower
  rw [← affineUnit_comp]
  apply congrArg (affineUnit D Sc cutoff _ _)
  unfold appendTail
  rw [dotE_pow, cl_comp]
  apply eq_of_heq
  apply append_cl_heq D Sc rfl rfl
  simp only [hl, List.map_replicate]


@[simp] theorem data_cross (i : I) (v s t : List I) (L : List PG) (m : ℕ)
    (h : SChain (s ++ [i]) (pl (s ++ [i]) L) t)
    (b : Old D Sc cutoff v (s ++ [i])) :
    data D Sc cutoff i v (s ++ [i]) t (PG.cross s.length :: L) m b =
      SKM.zsign k (D.parity i * D.parity i) ^ m •
        shortTensor D Sc cutoff i v s t
          (appendMovingPower D Sc cutoff i s m ≫
            affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h)) b := by
  dsimp only [data]
  rw [dite_eq_right (List.cons_ne_nil _ _)]
  have he : (s ++ [i]).dropLast = s := List.dropLast_concat
  rw [dite_eq_left (congrArg (· ++ [i]) he).symm]
  have ht : SChain ((s ++ [i]).dropLast ++ [i])
      (pl ((s ++ [i]).dropLast ++ [i]) (PG.cross s.length :: L).tail) t := by
    simpa only [he, List.tail_cons] using h
  rw [dite_eq_left ht, LinearMap.smul_apply]
  congr 1
  have aux (s' : List I) (e : s' = s) (hs : s ++ [i] = s' ++ [i])
      (hc : SChain (s' ++ [i]) (pl (s' ++ [i]) L) t) :
      wordLift D Sc cutoff i v (s ++ [i]) s' t hs L m hc b =
        shortTensor D Sc cutoff i v s t
          (appendMovingPower D Sc cutoff i s m ≫
            affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h)) b := by
    subst s'; rfl
  exact aux _ he _ ht

theorem decode_pair_representative (i : I) (v t : List I)
    (q : AppendIdx.Tail i v (t ++ [i]))
    (b : Old D Sc cutoff v q.representative.oldTarget) :
    decode D Sc cutoff i v t
      (appendPair D Sc cutoff 0 i (affineUnit D Sc cutoff _ _
        (appendTail D Sc q.representative)) b) =
    data D Sc cutoff i v q.representative.oldTarget t
      (cw (Categorification.TypeA.canWord (v ++ [i]).length
        q.representative.1.2.2.2.1⁻¹)) q.representative.1.1 b := by
  have he : decode D Sc cutoff i v t
      (appendOldReconstruct D Sc cutoff 0 i v (t ++ [i]) (DirectSum.lof k _ _ q b)) =
      data D Sc cutoff i v q.representative.oldTarget t
        (cw (Categorification.TypeA.canWord (v ++ [i]).length
          q.representative.1.2.2.2.1⁻¹)) q.representative.1.1 b := by
    simp only [decode, LinearMap.comp_apply, LinearEquiv.coe_coe,
      appendOldCoordinateEquiv_reconstruct, DirectSum.toModule_lof]
  have hu : affineUnit D Sc cutoff _ _ (appendTail D Sc q.representative) =
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
        appendTail D Sc q.representative : hom D Sc cutoff
          (q.representative.oldTarget ++ [i]) (t ++ [i])) := rfl
  rw [hu]
  simpa only [appendOldReconstruct, DirectSum.toModule_lof] using he

private theorem data_transport (i : I) {v s s' t : List I}
    (e : s = s') (L : List PG) (m : ℕ) (r : hom D Sc cutoff v s) :
    data D Sc cutoff i v s t L m ((ideal D Sc cutoff v s).mkQ r) =
    data D Sc cutoff i v s' t L m ((ideal D Sc cutoff v s').mkQ (e ▸ r)) := by
  subst s'; rfl

/-- Repeated old normal forms with the same tail give the same decoded balanced class. -/
theorem decode_pair (i : I) (v t : List I)
    (x : AppendIdx i v (t ++ [i])) (r : hom D Sc cutoff v x.oldTarget) :
    decode D Sc cutoff i v t
      (appendPair D Sc cutoff 0 i (affineUnit D Sc cutoff _ _ (appendTail D Sc x))
        ((ideal D Sc cutoff v x.oldTarget).mkQ r)) =
    data D Sc cutoff i v x.oldTarget t
      (cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹)) x.1.1
        ((ideal D Sc cutoff v x.oldTarget).mkQ r) := by
  let q : AppendIdx.Tail i v (t ++ [i]) := ⟨x.tailKey, x, rfl⟩
  have hk : x.tailKey = q.representative.tailKey := q.representative_tailKey.symm
  have ht := x.oldTarget_eq_of_tailKey_eq q.representative hk
  rw [appendTailPair_transport D Sc cutoff ht r _ _
    (appendTail_heq_of_tailKey_eq D Sc x q.representative hk), decode_pair_representative]
  have hm := congrArg Prod.fst hk
  have hd := congrArg Prod.snd hk
  change x.1.1 = q.representative.1.1 at hm
  change x.1.2.2.2 = q.representative.1.2.2.2 at hd
  rw [← hm, ← hd]
  exact (data_transport D Sc cutoff i ht _ _ r).symm

/-- Identity output tails have zero crossing coordinate. -/
theorem decode_embedding_single (i : I) (v t : List I) (m : ℕ)
    (g : hom D Sc cutoff v t) :
    decode D Sc cutoff i v t
      (appendOutputEmbedding D Sc cutoff i v t
        (Finsupp.single m ((ideal D Sc cutoff v t).mkQ g))) = 0 := by
  by_cases hg : g = 0
  · simp [hg]
  obtain ⟨y⟩ := exists_oldIndex_of_ne_zero D Sc cutoff g hg
  let x := appendIdentityIndex i y m
  have ht : x.oldTarget = t := appendIdentityIndex_target i y m
  let r : hom D Sc cutoff v x.oldTarget := ht.symm ▸ g
  have hr : ht ▸ r = g := by
    exact (show ∀ {a b : List I} (e : a = b) (z : hom D Sc cutoff v b),
      e ▸ (e.symm ▸ z : hom D Sc cutoff v a) = z from
        by intro a b e z; cases e; rfl) ht g
  have he := appendTailPair_transport D Sc cutoff ht r
    (appendTail D Sc x) ((dotE D Sc (t ++ [i]) t.length) ^ m)
    (appendIdentityIndex_tail D Sc i y m)
  rw [hr] at he
  have hc := decode_pair D Sc cutoff i v t x r
  rw [he] at hc
  have hw : cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) = [] := by
    simp only [x, appendIdentityIndex, appendIdentityShuffle_word, cw,
      List.reverse_nil, List.map_nil]
  rw [hw, data_nil, LinearMap.zero_apply] at hc
  simpa only [appendOutputEmbedding_single, appendPair_mk, twist_zero,
    appendMovingPower, x, appendIdentityIndex] using hc

theorem decode_embedding (i : I) (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    decode D Sc cutoff i v t (appendOutputEmbedding D Sc cutoff i v t f) = 0 := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg, add_zero]
  | single m b =>
    obtain ⟨g, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
    exact decode_embedding_single D Sc cutoff i v t m g

/-- The entire long correction vanishes under the decoder, with full old coefficients. -/
theorem decode_outputPolynomial_precomp (i : I) (v s t : List I)
    (r : hom D Sc cutoff v s) (f : ℕ →₀ hom D Sc cutoff s t) :
    decode D Sc cutoff i v t
      (appendProjection D Sc cutoff i v (t ++ [i])
        (rightContext D Sc cutoff [i] _ _ r ≫ appendOutputPolynomial D Sc cutoff i s t f)) = 0 := by
  rw [appendOutputPolynomial_precomp, ← appendOutputEmbedding_map, decode_embedding]


/-- Recover a canonical crossing only after applying the full triangular law.
The identity-row correction is present and is annihilated by the preceding theorem. -/
theorem decode_canonical_crossing (i : I) (v s t : List I)
    (x : AppendIdx i v (t ++ [i])) (e : x.oldTarget = s ++ [i])
    (L : List PG)
    (hw : cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) =
      PG.cross s.length :: L)
    (hf : Fits (s ++ [i]).length L)
    (h : SChain (s ++ [i]) (pl (s ++ [i]) L) t)
    (r : hom D Sc cutoff v x.oldTarget) :
    decode D Sc cutoff i v t
      (appendCrossingClass D Sc cutoff i v s t (e ▸ r)
        (appendMovingPower D Sc cutoff i s x.1.1 ≫
          affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h))) =
      shortTensor D Sc cutoff i v s t
        (appendMovingPower D Sc cutoff i s x.1.1 ≫
          affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h))
        ((ideal D Sc cutoff v (s ++ [i])).mkQ (e ▸ r)) := by
  have he := appendTailPair_transport D Sc cutoff e r _ _
    (appendTail_cross_heq D Sc i v s t x e L hw hf h)
  have hc := decode_pair D Sc cutoff i v t x r
  rw [he, hw, data_transport D Sc cutoff i e, data_cross D Sc cutoff i v s t L x.1.1 h] at hc
  simp only [appendPair_mk, twist_zero, affineUnit_comp,
    ← rightContext_affineUnit] at hc
  have hp : appendMovingPower D Sc cutoff i (s ++ [i]) x.1.1 =
      affineUnit D Sc cutoff _ _ ((dotE D Sc (s ++ [i] ++ [i]) (s.length + 1)) ^ x.1.1) := by
    simp only [appendMovingPower, List.length_append, List.length_singleton]
  rw [← hp, appendProjection_crossing_power_triangular, map_add, map_smul,
    decode_outputPolynomial_precomp, add_zero] at hc
  have hu : IsUnit (SKM.zsign k (D.parity i * D.parity i) ^ x.1.1) := by
    apply IsUnit.pow
    unfold SKM.zsign
    split <;> simp
  exact hu.smul_left_cancel.mp hc

/-- Recover every smaller append tail, including zero Hom corners. -/
theorem decode_crossing_tail (i : I) (v s t : List I)
    (z : AppendIdx i s t) (r : hom D Sc cutoff v (z.oldTarget ++ [i])) :
    decode D Sc cutoff i v t
      (appendCrossingClass D Sc cutoff i v z.oldTarget t r
        (affineUnit D Sc cutoff _ _ (appendTail D Sc z))) =
      shortTensor D Sc cutoff i v z.oldTarget t
        (affineUnit D Sc cutoff _ _ (appendTail D Sc z))
        ((ideal D Sc cutoff v (z.oldTarget ++ [i])).mkQ r) := by
  by_cases hr : r = 0
  · simp [hr, appendCrossingClass, shortTensor, BalancedInduction.tensor]
  obtain ⟨y⟩ := exists_oldIndex_of_ne_zero D Sc cutoff r hr
  have hv : s.length + 1 = v.length := by
    have hh := congrArg List.length y.tgt_cw
    simpa only [length_tgt, List.length_append, List.length_singleton,
      AppendIdx.oldTarget] using hh.symm
  obtain ⟨d, hd⟩ := appendCrossingShuffle_exists i v s t z hv
  have hzlen : z.oldTarget.length = s.length := by simp only [AppendIdx.oldTarget, length_tgt]
  let L := cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹)
  have hc := appendTail_cross_chain z
  have hf := appendTail_cross_fits z
  have htarget : tgt (z.oldTarget ++ [i] ++ [i])
      (cw (Categorification.TypeA.canWord (v ++ [i]).length d.1⁻¹)) = t ++ [i] := by
    rw [hd, show PG.cross s.length = PG.cross z.oldTarget.length from congrArg PG.cross hzlen.symm,
      tgt_cons]
    have hcross : tgt (z.oldTarget ++ [i] ++ [i]) [PG.cross z.oldTarget.length] =
        z.oldTarget ++ [i] ++ [i] := tgt_eq (by simpa using sChain_crossAt z.oldTarget [] i i)
    simp only [tgt_cons, tgt_nil] at hcross
    rw [hcross]
    exact (tgt_append_right [i] hf).trans (congrArg (· ++ [i]) (tgt_eq hc))
  let x := appendIndexWithTail i y d z.1.1 htarget
  have he : x.oldTarget = z.oldTarget ++ [i] := appendIndexWithTail_target i y d z.1.1 htarget
  let r' : hom D Sc cutoff v x.oldTarget := he.symm ▸ r
  have hr' : he ▸ r' = r := by
    exact (show ∀ {a b : List I} (e : a = b) (q : hom D Sc cutoff v b),
      e ▸ (e.symm ▸ q : hom D Sc cutoff v a) = q from
        by intro a b e q; cases e; rfl) he r
  have hword : cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) =
      PG.cross z.oldTarget.length :: L := by simpa only [x, appendIndexWithTail, hzlen] using hd
  have hh := decode_canonical_crossing D Sc cutoff i v z.oldTarget t
    x he L hword hf hc r'
  rw [hr'] at hh
  rw [appendTail_power_cross]
  exact hh


/-- Full affine balance in the independently defined short source. -/
theorem tensor_balance (i : I) (v s s' t : List I)
    (r : hom D Sc cutoff s s') (c : hom D Sc cutoff (s' ++ [i]) t)
    (b : Old D Sc cutoff v (s ++ [i])) :
    shortTensor D Sc cutoff i v s t (rightContext D Sc cutoff [i] _ _ r ≫ c) b =
      shortTensor D Sc cutoff i v s' t c
        ((coefficient D Sc cutoff (D.parity i) i v).map
          ((ideal D Sc cutoff s s').mkQ r) b) :=
  BalancedInduction.balance (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i) i v)
    (v := ⟨s⟩) (v' := ⟨s'⟩) r c b

/-- The prescribed column on an arbitrary lifted old quotient coefficient. -/
theorem column_mk (i : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (r : hom D Sc cutoff v (s ++ [i])) :
    shortCross D Sc cutoff i v t
      (shortTensor D Sc cutoff i v s t c ((ideal D Sc cutoff _ _).mkQ r)) =
      appendCrossingClass D Sc cutoff i v s t r c := by
  rw [shortCross_tensor, shortCrossPair_mk]
  rfl

/-- Recovery on a smaller tail for every old quotient coefficient. -/
theorem decode_short_tail (i : I) (v s t : List I) (z : AppendIdx i s t)
    (b : Old D Sc cutoff v (z.oldTarget ++ [i])) :
    decode D Sc cutoff i v t (shortCross D Sc cutoff i v t
      (shortTensor D Sc cutoff i v z.oldTarget t
        (affineUnit D Sc cutoff _ _ (appendTail D Sc z)) b)) =
      shortTensor D Sc cutoff i v z.oldTarget t
        (affineUnit D Sc cutoff _ _ (appendTail D Sc z)) b := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v (z.oldTarget ++ [i])).mkQ_surjective b
  rw [column_mk]
  exact decode_crossing_tail D Sc cutoff i v s t z r

/-- Every full-coefficient balanced generator is recovered. -/
theorem decode_tensor (i : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    decode D Sc cutoff i v t (shortCross D Sc cutoff i v t
      (shortTensor D Sc cutoff i v s t c b)) = shortTensor D Sc cutoff i v s t c b := by
  obtain ⟨f, rfl⟩ := (appendAffineEquiv D Sc cutoff i s t).symm.surjective c
  induction f using Finsupp.induction_linear with
  | zero => simp [shortTensor, BalancedInduction.tensor]
  | add f g hf hg =>
    have hadd (c c' : hom D Sc cutoff (s ++ [i]) t) :
        shortTensor D Sc cutoff i v s t (c + c') b =
          shortTensor D Sc cutoff i v s t c b + shortTensor D Sc cutoff i v s t c' b := by
      simp only [shortTensor, BalancedInduction.tensor, TensorProduct.add_tmul, map_add]
    simp only [map_add, hadd, hf, hg]
  | single z a =>
    rw [appendAffineEquiv_symm_single]
    have hfactor : (a ⊗ₜ[k] appendElt D Sc z : hom D Sc cutoff (s ++ [i]) t) =
        rightContext D Sc cutoff [i] _ _
          (coefficientTwist D cutoff (appendTailParity D z) a ⊗ₜ[k] z.old.nf) ≫
            affineUnit D Sc cutoff _ _ (appendTail D Sc z) := by
      have he : affineUnit D Sc cutoff _ _ (appendTail D Sc z) =
          ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc z :
            hom D Sc cutoff (z.oldTarget ++ [i]) t) := rfl
      rw [he]
      exact (append_insert_twisted_coefficient D Sc cutoff z a).symm
    rw [hfactor, tensor_balance]
    exact decode_short_tail D Sc cutoff i v s t z _

/-- Left inverse on all balanced classes, not only their chosen representatives. -/
theorem decode_comp_shortCross (i : I) (v t : List I) :
    decode D Sc cutoff i v t ∘ₗ shortCross D Sc cutoff i v t = LinearMap.id := by
  apply BalancedInduction.hom_ext
  intro s c b
  exact decode_tensor D Sc cutoff i v s.word t c b

@[simp] theorem decode_shortCross (i : I) (v t : List I)
    (z : ShortTarget D Sc cutoff i v t) :
    decode D Sc cutoff i v t (shortCross D Sc cutoff i v t z) = z :=
  LinearMap.congr_fun (decode_comp_shortCross D Sc cutoff i v t) z

theorem shortCross_injective (i : I) (v t : List I) :
    Function.Injective (shortCross D Sc cutoff i v t) :=
  Function.LeftInverse.injective (decode_shortCross D Sc cutoff i v t)


/-- The range is the original crossing span with arbitrary full old arrows on both sides. -/
theorem range_shortCross (i : I) (v t : List I) :
    LinearMap.range (shortCross D Sc cutoff i v t) = appendCrossingSpan D Sc cutoff i v t := by
  apply le_antisymm
  · have hc : appendC0 D Sc cutoff i v t ∘ₗ shortCross D Sc cutoff i v t = 0 := by
      apply BalancedInduction.hom_ext
      intro s c b
      obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v (s.word ++ [i])).mkQ_surjective b
      change appendC0 D Sc cutoff i v t
        (shortCross D Sc cutoff i v t (shortTensor D Sc cutoff i v s.word t c
          ((ideal D Sc cutoff _ _).mkQ r))) = 0
      rw [column_mk, appendC0_crossing]
    rintro z ⟨a, rfl⟩
    rw [← appendC0_ker]
    exact LinearMap.congr_fun hc a
  · apply Submodule.span_le.mpr
    rintro z ⟨s, r, c, rfl⟩
    exact ⟨shortTensor D Sc cutoff i v s t c ((ideal D Sc cutoff _ _).mkQ r),
      column_mk D Sc cutoff i v s t c r⟩

/-- The independently balanced short source identifies with the genuine crossing span. -/
def crossingEquiv (i : I) (v t : List I) :
    ShortTarget D Sc cutoff i v t ≃ₗ[k] appendCrossingSpan D Sc cutoff i v t where
  toFun z := ⟨shortCross D Sc cutoff i v t z, by
    rw [← range_shortCross]; exact ⟨z, rfl⟩⟩
  invFun z := decode D Sc cutoff i v t z.1
  left_inv := decode_shortCross D Sc cutoff i v t
  right_inv z := by
    apply Subtype.ext
    have hz : z.1 ∈ LinearMap.range (shortCross D Sc cutoff i v t) := by
      rw [range_shortCross]; exact z.2
    obtain ⟨a, ha⟩ := hz
    change shortCross D Sc cutoff i v t (decode D Sc cutoff i v t z.1) = z.1
    rw [← ha, decode_shortCross]
  map_add' a b := Subtype.ext (map_add _ a b)
  map_smul' a b := Subtype.ext (map_smul _ a b)

end ShortCrossCoordinates
end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor
