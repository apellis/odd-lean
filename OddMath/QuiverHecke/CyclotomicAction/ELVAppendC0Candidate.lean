/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendOutputDot
import OddMath.QuiverHecke.CyclotomicAction.ELVOldCategory

/-!
# Corrected output-coordinate candidate on the full ELV append quotient

The actual linear functional uses the all-power crossing correction on each
nonidentity input tail, rather than discarding those tails. It recovers the
specified output embedding and annihilates the canonical crossing rows below.
Its identification with the quotient by the entire crossing image is not yet
asserted; the name remains `appendC0Candidate` until that compatibility is proved.
-/

noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped Classical DirectSum TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- The polynomial prescribed by a moving exponent and crossing word. -/
def appendTailPolynomialData (i : I) (s t : List I) (L : List PG) (m : ℕ) :
    ℕ →₀ hom D Sc cutoff s t := by
  by_cases hL : L = []
  · by_cases ht : s = t
    · exact Finsupp.single m (eqToHom (congrArg (obj D Sc cutoff) ht))
    · exact 0
  · by_cases hs : s = s.dropLast ++ [i]
    · by_cases ht : SChain (s.dropLast ++ [i]) (pl (s.dropLast ++ [i]) L.tail) t
      · exact Finsupp.mapRange.linearMap
          (Linear.leftComp k _ (eqToHom (congrArg (obj D Sc cutoff) hs)))
          (appendCrossingCorrection D Sc cutoff i s.dropLast t m
            (affineUnit D Sc cutoff _ _ (cl D Sc _ _ L.tail ht)))
      · exact 0
    · exact 0

/-- The polynomial part prescribed by the input moving tail. -/
def appendTailPolynomialCandidate (i : I) (v t : List I)
    (x : AppendIdx i v (t ++ [i])) :
    ℕ →₀ hom D Sc cutoff x.oldTarget t :=
  appendTailPolynomialData D Sc cutoff i x.oldTarget t
    (cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹)) x.1.1

/-- Compose a finite old output row with an arbitrary old quotient input. -/
def appendPolynomialOldPair (v s t : List I)
    (f : ℕ →₀ hom D Sc cutoff s t) :
    Old D Sc cutoff v s →ₗ[k] (ℕ →₀ Old D Sc cutoff v t) :=
  f.sum fun m g => (Finsupp.lsingle m).comp
    ((oldComp D Sc cutoff v s t).flip ((ideal D Sc cutoff s t).mkQ g))

/-- A corrected coordinate candidate on the actual append-old quotient.
The crossing and recovery laws are not asserted by this definition. -/
def appendC0Candidate (i : I) (v t : List I) :
    AppendTarget D Sc cutoff i v (t ++ [i]) →ₗ[k] (ℕ →₀ Old D Sc cutoff v t) :=
  (DirectSum.toModule k _ _ fun q : AppendIdx.Tail i v (t ++ [i]) =>
    appendPolynomialOldPair D Sc cutoff v q.representative.oldTarget t
      (appendTailPolynomialCandidate D Sc cutoff i v t q.representative)).comp
    (appendOldCoordinateEquiv D Sc cutoff 0 i v (t ++ [i])).toLinearMap

@[simp] theorem appendC0Candidate_reconstruct_lof (i : I) (v t : List I)
    (q : AppendIdx.Tail i v (t ++ [i]))
    (b : Old D Sc cutoff v q.representative.oldTarget) :
    appendC0Candidate D Sc cutoff i v t
      (appendOldReconstruct D Sc cutoff 0 i v (t ++ [i]) (DirectSum.lof k _ _ q b)) =
    appendPolynomialOldPair D Sc cutoff v q.representative.oldTarget t
      (appendTailPolynomialCandidate D Sc cutoff i v t q.representative) b := by
  simp only [appendC0Candidate, LinearMap.comp_apply, LinearEquiv.coe_coe,
    appendOldCoordinateEquiv_reconstruct, DirectSum.toModule_lof]

@[simp] theorem appendPolynomialOldPair_single (v s t : List I) (m : ℕ)
    (g : hom D Sc cutoff s t) (b : Old D Sc cutoff v s) :
    appendPolynomialOldPair D Sc cutoff v s t (Finsupp.single m g) b =
      Finsupp.single m (oldComp D Sc cutoff v s t b ((ideal D Sc cutoff s t).mkQ g)) := by
  simp [appendPolynomialOldPair]

@[simp] theorem appendTailPolynomialData_nil (i : I) (t : List I) (m : ℕ) :
    appendTailPolynomialData D Sc cutoff i t t [] m = Finsupp.single m (𝟙 _) := by
  simp [appendTailPolynomialData]

private theorem appendCorrection_transport (i : I) (s s' t : List I)
    (e : s' = s) (L : List PG) (m : ℕ)
    (h : SChain (s ++ [i]) (pl (s ++ [i]) L) t)
    (h' : SChain (s' ++ [i]) (pl (s' ++ [i]) L) t) :
    Finsupp.mapRange.linearMap
      (Linear.leftComp k _ (eqToHom (congrArg (fun a => obj D Sc cutoff (a ++ [i])) e.symm)))
      (appendCrossingCorrection D Sc cutoff i s' t m
        (affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h'))) =
    appendCrossingCorrection D Sc cutoff i s t m
      (affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h)) := by
  subst s'
  ext d
  simp [Finsupp.mapRange.linearMap_apply, Linear.leftComp_apply]

/-- The candidate uses the nonzero triangular correction on a crossing row. -/
theorem appendTailPolynomialData_cross (i : I) (s t : List I) (L : List PG) (m : ℕ)
    (h : SChain (s ++ [i]) (pl (s ++ [i]) L) t) :
    appendTailPolynomialData D Sc cutoff i (s ++ [i]) t (PG.cross s.length :: L) m =
      appendCrossingCorrection D Sc cutoff i s t m
        (affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h)) := by
  dsimp only [appendTailPolynomialData]
  rw [dite_eq_right (List.cons_ne_nil _ _)]
  have he : (s ++ [i]).dropLast = s := List.dropLast_concat
  rw [dite_eq_left (congrArg (· ++ [i]) he).symm]
  have ht : SChain ((s ++ [i]).dropLast ++ [i])
      (pl ((s ++ [i]).dropLast ++ [i]) (PG.cross s.length :: L).tail) t := by
    simpa only [he, List.tail_cons] using h
  rw [dite_eq_left ht]
  exact appendCorrection_transport D Sc cutoff i s _ t he L m h ht

theorem appendC0Candidate_pair_representative (i : I) (v t : List I)
    (q : AppendIdx.Tail i v (t ++ [i]))
    (b : Old D Sc cutoff v q.representative.oldTarget) :
    appendC0Candidate D Sc cutoff i v t
      (appendPair D Sc cutoff 0 i (affineUnit D Sc cutoff _ _
        (appendTail D Sc q.representative)) b) =
    appendPolynomialOldPair D Sc cutoff v q.representative.oldTarget t
      (appendTailPolynomialCandidate D Sc cutoff i v t q.representative) b := by
  have he : affineUnit D Sc cutoff _ _ (appendTail D Sc q.representative) =
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
        appendTail D Sc q.representative : hom D Sc cutoff
          (q.representative.oldTarget ++ [i]) (t ++ [i])) := rfl
  rw [he]
  simpa only [appendOldReconstruct, DirectSum.toModule_lof] using
    appendC0Candidate_reconstruct_lof D Sc cutoff i v t q b

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

private theorem appendDataPair_transport (i : I) {v s s' t : List I}
    (e : s = s') (L : List PG) (m : ℕ) (r : hom D Sc cutoff v s) :
    appendPolynomialOldPair D Sc cutoff v s t
      (appendTailPolynomialData D Sc cutoff i s t L m) ((ideal D Sc cutoff v s).mkQ r) =
    appendPolynomialOldPair D Sc cutoff v s' t
      (appendTailPolynomialData D Sc cutoff i s' t L m)
        ((ideal D Sc cutoff v s').mkQ (e ▸ r)) := by
  subst s'
  rfl

/-- Readback of the corrected candidate on every existing input PBW tail. -/
theorem appendC0Candidate_pair (i : I) (v t : List I)
    (x : AppendIdx i v (t ++ [i])) (r : hom D Sc cutoff v x.oldTarget) :
    appendC0Candidate D Sc cutoff i v t
      (appendPair D Sc cutoff 0 i (affineUnit D Sc cutoff _ _ (appendTail D Sc x))
        ((ideal D Sc cutoff v x.oldTarget).mkQ r)) =
    appendPolynomialOldPair D Sc cutoff v x.oldTarget t
      (appendTailPolynomialCandidate D Sc cutoff i v t x)
        ((ideal D Sc cutoff v x.oldTarget).mkQ r) := by
  let q : AppendIdx.Tail i v (t ++ [i]) := ⟨x.tailKey, x, rfl⟩
  have hk : x.tailKey = q.representative.tailKey := q.representative_tailKey.symm
  have ht := x.oldTarget_eq_of_tailKey_eq q.representative hk
  rw [appendTailPair_transport D Sc cutoff ht r _ _
    (appendTail_heq_of_tailKey_eq D Sc x q.representative hk)]
  rw [appendC0Candidate_pair_representative]
  have hm := congrArg Prod.fst hk
  have hd := congrArg Prod.snd hk
  change x.1.1 = q.representative.1.1 at hm
  change x.1.2.2.2 = q.representative.1.2.2.2 at hd
  unfold appendTailPolynomialCandidate
  rw [← hm, ← hd]
  exact (appendDataPair_transport D Sc cutoff i ht _ _ r).symm

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

private theorem appendDataPair_nil (i : I) {v s t : List I}
    (e : s = t) (m : ℕ) (r : hom D Sc cutoff v s) :
    appendPolynomialOldPair D Sc cutoff v s t
      (appendTailPolynomialData D Sc cutoff i s t [] m)
      ((ideal D Sc cutoff v s).mkQ r) =
    Finsupp.single m ((ideal D Sc cutoff v t).mkQ (e ▸ r)) := by
  subst t
  rw [appendTailPolynomialData_nil, appendPolynomialOldPair_single, oldComp_mk,
    Category.comp_id]

/-- Recovery on the specified output embedding, not on a newly chosen section. -/
theorem appendC0Candidate_embedding_single (i : I) (v t : List I) (m : ℕ)
    (g : hom D Sc cutoff v t) :
    appendC0Candidate D Sc cutoff i v t
      (appendOutputEmbedding D Sc cutoff i v t
        (Finsupp.single m ((ideal D Sc cutoff v t).mkQ g))) =
    Finsupp.single m ((ideal D Sc cutoff v t).mkQ g) := by
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
  have hc := appendC0Candidate_pair D Sc cutoff i v t x r
  rw [he] at hc
  have hw : cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) = [] := by
    simp only [x, appendIdentityIndex, appendIdentityShuffle_word, cw,
      List.reverse_nil, List.map_nil]
  unfold appendTailPolynomialCandidate at hc
  rw [hw, appendDataPair_nil D Sc cutoff i ht, hr] at hc
  simpa only [appendOutputEmbedding_single, appendPair_mk, twist_zero,
    appendMovingPower, x, appendIdentityIndex] using hc

theorem appendC0Candidate_embedding (i : I) (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    appendC0Candidate D Sc cutoff i v t (appendOutputEmbedding D Sc cutoff i v t f) = f := by
  induction f using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add f g hf hg => simp only [map_add, hf, hg]
  | single m b =>
    obtain ⟨g, rfl⟩ := (ideal D Sc cutoff v t).mkQ_surjective b
    exact appendC0Candidate_embedding_single D Sc cutoff i v t m g

private theorem appendPolynomialOldPair_mk (v s t : List I)
    (f : ℕ →₀ hom D Sc cutoff s t) (r : hom D Sc cutoff v s) :
    appendPolynomialOldPair D Sc cutoff v s t f ((ideal D Sc cutoff v s).mkQ r) =
    Finsupp.mapRange.linearMap (ideal D Sc cutoff v t).mkQ
      (Finsupp.lsum k (fun d => (Finsupp.lsingle d).comp (Linear.leftComp k _ r)) f) := by
  induction f using Finsupp.induction_linear with
  | zero => simp [appendPolynomialOldPair]
  | add f g hf hg =>
    have hadd : appendPolynomialOldPair D Sc cutoff v s t (f + g) =
        appendPolynomialOldPair D Sc cutoff v s t f + appendPolynomialOldPair D Sc cutoff v s t g := by
      unfold appendPolynomialOldPair
      apply Finsupp.sum_add_index
      · intro m; simp
      · intro m a b; simp [map_add, LinearMap.comp_add]
    rw [hadd, LinearMap.add_apply, hf, hg, map_add, map_add]
  | single m g =>
    simp only [appendPolynomialOldPair_single, oldComp_mk, Finsupp.lsum_single,
      LinearMap.comp_apply, Linear.leftComp_apply, Finsupp.lsingle_apply,
      Finsupp.mapRange.linearMap_apply, Finsupp.mapRange_single]

private theorem appendC0Candidate_outputPolynomial_precomp (i : I) (v s t : List I)
    (r : hom D Sc cutoff v s) (f : ℕ →₀ hom D Sc cutoff s t) :
    appendC0Candidate D Sc cutoff i v t
      (appendProjection D Sc cutoff i v (t ++ [i])
        (rightContext D Sc cutoff [i] _ _ r ≫ appendOutputPolynomial D Sc cutoff i s t f)) =
    appendPolynomialOldPair D Sc cutoff v s t f ((ideal D Sc cutoff v s).mkQ r) := by
  rw [appendOutputPolynomial_precomp, ← appendOutputEmbedding_map,
    appendC0Candidate_embedding, appendPolynomialOldPair_mk]

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

/-- The corrected functional annihilates every canonical crossing row, with
an arbitrary full old input coefficient and every moving power. -/
theorem appendC0Candidate_canonical_crossing (i : I) (v s t : List I)
    (x : AppendIdx i v (t ++ [i])) (e : x.oldTarget = s ++ [i])
    (L : List PG)
    (hw : cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) =
      PG.cross s.length :: L)
    (hf : Fits (s ++ [i]).length L)
    (h : SChain (s ++ [i]) (pl (s ++ [i]) L) t)
    (r : hom D Sc cutoff v x.oldTarget) :
    appendC0Candidate D Sc cutoff i v t
      (appendCrossingClass D Sc cutoff i v s t (e ▸ r)
        (appendMovingPower D Sc cutoff i s x.1.1 ≫
          affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h))) = 0 := by
  have he := appendTailPair_transport D Sc cutoff e r _ _
    (appendTail_cross_heq D Sc i v s t x e L hw hf h)
  have hc := appendC0Candidate_pair D Sc cutoff i v t x r
  rw [he] at hc
  unfold appendTailPolynomialCandidate at hc
  rw [hw, appendDataPair_transport D Sc cutoff i e] at hc
  rw [appendTailPolynomialData_cross D Sc cutoff i s t L x.1.1 h] at hc
  simp only [appendPair_mk, twist_zero, affineUnit_comp,
    ← rightContext_affineUnit] at hc
  have hp : appendMovingPower D Sc cutoff i (s ++ [i]) x.1.1 =
      affineUnit D Sc cutoff _ _ ((dotE D Sc (s ++ [i] ++ [i]) (s.length + 1)) ^ x.1.1) := by
    simp only [appendMovingPower, List.length_append, List.length_singleton]
  rw [← hp] at hc
  rw [appendProjection_crossing_power_triangular, map_add, map_smul,
    appendC0Candidate_outputPolynomial_precomp] at hc
  have hz := add_right_cancel (hc.trans (zero_add _).symm)
  change SKM.zsign k (D.parity i * D.parity i) ^ x.1.1 • _ = 0 at hz
  have hu : IsUnit (SKM.zsign k (D.parity i * D.parity i) ^ x.1.1) := by
    apply IsUnit.pow
    unfold SKM.zsign
    split <;> simp
  exact (hu.smul_eq_zero).mp hz

/-- The actual polynomial output embedding is injective over the full ELV old quotient. -/
theorem appendOutputEmbedding_injective (i : I) (v t : List I) :
    Function.Injective (appendOutputEmbedding D Sc cutoff i v t) :=
  Function.LeftInverse.injective (appendC0Candidate_embedding D Sc cutoff i v t)

end OddMath.QuiverHecke.ELVOld
