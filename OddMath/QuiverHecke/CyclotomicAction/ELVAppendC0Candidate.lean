/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendOutputDot
import OddMath.QuiverHecke.CyclotomicAction.ELVOldCategory

/-!
# Corrected polynomial projection and splitting of the full ELV append target

The explicit coordinate candidate uses the all-power crossing correction on
each nonidentity input tail. After recovery on the actual output embedding and
annihilation of the entire crossing image are proved, it is exported as
`appendC0`. Its kernel is exactly the crossing span. The resulting splitting
has augmented inverse `z ↦ (z - j(C0 z), C0 z)` and reconstruction `(c,f) ↦ c+j(f)`.

The output-dot commutator is globally concentrated in polynomial degree zero.
On a crossing it is minus the self-crossing sign times the twisted old
composition; in the odd case this is a positive constant. No polynomial
linearity, old-quotient flatness, or finite-colour assumption is used.
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
The crossing and recovery laws are proved below before exporting `appendC0`. -/
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

/-- All actual old append tails are annihilated after the final crossing. -/
theorem appendC0Candidate_crossing_tail (i : I) (v s t : List I)
    (z : AppendIdx i s t) (r : hom D Sc cutoff v (z.oldTarget ++ [i])) :
    appendC0Candidate D Sc cutoff i v t
      (appendCrossingClass D Sc cutoff i v z.oldTarget t r
        (affineUnit D Sc cutoff _ _ (appendTail D Sc z))) = 0 := by
  by_cases hr : r = 0
  · simp [hr, appendCrossingClass]
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
  have hh := appendC0Candidate_canonical_crossing D Sc cutoff i v z.oldTarget t
    x he L hword hf hc r'
  rw [hr'] at hh
  rw [appendTail_power_cross]
  exact hh

private theorem appendCrossingClass_prefix (i : I) (v s u t : List I)
    (r : hom D Sc cutoff v (s ++ [i])) (b : hom D Sc cutoff s u)
    (g : hom D Sc cutoff (u ++ [i]) t) :
    appendCrossingClass D Sc cutoff i v s t r (rightContext D Sc cutoff [i] _ _ b ≫ g) =
      appendCrossingClass D Sc cutoff i v u t
        (r ≫ rightContext D Sc cutoff [i] _ _ (twist k (D.parity i * D.parity i) b)) g := by
  simp only [appendCrossingClass, rightContext_comp, Category.assoc]
  rw [← Category.assoc (affineUnit D Sc cutoff _ _ (crossLast D Sc s i i)),
    crossLast_comp_rightContext, Category.assoc]

/-- The actual corrected functional annihilates the entire crossing image,
with arbitrary full old arrows on both sides. -/
theorem appendC0Candidate_crossing (i : I) (v s t : List I)
    (r : hom D Sc cutoff v (s ++ [i])) (g : hom D Sc cutoff (s ++ [i]) t) :
    appendC0Candidate D Sc cutoff i v t (appendCrossingClass D Sc cutoff i v s t r g) = 0 := by
  suffices hh : ∀ f : AppendIdx i s t →₀ SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff,
      appendC0Candidate D Sc cutoff i v t
        (appendCrossingClass D Sc cutoff i v s t r ((appendAffineEquiv D Sc cutoff i s t).symm f)) = 0 by
    simpa only [LinearEquiv.symm_apply_apply] using hh ((appendAffineEquiv D Sc cutoff i s t) g)
  intro f
  induction f using Finsupp.induction_linear with
  | zero => simp [appendCrossingClass]
  | add f g hf hg =>
    simpa only [map_add, appendCrossingClass, rightContext_comp, Preadditive.comp_add,
      map_add, add_zero] using congrArg₂ (· + ·) hf hg
  | single z a =>
    rw [appendAffineEquiv_symm_single]
    have hfactor : (a ⊗ₜ[k] appendElt D Sc z : hom D Sc cutoff (s ++ [i]) t) =
        rightContext D Sc cutoff [i] _ _ (coefficientTwist D cutoff (appendTailParity D z) a ⊗ₜ[k] z.old.nf) ≫
          affineUnit D Sc cutoff _ _ (appendTail D Sc z) := by
      have he : affineUnit D Sc cutoff _ _ (appendTail D Sc z) =
          ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc z :
            hom D Sc cutoff (z.oldTarget ++ [i]) t) := rfl
      rw [he]
      exact (append_insert_twisted_coefficient D Sc cutoff z a).symm
    rw [hfactor, appendCrossingClass_prefix]
    exact appendC0Candidate_crossing_tail D Sc cutoff i v s t z _

/-- The corrected polynomial projection, with recovery and entire-crossing
annihilation now proved for its explicit coordinate construction. -/
def appendC0 (i : I) (v t : List I) :
    AppendTarget D Sc cutoff i v (t ++ [i]) →ₗ[k] (ℕ →₀ Old D Sc cutoff v t) :=
  appendC0Candidate D Sc cutoff i v t

@[simp] theorem appendC0_embedding (i : I) (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    appendC0 D Sc cutoff i v t (appendOutputEmbedding D Sc cutoff i v t f) = f :=
  appendC0Candidate_embedding D Sc cutoff i v t f

@[simp] theorem appendC0_crossing (i : I) (v s t : List I)
    (r : hom D Sc cutoff v (s ++ [i])) (g : hom D Sc cutoff (s ++ [i]) t) :
    appendC0 D Sc cutoff i v t (appendCrossingClass D Sc cutoff i v s t r g) = 0 :=
  appendC0Candidate_crossing D Sc cutoff i v s t r g

/-- The genuine full crossing span, with arbitrary old arrows on both sides. -/
def appendCrossingSpan (i : I) (v t : List I) :
    Submodule k (AppendTarget D Sc cutoff i v (t ++ [i])) :=
  Submodule.span k {z | ∃ (s : List I) (r : hom D Sc cutoff v (s ++ [i]))
    (g : hom D Sc cutoff (s ++ [i]) t), z = appendCrossingClass D Sc cutoff i v s t r g}

theorem appendCrossingSpan_le_ker (i : I) (v t : List I) :
    appendCrossingSpan D Sc cutoff i v t ≤ LinearMap.ker (appendC0 D Sc cutoff i v t) := by
  apply Submodule.span_le.mpr
  rintro z ⟨s, r, g, rfl⟩
  exact appendC0_crossing D Sc cutoff i v s t r g

/-- The global constant defect on every genuine crossing, not merely a local
identity or an assumed polynomial-linear projection. -/
theorem appendC0_outputDot_crossing (i : I) (v s t : List I)
    (r : hom D Sc cutoff v (s ++ [i])) (g : hom D Sc cutoff (s ++ [i]) t) :
    appendC0 D Sc cutoff i v t
      (appendOutputDot D Sc cutoff i v t (appendCrossingClass D Sc cutoff i v s t r g)) =
    -SKM.zsign k (D.parity i * D.parity i) •
      Finsupp.single 0 ((ideal D Sc cutoff v t).mkQ (r ≫ twist k (D.parity i) g)) := by
  rw [appendOutputDot_crossingClass, map_sub, map_smul, map_smul,
    appendC0_crossing, appendC0_embedding, smul_zero, zero_sub, neg_smul]

theorem appendC0_outputDot_crossing_odd (i : I) (hi : D.parity i = 1) (v s t : List I)
    (r : hom D Sc cutoff v (s ++ [i])) (g : hom D Sc cutoff (s ++ [i]) t) :
    appendC0 D Sc cutoff i v t
      (appendOutputDot D Sc cutoff i v t (appendCrossingClass D Sc cutoff i v s t r g)) =
      Finsupp.single 0 ((ideal D Sc cutoff v t).mkQ (r ≫ twist k 1 g)) := by
  rw [appendOutputDot_crossingClass_odd D Sc cutoff i hi, map_add, map_neg,
    appendC0_crossing, neg_zero, appendC0_embedding, zero_add]

private theorem appendRunWord_shape (i : I) (u t : List I) (n : ℕ) (hn : u.length = n)
    (j : Fin (n + 1))
    (ht : tgt (u ++ [i]) (cw (Categorification.TypeA.canWord (n + 1) (appendRun n j).1⁻¹)) = t ++ [i]) :
    (cw (Categorification.TypeA.canWord (n + 1) (appendRun n j).1⁻¹) = [] ∧ u = t) ∨
    ∃ (s : List I) (L : List PG), u = s ++ [i] ∧
      cw (Categorification.TypeA.canWord (n + 1) (appendRun n j).1⁻¹) = PG.cross s.length :: L ∧
      Fits (s ++ [i]).length L ∧ SChain (s ++ [i]) (pl (s ++ [i]) L) t := by
  cases n with
  | zero =>
    have hj : j = Fin.last 0 := by apply Fin.ext; have := j.2; simp only [Fin.val_last]; omega
    have hw : cw (Categorification.TypeA.canWord 1 (appendRun 0 j).1⁻¹) = [] := by
      rw [hj, canWord_appendRun]
      simp [cw]
    rw [hw, tgt_nil] at ht
    exact Or.inl ⟨hw, List.append_cancel_right ht⟩
  | succ n =>
    revert ht
    refine Fin.lastCases ?_ (fun j => ?_) j
    · intro ht
      have hw : cw (Categorification.TypeA.canWord (n + 1 + 1)
          (appendRun (n + 1) (Fin.last (n + 1))).1⁻¹) = [] := by
        rw [canWord_appendRun]
        simp [cw]
      rw [hw, tgt_nil] at ht
      exact Or.inl ⟨hw, List.append_cancel_right ht⟩
    · intro ht
      have hu : u ≠ [] := by intro h; simp [h] at hn
      obtain ⟨s, c, rfl⟩ := (List.eq_nil_or_concat' u).resolve_left hu
      have hs : s.length = n := by simpa only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] using hn
      let L := cw (Categorification.TypeA.canWord (n + 1) (appendRun n j).1⁻¹)
      have hw : cw (Categorification.TypeA.canWord (n + 2) (appendRun (n + 1) j.castSucc).1⁻¹) =
          PG.cross s.length :: L := by simpa only [hs] using appendRunWord_castSucc n j
      have hf : Fits (s ++ [i]).length L := by
        simpa only [List.length_append, List.length_singleton, hs] using
          fits_cw (Categorification.TypeA.validWord_canWord (n + 1) (appendRun n j).1⁻¹)
      rw [hw, tgt_cons] at ht
      have hcross : (PG.cross s.length).act (s ++ [c] ++ [i]) = s ++ [i] ++ [c] := by
        have hc : tgt (s ++ [c] ++ [i]) [PG.cross s.length] = s ++ [i] ++ [c] :=
          tgt_eq (by simpa using sChain_crossAt s [] c i)
        simpa only [tgt_cons, tgt_nil] using hc
      rw [hcross, tgt_append_right [c] hf] at ht
      have hci : c = i := by
        have he := congrArg List.getLast? ht
        simpa using he
      subst c
      have ht' := List.append_cancel_right ht
      exact Or.inr ⟨s, L, rfl, hw, hf, by rw [← ht']; exact sChain_pl _ _⟩

private theorem appendTail_shape (i : I) (v t : List I) (x : AppendIdx i v (t ++ [i])) :
    (cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) = [] ∧ x.oldTarget = t) ∨
    ∃ (s : List I) (L : List PG), x.oldTarget = s ++ [i] ∧
      cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) = PG.cross s.length :: L ∧
      Fits (s ++ [i]).length L ∧ SChain (s ++ [i]) (pl (s ++ [i]) L) t := by
  let d0 := AppendShuffle.cast (appendLen v i) rfl x.1.2.2.2
  let j := (appendRunEquiv v.length).symm d0
  have hj : appendRun v.length j = d0 := (appendRunEquiv v.length).apply_symm_apply d0
  have hw : cw (Categorification.TypeA.canWord (v.length + 1) (appendRun v.length j).1⁻¹) =
      cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) := by
    rw [hj, AppendShuffle.canWord_cast]
  have hl : x.oldTarget.length = v.length := by simp only [AppendIdx.oldTarget, length_tgt]
  have ht : tgt (x.oldTarget ++ [i])
      (cw (Categorification.TypeA.canWord (v.length + 1) (appendRun v.length j).1⁻¹)) = t ++ [i] := by
    rw [hw]
    exact tgt_eq (appendTail_cross_chain x)
  simpa only [hw] using appendRunWord_shape i x.oldTarget t v.length hl j ht

private theorem appendTail_nil_heq (i : I) (v t : List I)
    (x : AppendIdx i v (t ++ [i])) (e : x.oldTarget = t)
    (hw : cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) = []) :
    HEq (appendTail D Sc x) ((dotE D Sc (t ++ [i]) t.length) ^ x.1.1) := by
  have hl : v.length = t.length := by
    have hh := congrArg List.length e
    simpa only [AppendIdx.oldTarget, length_tgt] using hh
  unfold appendTail
  rw [dotE_pow]
  apply append_cl_heq D Sc (congrArg (· ++ [i]) e) rfl
  simp only [hw, hl, List.map_replicate, List.append_nil]

private theorem appendPair_mem_crossing_sup_output (i : I) (v t : List I)
    (x : AppendIdx i v (t ++ [i])) (r : hom D Sc cutoff v x.oldTarget) :
    appendPair D Sc cutoff 0 i (affineUnit D Sc cutoff _ _ (appendTail D Sc x))
      ((ideal D Sc cutoff v x.oldTarget).mkQ r) ∈
      appendCrossingSpan D Sc cutoff i v t ⊔ LinearMap.range (appendOutputEmbedding D Sc cutoff i v t) := by
  rcases appendTail_shape i v t x with ⟨hw, e⟩ | ⟨s, L, e, hw, hf, h⟩
  · rw [appendTailPair_transport D Sc cutoff e r _ _ (appendTail_nil_heq D Sc i v t x e hw),
      appendPair_mk, twist_zero]
    apply Submodule.mem_sup_right
    refine ⟨Finsupp.single x.1.1 ((ideal D Sc cutoff v t).mkQ (e ▸ r)), ?_⟩
    exact appendOutputEmbedding_single D Sc cutoff i v t x.1.1 (e ▸ r)
  · rw [appendTailPair_transport D Sc cutoff e r _ _
      (appendTail_cross_heq D Sc i v s t x e L hw hf h), appendPair_mk, twist_zero]
    simp only [affineUnit_comp, ← rightContext_affineUnit]
    have hp : appendMovingPower D Sc cutoff i (s ++ [i]) x.1.1 =
        affineUnit D Sc cutoff _ _ ((dotE D Sc (s ++ [i] ++ [i]) (s.length + 1)) ^ x.1.1) := by
      simp only [appendMovingPower, List.length_append, List.length_singleton]
    rw [← hp, appendProjection_crossing_power_triangular]
    apply Submodule.add_mem
    · apply Submodule.smul_mem
      apply Submodule.mem_sup_left
      apply Submodule.subset_span
      exact ⟨s, e ▸ r, appendMovingPower D Sc cutoff i s x.1.1 ≫
        affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h), rfl⟩
    · apply Submodule.mem_sup_right
      rw [appendOutputPolynomial_precomp, ← appendOutputEmbedding_map]
      exact LinearMap.mem_range_self _ _

/-- The polynomial row and actual crossing span exhaust the append target,
including the separate height-zero case in the canonical run analysis. -/
theorem appendCrossingSpan_sup_output (i : I) (v t : List I) :
    appendCrossingSpan D Sc cutoff i v t ⊔ LinearMap.range (appendOutputEmbedding D Sc cutoff i v t) = ⊤ := by
  apply top_unique
  intro z hz
  clear hz
  obtain ⟨f, rfl⟩ := (appendOldCoordinateEquiv D Sc cutoff 0 i v (t ++ [i])).symm.surjective z
  change appendOldReconstruct D Sc cutoff 0 i v (t ++ [i]) f ∈ _
  induction f using DirectSum.induction_on with
  | zero => simp only [map_zero]; exact Submodule.zero_mem _
  | add f g hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg
  | of q b =>
    change appendOldReconstruct D Sc cutoff 0 i v (t ++ [i]) (DirectSum.lof k _ _ q b) ∈ _
    obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v q.representative.oldTarget).mkQ_surjective b
    have he : affineUnit D Sc cutoff _ _ (appendTail D Sc q.representative) =
        ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k] appendTail D Sc q.representative :
          hom D Sc cutoff (q.representative.oldTarget ++ [i]) (t ++ [i])) := rfl
    simpa only [appendOldReconstruct, DirectSum.toModule_lof, he] using
      appendPair_mem_crossing_sup_output D Sc cutoff i v t q.representative r

/-- The kernel is exactly the genuine entire crossing image. -/
theorem appendC0_ker (i : I) (v t : List I) :
    LinearMap.ker (appendC0 D Sc cutoff i v t) = appendCrossingSpan D Sc cutoff i v t := by
  apply le_antisymm _ (appendCrossingSpan_le_ker D Sc cutoff i v t)
  intro z hz
  have hall : z ∈ appendCrossingSpan D Sc cutoff i v t ⊔
      LinearMap.range (appendOutputEmbedding D Sc cutoff i v t) := by
    rw [appendCrossingSpan_sup_output]
    exact Submodule.mem_top
  obtain ⟨c, hc, p, hp, he⟩ := Submodule.mem_sup.mp hall
  obtain ⟨f, rfl⟩ := hp
  have hc0 : appendC0 D Sc cutoff i v t c = 0 := appendCrossingSpan_le_ker D Sc cutoff i v t hc
  have hf := congrArg (appendC0 D Sc cutoff i v t) he
  rw [map_add, hc0, appendC0_embedding, zero_add] at hf
  have hf0 : f = 0 := hf.trans hz
  rw [hf0, map_zero, add_zero] at he
  exact he ▸ hc

theorem appendC0_residual_mem (i : I) (v t : List I)
    (z : AppendTarget D Sc cutoff i v (t ++ [i])) :
    z - appendOutputEmbedding D Sc cutoff i v t (appendC0 D Sc cutoff i v t z) ∈
      appendCrossingSpan D Sc cutoff i v t := by
  rw [← appendC0_ker, LinearMap.mem_ker]
  simp only [map_sub, appendC0_embedding, sub_self]

/-- The prescribed augmented inverse: subtract the actual polynomial output
from the vector to obtain its crossing component. -/
def appendC0Splitting (i : I) (v t : List I) :
    AppendTarget D Sc cutoff i v (t ++ [i]) ≃ₗ[k]
      (appendCrossingSpan D Sc cutoff i v t × (ℕ →₀ Old D Sc cutoff v t)) where
  toFun z := (⟨z - appendOutputEmbedding D Sc cutoff i v t (appendC0 D Sc cutoff i v t z),
    appendC0_residual_mem D Sc cutoff i v t z⟩, appendC0 D Sc cutoff i v t z)
  invFun p := p.1.1 + appendOutputEmbedding D Sc cutoff i v t p.2
  left_inv z := sub_add_cancel z _
  right_inv p := by
    obtain ⟨c, f⟩ := p
    have hc : appendC0 D Sc cutoff i v t c.1 = 0 := appendCrossingSpan_le_ker D Sc cutoff i v t c.2
    apply Prod.ext
    · apply Subtype.ext
      change c.1 + _ - _ = c.1
      simp only [map_add, hc, appendC0_embedding, zero_add, add_sub_cancel_right]
    · change appendC0 D Sc cutoff i v t (c.1 + _) = f
      simp only [map_add, hc, appendC0_embedding, zero_add]
  map_add' a b := by
    apply Prod.ext
    · apply Subtype.ext
      change a + b - _ = (a - _) + (b - _)
      simp only [map_add]
      abel
    · exact map_add _ a b
  map_smul' a b := by
    apply Prod.ext
    · apply Subtype.ext
      change a • b - _ = a • (b - _)
      simp only [map_smul, smul_sub]
    · exact map_smul _ a b

@[simp] theorem appendC0Splitting_symm (i : I) (v t : List I)
    (c : appendCrossingSpan D Sc cutoff i v t) (f : ℕ →₀ Old D Sc cutoff v t) :
    (appendC0Splitting D Sc cutoff i v t).symm (c, f) =
      c.1 + appendOutputEmbedding D Sc cutoff i v t f := rfl

/-- The output-dot commutator of the actual global polynomial projection. -/
def appendC0Defect (i : I) (v t : List I) :
    AppendTarget D Sc cutoff i v (t ++ [i]) →ₗ[k] (ℕ →₀ Old D Sc cutoff v t) :=
  (appendC0 D Sc cutoff i v t).comp (appendOutputDot D Sc cutoff i v t) -
    (appendOutputShift D Sc cutoff v t).comp (appendC0 D Sc cutoff i v t)

@[simp] theorem appendC0Defect_embedding (i : I) (v t : List I)
    (f : ℕ →₀ Old D Sc cutoff v t) :
    appendC0Defect D Sc cutoff i v t (appendOutputEmbedding D Sc cutoff i v t f) = 0 := by
  simp only [appendC0Defect, LinearMap.sub_apply, LinearMap.comp_apply,
    appendOutputDot_embedding, appendC0_embedding, sub_self]

@[simp] theorem appendC0Defect_crossing (i : I) (v s t : List I)
    (r : hom D Sc cutoff v (s ++ [i])) (g : hom D Sc cutoff (s ++ [i]) t) :
    appendC0Defect D Sc cutoff i v t (appendCrossingClass D Sc cutoff i v s t r g) =
      -SKM.zsign k (D.parity i * D.parity i) •
        Finsupp.single 0 ((ideal D Sc cutoff v t).mkQ (r ≫ twist k (D.parity i) g)) := by
  simp only [appendC0Defect, LinearMap.sub_apply, LinearMap.comp_apply,
    appendC0_outputDot_crossing, appendC0_crossing, map_zero, sub_zero]

/-- The global output-dot defect has degree zero on every append-target vector. -/
theorem appendC0Defect_degreeZero (i : I) (v t : List I)
    (z : AppendTarget D Sc cutoff i v (t ++ [i])) :
    appendC0Defect D Sc cutoff i v t z =
      Finsupp.single 0 (appendC0Defect D Sc cutoff i v t z 0) := by
  have hc : ∀ c ∈ appendCrossingSpan D Sc cutoff i v t,
      appendC0Defect D Sc cutoff i v t c =
        Finsupp.single 0 (appendC0Defect D Sc cutoff i v t c 0) := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨s, r, g, rfl⟩ := hc
      simp only [appendC0Defect_crossing, Finsupp.single_eq_same,
        Finsupp.smul_single]
    | zero => simp only [map_zero, Finsupp.zero_apply, Finsupp.single_zero]
    | add a b ha hb ha' hb' =>
      rw [map_add, ha', hb']
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, Finsupp.single_add]
    | smul a b hb hb' =>
      rw [map_smul, hb']
      simp only [Finsupp.single_eq_same, Finsupp.smul_single]
  have hh := hc _ (appendC0_residual_mem D Sc cutoff i v t z)
  simpa only [map_sub, appendC0Defect_embedding, sub_zero] using hh

theorem appendCrossingSpan_disjoint_output (i : I) (v t : List I) :
    Disjoint (appendCrossingSpan D Sc cutoff i v t)
      (LinearMap.range (appendOutputEmbedding D Sc cutoff i v t)) := by
  apply Submodule.disjoint_def.mpr
  intro z hc hp
  obtain ⟨f, rfl⟩ := hp
  have hf : f = 0 := (appendC0_embedding D Sc cutoff i v t f).symm.trans
    (appendCrossingSpan_le_ker D Sc cutoff i v t hc)
  simp only [hf, map_zero]

/-- The global output-dot formula, with its required degree-zero defect. -/
theorem appendC0_outputDot (i : I) (v t : List I)
    (z : AppendTarget D Sc cutoff i v (t ++ [i])) :
    appendC0 D Sc cutoff i v t (appendOutputDot D Sc cutoff i v t z) =
      appendOutputShift D Sc cutoff v t (appendC0 D Sc cutoff i v t z) +
        Finsupp.single 0 (appendC0Defect D Sc cutoff i v t z 0) := by
  have h := appendC0Defect_degreeZero D Sc cutoff i v t z
  change appendC0 D Sc cutoff i v t (appendOutputDot D Sc cutoff i v t z) -
    appendOutputShift D Sc cutoff v t (appendC0 D Sc cutoff i v t z) = _ at h
  exact (sub_eq_iff_eq_add.mp h).trans (add_comm _ _)

end OddMath.QuiverHecke.ELVOld
