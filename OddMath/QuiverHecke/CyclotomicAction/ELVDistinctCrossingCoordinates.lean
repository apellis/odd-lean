/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVDistinctAppendTails
import OddMath.QuiverHecke.CyclotomicAction.ELVDistinctCrossingPowers

/-! # Distinct-colour balanced PBW crossing decoder

The crossing-coset inverse required in Brundan–Ellis (1.12) and
`DeformedActionAssembly.md` §3, before imposing the output-old ideal.
The full cyclotomic quotient and prescribed mate comparison are separate.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped Classical DirectSum TensorProduct
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

/-- Insert a shorter crossing word with its unchanged old quotient coefficient. -/
def wordLift (i j : I) (v q s t : List I) (hs : q = s ++ [j])
    (L : List PG) (m : ℕ) (ht : SChain (s ++ [i]) (pl (s ++ [i]) L) t) :
    Old D Sc cutoff v q →ₗ[k] ShortTarget D Sc cutoff i j v t := by
  subst q
  exact (BalancedInduction.inclusion (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i * D.parity j) j v) ⟨t⟩ ⟨s⟩) ∘ₗ
      TensorProduct.mk k _ _ (appendMovingPower D Sc cutoff i s m ≫
        affineUnit D Sc cutoff _ _ (cl D Sc _ _ L ht))

/-- Decode the crossing part of a normalized append tail. -/
def data (i j : I) (v q t : List I) (L : List PG) (m : ℕ) :
    Old D Sc cutoff v q →ₗ[k] ShortTarget D Sc cutoff i j v t := by
  by_cases hL : L = []
  · exact 0
  · by_cases hs : q = q.dropLast ++ [j]
    · by_cases ht : SChain (q.dropLast ++ [i]) (pl (q.dropLast ++ [i]) L.tail) t
      · exact SKM.zsign k (D.parity i * D.parity j) ^ m •
          wordLift D Sc cutoff i j v q q.dropLast t hs L.tail m ht
      · exact 0
    · exact 0

/-- Full old quotient coordinates are decoded without choosing representatives in the ideal. -/
def decode (i j : I) (v t : List I) :
    AppendTarget D Sc cutoff i v (t ++ [j]) →ₗ[k] ShortTarget D Sc cutoff i j v t :=
  (DirectSum.toModule k _ _ fun q : AppendIdx.Tail i v (t ++ [j]) =>
    data D Sc cutoff i j v q.representative.oldTarget t
      (cw (Categorification.TypeA.canWord (v ++ [i]).length
        q.representative.1.2.2.2.1⁻¹)) q.representative.1.1) ∘ₗ
      (appendOldCoordinateEquiv D Sc cutoff 0 i v (t ++ [j])).toLinearMap

@[simp] theorem data_nil (i j : I) (v q t : List I) (m : ℕ) :
    data D Sc cutoff i j v q t [] m = 0 := by
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

@[simp] theorem data_cross (i j : I) (v s t : List I) (L : List PG) (m : ℕ)
    (h : SChain (s ++ [i]) (pl (s ++ [i]) L) t)
    (b : Old D Sc cutoff v (s ++ [j])) :
    data D Sc cutoff i j v (s ++ [j]) t (PG.cross s.length :: L) m b =
      SKM.zsign k (D.parity i * D.parity j) ^ m •
        shortTensor D Sc cutoff i j v s t
          (appendMovingPower D Sc cutoff i s m ≫
            affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h)) b := by
  dsimp only [data]
  rw [dite_eq_right (List.cons_ne_nil _ _)]
  have he : (s ++ [j]).dropLast = s := List.dropLast_concat
  rw [dite_eq_left (congrArg (· ++ [j]) he).symm]
  have ht : SChain ((s ++ [j]).dropLast ++ [i])
      (pl ((s ++ [j]).dropLast ++ [i]) (PG.cross s.length :: L).tail) t := by
    simpa only [he, List.tail_cons] using h
  rw [dite_eq_left ht, LinearMap.smul_apply]
  congr 1
  have aux (s' : List I) (e : s' = s) (hs : s ++ [j] = s' ++ [j])
      (hc : SChain (s' ++ [i]) (pl (s' ++ [i]) L) t) :
      wordLift D Sc cutoff i j v (s ++ [j]) s' t hs L m hc b =
        shortTensor D Sc cutoff i j v s t
          (appendMovingPower D Sc cutoff i s m ≫
            affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h)) b := by
    subst s'; rfl
  exact aux _ he _ ht

theorem decode_pair_representative (i j : I) (v t : List I)
    (q : AppendIdx.Tail i v (t ++ [j]))
    (b : Old D Sc cutoff v q.representative.oldTarget) :
    decode D Sc cutoff i j v t
      (appendPair D Sc cutoff 0 i (affineUnit D Sc cutoff _ _
        (appendTail D Sc q.representative)) b) =
    data D Sc cutoff i j v q.representative.oldTarget t
      (cw (Categorification.TypeA.canWord (v ++ [i]).length
        q.representative.1.2.2.2.1⁻¹)) q.representative.1.1 b := by
  have he : decode D Sc cutoff i j v t
      (appendOldReconstruct D Sc cutoff 0 i v (t ++ [j]) (DirectSum.lof k _ _ q b)) =
      data D Sc cutoff i j v q.representative.oldTarget t
        (cw (Categorification.TypeA.canWord (v ++ [i]).length
          q.representative.1.2.2.2.1⁻¹)) q.representative.1.1 b := by
    simp only [decode, LinearMap.comp_apply, LinearEquiv.coe_coe,
      appendOldCoordinateEquiv_reconstruct, DirectSum.toModule_lof]
  have hu : affineUnit D Sc cutoff _ _ (appendTail D Sc q.representative) =
      ((1 : SKM.SYM.ELVCoefficientAlgebra (k := k) D cutoff) ⊗ₜ[k]
        appendTail D Sc q.representative : hom D Sc cutoff
          (q.representative.oldTarget ++ [i]) (t ++ [j])) := rfl
  rw [hu]
  simpa only [appendOldReconstruct, DirectSum.toModule_lof] using he

private theorem data_transport (i j : I) {v s s' t : List I}
    (e : s = s') (L : List PG) (m : ℕ) (r : hom D Sc cutoff v s) :
    data D Sc cutoff i j v s t L m ((ideal D Sc cutoff v s).mkQ r) =
    data D Sc cutoff i j v s' t L m ((ideal D Sc cutoff v s').mkQ (e ▸ r)) := by
  subst s'; rfl

/-- Repeated old normal forms with the same tail give the same decoded balanced class. -/
theorem decode_pair (i j : I) (v t : List I)
    (x : AppendIdx i v (t ++ [j])) (r : hom D Sc cutoff v x.oldTarget) :
    decode D Sc cutoff i j v t
      (appendPair D Sc cutoff 0 i (affineUnit D Sc cutoff _ _ (appendTail D Sc x))
        ((ideal D Sc cutoff v x.oldTarget).mkQ r)) =
    data D Sc cutoff i j v x.oldTarget t
      (cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹)) x.1.1
        ((ideal D Sc cutoff v x.oldTarget).mkQ r) := by
  let q : AppendIdx.Tail i v (t ++ [j]) := ⟨x.tailKey, x, rfl⟩
  have hk : x.tailKey = q.representative.tailKey := q.representative_tailKey.symm
  have ht := x.oldTarget_eq_of_tailKey_eq q.representative hk
  rw [appendTailPair_transport D Sc cutoff ht r _ _
    (appendTail_heq_of_tailKey_eq D Sc x q.representative hk), decode_pair_representative]
  have hm := congrArg Prod.fst hk
  have hd := congrArg Prod.snd hk
  change x.1.1 = q.representative.1.1 at hm
  change x.1.2.2.2 = q.representative.1.2.2.2 at hd
  rw [← hm, ← hd]
  exact (data_transport D Sc cutoff i j ht _ _ r).symm

/-- The mixed crossing word in the old-only append quotient. -/
def crossingClass (i j : I) (v s t : List I)
    (r : hom D Sc cutoff v (s ++ [j])) (c : hom D Sc cutoff (s ++ [i]) t) :
    AppendTarget D Sc cutoff i v (t ++ [j]) :=
  appendProjection D Sc cutoff i v (t ++ [j])
    (rightContext D Sc cutoff [i] _ _ r ≫
      affineUnit D Sc cutoff _ _ (crossLast D Sc s j i) ≫
      rightContext D Sc cutoff [j] _ _ c)

theorem decode_canonical_crossing (i j : I) (hij : i ≠ j) (v s t : List I)
    (x : AppendIdx i v (t ++ [j])) (e : x.oldTarget = s ++ [j])
    (L : List PG)
    (hw : cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) =
      PG.cross s.length :: L)
    (hf : Fits (s ++ [i]).length L)
    (h : SChain (s ++ [i]) (pl (s ++ [i]) L) t)
    (r : hom D Sc cutoff v x.oldTarget) :
    decode D Sc cutoff i j v t
      (crossingClass D Sc cutoff i j v s t (e ▸ r)
        (appendMovingPower D Sc cutoff i s x.1.1 ≫
          affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h))) =
      shortTensor D Sc cutoff i j v s t
        (appendMovingPower D Sc cutoff i s x.1.1 ≫
          affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h))
        ((ideal D Sc cutoff v (s ++ [j])).mkQ (e ▸ r)) := by
  have he := appendTailPair_transport D Sc cutoff e r _ _
    (appendTail_cross_heq D Sc i j v s t x e L hw hf h)
  have hc := decode_pair D Sc cutoff i j v t x r
  rw [he, hw, data_transport D Sc cutoff i j e, data_cross D Sc cutoff i j v s t L x.1.1 h] at hc
  simp only [appendPair_mk, twist_zero, affineUnit_comp,
    ← rightContext_affineUnit] at hc
  have hp : appendMovingPower D Sc cutoff i (s ++ [j]) x.1.1 =
      affineUnit D Sc cutoff _ _ ((dotE D Sc (s ++ [j] ++ [i]) (s.length + 1)) ^ x.1.1) := by
    simp only [appendMovingPower, List.length_append, List.length_singleton]
  rw [← hp, projection_crossing_power_slide D Sc cutoff i j hij, map_smul] at hc
  have hu : IsUnit (SKM.zsign k (D.parity i * D.parity j) ^ x.1.1) := by
    apply IsUnit.pow
    unfold SKM.zsign
    split <;> simp
  exact hu.smul_left_cancel.mp hc

/-- Recover every smaller append tail, including zero Hom corners. -/
theorem decode_crossing_tail (i j : I) (hij : i ≠ j) (v s t : List I)
    (z : AppendIdx i s t) (r : hom D Sc cutoff v (z.oldTarget ++ [j])) :
    decode D Sc cutoff i j v t
      (crossingClass D Sc cutoff i j v z.oldTarget t r
        (affineUnit D Sc cutoff _ _ (appendTail D Sc z))) =
      shortTensor D Sc cutoff i j v z.oldTarget t
        (affineUnit D Sc cutoff _ _ (appendTail D Sc z))
        ((ideal D Sc cutoff v (z.oldTarget ++ [j])).mkQ r) := by
  by_cases hr : r = 0
  · simp [hr, crossingClass, shortTensor, BalancedInduction.tensor]
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
  have htarget : tgt (z.oldTarget ++ [j] ++ [i])
      (cw (Categorification.TypeA.canWord (v ++ [i]).length d.1⁻¹)) = t ++ [j] := by
    rw [hd, show PG.cross s.length = PG.cross z.oldTarget.length from congrArg PG.cross hzlen.symm,
      tgt_cons]
    have hcross : tgt (z.oldTarget ++ [j] ++ [i]) [PG.cross z.oldTarget.length] =
        z.oldTarget ++ [i] ++ [j] := tgt_eq (by simpa using sChain_crossAt z.oldTarget [] j i)
    simp only [tgt_cons, tgt_nil] at hcross
    rw [hcross]
    exact (tgt_append_right [j] hf).trans (congrArg (· ++ [j]) (tgt_eq hc))
  let x := appendIndexWithTail i y d z.1.1 htarget
  have he : x.oldTarget = z.oldTarget ++ [j] := appendIndexWithTail_target i y d z.1.1 htarget
  let r' : hom D Sc cutoff v x.oldTarget := he.symm ▸ r
  have hr' : he ▸ r' = r := by
    exact (show ∀ {a b : List I} (e : a = b) (q : hom D Sc cutoff v b),
      e ▸ (e.symm ▸ q : hom D Sc cutoff v a) = q from
        by intro a b e q; cases e; rfl) he r
  have hword : cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) =
      PG.cross z.oldTarget.length :: L := by simpa only [x, appendIndexWithTail, hzlen] using hd
  have hh := decode_canonical_crossing D Sc cutoff i j hij v z.oldTarget t
    x he L hword hf hc r'
  rw [hr'] at hh
  rw [appendTail_power_cross]
  exact hh

/-- Full affine balance in the independently defined short source. -/
theorem tensor_balance (i j : I) (v s s' t : List I)
    (r : hom D Sc cutoff s s') (c : hom D Sc cutoff (s' ++ [i]) t)
    (b : Old D Sc cutoff v (s ++ [j])) :
    shortTensor D Sc cutoff i j v s t (rightContext D Sc cutoff [i] _ _ r ≫ c) b =
      shortTensor D Sc cutoff i j v s' t c
        ((coefficient D Sc cutoff (D.parity i * D.parity j) j v).map
          ((ideal D Sc cutoff s s').mkQ r) b) :=
  BalancedInduction.balance (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i * D.parity j) j v)
    (v := ⟨s⟩) (v' := ⟨s'⟩) r c b

/-- The prescribed column on an arbitrary lifted old quotient coefficient. -/
theorem column_mk (i j : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (r : hom D Sc cutoff v (s ++ [j])) :
    shortCross D Sc cutoff i j v t
      (shortTensor D Sc cutoff i j v s t c ((ideal D Sc cutoff _ _).mkQ r)) =
      crossingClass D Sc cutoff i j v s t r c := by
  rw [shortCross_tensor, shortCrossPair_mk]
  rfl

/-- Recovery on a smaller tail for every old quotient coefficient. -/
theorem decode_short_tail (i j : I) (hij : i ≠ j) (v s t : List I) (z : AppendIdx i s t)
    (b : Old D Sc cutoff v (z.oldTarget ++ [j])) :
    decode D Sc cutoff i j v t (shortCross D Sc cutoff i j v t
      (shortTensor D Sc cutoff i j v z.oldTarget t
        (affineUnit D Sc cutoff _ _ (appendTail D Sc z)) b)) =
      shortTensor D Sc cutoff i j v z.oldTarget t
        (affineUnit D Sc cutoff _ _ (appendTail D Sc z)) b := by
  obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v (z.oldTarget ++ [j])).mkQ_surjective b
  rw [column_mk]
  exact decode_crossing_tail D Sc cutoff i j hij v s t z r

/-- Every full-coefficient balanced generator is recovered. -/
theorem decode_tensor (i j : I) (hij : i ≠ j) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [j])) :
    decode D Sc cutoff i j v t (shortCross D Sc cutoff i j v t
      (shortTensor D Sc cutoff i j v s t c b)) = shortTensor D Sc cutoff i j v s t c b := by
  obtain ⟨f, rfl⟩ := (appendAffineEquiv D Sc cutoff i s t).symm.surjective c
  induction f using Finsupp.induction_linear with
  | zero => simp [shortTensor, BalancedInduction.tensor]
  | add f g hf hg =>
    have hadd (c c' : hom D Sc cutoff (s ++ [i]) t) :
        shortTensor D Sc cutoff i j v s t (c + c') b =
          shortTensor D Sc cutoff i j v s t c b + shortTensor D Sc cutoff i j v s t c' b := by
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
    exact decode_short_tail D Sc cutoff i j hij v s t z _

/-- Left inverse on all balanced classes, not only their chosen representatives. -/
theorem decode_comp_shortCross (i j : I) (hij : i ≠ j) (v t : List I) :
    decode D Sc cutoff i j v t ∘ₗ shortCross D Sc cutoff i j v t = LinearMap.id := by
  apply BalancedInduction.hom_ext
  intro s c b
  exact decode_tensor D Sc cutoff i j hij v s.word t c b

@[simp] theorem decode_shortCross (i j : I) (hij : i ≠ j) (v t : List I)
    (z : ShortTarget D Sc cutoff i j v t) :
    decode D Sc cutoff i j v t (shortCross D Sc cutoff i j v t z) = z :=
  LinearMap.congr_fun (decode_comp_shortCross D Sc cutoff i j hij v t) z

theorem shortCross_injective (i j : I) (hij : i ≠ j) (v t : List I) :
    Function.Injective (shortCross D Sc cutoff i j v t) :=
  Function.LeftInverse.injective (decode_shortCross D Sc cutoff i j hij v t)

/-- Every mixed append tail lies in the crossing column; distinct support
leaves no polynomial row. -/
theorem appendPair_mem_range_shortCross (i j : I) (hij : i ≠ j) (v t : List I)
    (x : AppendIdx i v (t ++ [j])) (r : hom D Sc cutoff v x.oldTarget) :
    appendPair D Sc cutoff 0 i (affineUnit D Sc cutoff _ _ (appendTail D Sc x))
      ((ideal D Sc cutoff v x.oldTarget).mkQ r) ∈
      LinearMap.range (shortCross D Sc cutoff i j v t) := by
  obtain ⟨s, L, e, hw, hf, h⟩ := appendTail_mixed_shape i j hij v t x
  rw [appendTailPair_transport D Sc cutoff e r _ _
    (appendTail_cross_heq D Sc i j v s t x e L hw hf h)]
  simp only [appendPair_mk, twist_zero, affineUnit_comp, ← rightContext_affineUnit]
  have hp : affineUnit D Sc cutoff _ _
      ((dotE D Sc (s ++ [j] ++ [i]) (s.length + 1)) ^ x.1.1) =
      appendMovingPower D Sc cutoff i (s ++ [j]) x.1.1 := by
    simp only [appendMovingPower, List.length_append, List.length_singleton]
  rw [hp, projection_crossing_power_slide D Sc cutoff i j hij]
  refine ⟨SKM.zsign k (D.parity i * D.parity j) ^ x.1.1 •
    shortTensor D Sc cutoff i j v s t
      (appendMovingPower D Sc cutoff i s x.1.1 ≫
        affineUnit D Sc cutoff _ _ (cl D Sc _ _ L h))
      ((ideal D Sc cutoff v (s ++ [j])).mkQ (e ▸ r)), ?_⟩
  rw [map_smul, column_mk]
  rfl

/-- The crossing column is onto the entire mixed old-only append target. -/
theorem shortCross_surjective (i j : I) (hij : i ≠ j) (v t : List I) :
    Function.Surjective (shortCross D Sc cutoff i j v t) := by
  intro z
  obtain ⟨f, rfl⟩ := appendOldReconstruct_surjective D Sc cutoff 0 i v (t ++ [j]) z
  change appendOldReconstruct D Sc cutoff 0 i v (t ++ [j]) f ∈
    LinearMap.range (shortCross D Sc cutoff i j v t)
  induction f using DirectSum.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | of q b =>
    obtain ⟨r, rfl⟩ := (ideal D Sc cutoff v q.representative.oldTarget).mkQ_surjective b
    change appendOldReconstruct D Sc cutoff 0 i v (t ++ [j]) (DirectSum.lof k _ _ q _) ∈ _
    rw [appendOldReconstruct, DirectSum.toModule_lof]
    exact appendPair_mem_range_shortCross D Sc cutoff i j hij v t q.representative r

/-- The explicit PBW crossing equivalence before the output-old quotient. -/
def crossingEquiv (i j : I) (hij : i ≠ j) (v t : List I) :
    ShortTarget D Sc cutoff i j v t ≃ₗ[k] AppendTarget D Sc cutoff i v (t ++ [j]) :=
  LinearEquiv.ofBijective (shortCross D Sc cutoff i j v t)
    ⟨shortCross_injective D Sc cutoff i j hij v t,
      shortCross_surjective D Sc cutoff i j hij v t⟩

@[simp] theorem crossingEquiv_symm (i j : I) (hij : i ≠ j) (v t : List I)
    (z : AppendTarget D Sc cutoff i v (t ++ [j])) :
    (crossingEquiv D Sc cutoff i j hij v t).symm z = decode D Sc cutoff i j v t z := by
  obtain ⟨w, rfl⟩ := shortCross_surjective D Sc cutoff i j hij v t z
  rw [decode_shortCross D Sc cutoff i j hij]
  exact (crossingEquiv D Sc cutoff i j hij v t).symm_apply_apply w

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
