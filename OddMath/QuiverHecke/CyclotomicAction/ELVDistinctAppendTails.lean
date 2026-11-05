/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVDistinctCrossingTensor
import OddMath.QuiverHecke.CyclotomicAction.ELVAppendCrossingTriangular

/-! # Distinct-colour append tails

The PBW crossing decoder for Brundan–Ellis (1.12) peels the first crossing
of every mixed append tail. Identity tails are absent by last-colour support;
the distinct-colour dot slide has no divided-difference correction.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
open scoped Classical DirectSum TensorProduct
namespace OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

theorem append_cl_heq {s s' t t' : List I} {L L' : List PG}
    (hs : s = s') (ht : t = t') (hL : L = L')
    (h : SChain s (pl s L) t) (h' : SChain s' (pl s' L') t') :
    HEq (cl D Sc s t L h) (cl D Sc s' t' L' h') := by
  subst s'
  subst t'
  subst L'
  rfl

def appendShuffleSizeCast {n n' : ℕ} (e : n = n') :
    AppendShuffle (show n + 1 = n + 1 from rfl) ≃
      AppendShuffle (show n' + 1 = n' + 1 from rfl) := by
  subst n'
  exact Equiv.refl _

theorem appendShuffleSizeCast_word {n n' : ℕ} (e : n = n')
    (d : AppendShuffle (show n + 1 = n + 1 from rfl)) :
    Categorification.TypeA.canWord (n' + 1) (appendShuffleSizeCast e d).1⁻¹ =
    Categorification.TypeA.canWord (n + 1) d.1⁻¹ := by
  subst n'
  rfl

def appendIndexWithTail (i : I) {v u w : List I} (y : NFIdx v u)
    (d : AppendShuffle (appendLen v i)) (m : ℕ)
    (h : tgt (u ++ [i]) (cw (Categorification.TypeA.canWord (v ++ [i]).length d.1⁻¹)) = w) :
    AppendIdx i v w :=
  ⟨(m, y.1.1, y.1.2, d), y.2.1, y.2.2.1, by
    rw [appendCrossingWord, cw_append, tgt_append,
      tgt_append_right [i] (fits_cw (Categorification.TypeA.validWord_canWord v.length y.1.2)),
      y.tgt_cw]
    exact h⟩

theorem appendIndexWithTail_target (i : I) {v u w : List I} (y : NFIdx v u)
    (d : AppendShuffle (appendLen v i)) (m : ℕ)
    (h : tgt (u ++ [i]) (cw (Categorification.TypeA.canWord (v ++ [i]).length d.1⁻¹)) = w) :
    (appendIndexWithTail i y d m h).oldTarget = u := y.tgt_cw

theorem appendTail_cross_chain {i : I} {s t : List I} (z : AppendIdx i s t) :
    SChain (z.oldTarget ++ [i])
      (pl (z.oldTarget ++ [i]) (cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹))) t := by
  have hz := z.2.2.2
  rw [appendCrossingWord, cw_append, tgt_append,
    tgt_append_right [i] (fits_cw (Categorification.TypeA.validWord_canWord s.length z.1.2.2.1))] at hz
  change tgt (z.oldTarget ++ [i])
    (cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹)) = t at hz
  simpa only [hz] using sChain_pl (z.oldTarget ++ [i])
    (cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹))

theorem appendTail_cross_fits {i : I} {s t : List I} (z : AppendIdx i s t) :
    Fits (z.oldTarget ++ [i]).length
      (cw (Categorification.TypeA.canWord (s ++ [i]).length z.1.2.2.2.1⁻¹)) := by
  simpa only [AppendIdx.oldTarget, List.length_append, length_tgt] using
    fits_cw (Categorification.TypeA.validWord_canWord (s ++ [i]).length z.1.2.2.2.1⁻¹)

theorem appendRunWord_castSucc (n : ℕ) (j : Fin (n + 1)) :
    cw (Categorification.TypeA.canWord (n + 2) (appendRun (n + 1) j.castSucc).1⁻¹) =
      PG.cross n :: cw (Categorification.TypeA.canWord (n + 1) (appendRun n j).1⁻¹) := by
  rw [canWord_appendRun, canWord_appendRun, Fin.val_castSucc]
  have hj : j.val ≤ n := Nat.lt_succ_iff.mp j.2
  rw [show n + 1 - j.val = (n - j.val) + 1 by omega, List.range'_concat, cw_append]
  simp only [cw, List.reverse_singleton, List.map_singleton, List.cons_append, List.nil_append]
  congr 2
  omega

theorem appendCrossingShuffle_exists (i : I) (v s t : List I)
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

theorem appendTail_power_cross (i : I) (s t : List I) (z : AppendIdx i s t) :
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

/-- The first crossing exchanges the two literal last colours, with the
unchanged final output colour retained as a spectator through the tail. -/
theorem appendTail_cross_heq (i j : I) (v s t : List I)
    (x : AppendIdx i v (t ++ [j])) (e : x.oldTarget = s ++ [j])
    (L : List PG)
    (hw : cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) =
      PG.cross s.length :: L)
    (hf : Fits (s ++ [i]).length L)
    (h : SChain (s ++ [i]) (pl (s ++ [i]) L) t) :
    HEq (appendTail D Sc x)
      (((dotE D Sc (s ++ [j] ++ [i]) (s.length + 1)) ^ x.1.1) ≫
        crossLast D Sc s j i ≫ affineRightContext D Sc [j] _ _ (cl D Sc _ _ L h)) := by
  have hl : v.length = s.length + 1 := by
    have hh := congrArg List.length e
    simpa only [AppendIdx.oldTarget, length_tgt, List.length_append,
      List.length_singleton] using hh
  change HEq (appendTail D Sc x)
    (_ ≫ crossLast D Sc s j i ≫ (cl D Sc _ _ L h ▷ (pres D Sc).obj (ob D [j])))
  rw [dotE_pow, crossLast, cl_whiskerRight D Sc _ _ [j] hf, cl_comp, cl_comp]
  unfold appendTail
  apply append_cl_heq D Sc (congrArg (· ++ [i]) e) rfl
  simp only [hw, hl, List.map_replicate, List.singleton_append]

theorem appendRunWord_mixed_shape (i j : I) (hij : i ≠ j)
    (u t : List I) (n : ℕ) (hn : u.length = n) (a : Fin (n + 1))
    (ht : tgt (u ++ [i]) (cw (Categorification.TypeA.canWord (n + 1)
      (appendRun n a).1⁻¹)) = t ++ [j]) :
    ∃ (s : List I) (L : List PG), u = s ++ [j] ∧
      cw (Categorification.TypeA.canWord (n + 1) (appendRun n a).1⁻¹) = PG.cross s.length :: L ∧
      Fits (s ++ [i]).length L ∧ SChain (s ++ [i]) (pl (s ++ [i]) L) t := by
  cases n with
  | zero =>
    have ha : a = Fin.last 0 := by apply Fin.ext; have := a.2; simp only [Fin.val_last]; omega
    have hw : cw (Categorification.TypeA.canWord 1 (appendRun 0 a).1⁻¹) = [] := by
      rw [ha, canWord_appendRun]
      simp
    rw [hw, tgt_nil] at ht
    have he : i = j := by simpa using congrArg List.getLast? ht
    exact (hij he).elim
  | succ n =>
    revert ht
    refine Fin.lastCases ?_ (fun a => ?_) a
    · intro ht
      have hw : cw (Categorification.TypeA.canWord (n + 1 + 1)
          (appendRun (n + 1) (Fin.last (n + 1))).1⁻¹) = [] := by
        rw [canWord_appendRun]
        simp
      rw [hw, tgt_nil] at ht
      have he : i = j := by simpa using congrArg List.getLast? ht
      exact (hij he).elim
    · intro ht
      have hu : u ≠ [] := by intro h; simp [h] at hn
      obtain ⟨s, c, rfl⟩ := (List.eq_nil_or_concat' u).resolve_left hu
      have hs : s.length = n := by
        simpa only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff] using hn
      let L := cw (Categorification.TypeA.canWord (n + 1) (appendRun n a).1⁻¹)
      have hw : cw (Categorification.TypeA.canWord (n + 2)
          (appendRun (n + 1) a.castSucc).1⁻¹) = PG.cross s.length :: L := by
        simpa only [hs] using appendRunWord_castSucc n a
      have hf : Fits (s ++ [i]).length L := by
        simpa only [List.length_append, List.length_singleton, hs] using
          fits_cw (Categorification.TypeA.validWord_canWord (n + 1) (appendRun n a).1⁻¹)
      rw [hw, tgt_cons] at ht
      have hcross : (PG.cross s.length).act (s ++ [c] ++ [i]) = s ++ [i] ++ [c] := by
        have hc : tgt (s ++ [c] ++ [i]) [PG.cross s.length] = s ++ [i] ++ [c] :=
          tgt_eq (by simpa using sChain_crossAt s [] c i)
        simpa only [tgt_cons, tgt_nil] using hc
      rw [hcross, tgt_append_right [c] hf] at ht
      have hcj : c = j := by simpa using congrArg List.getLast? ht
      subst c
      have ht' := List.append_cancel_right ht
      exact ⟨s, L, rfl, hw, hf, by rw [← ht']; exact sChain_pl _ _⟩

/-- Every mixed append coordinate has a first crossing; no identity row is
discarded or quotiented out. -/
theorem appendTail_mixed_shape (i j : I) (hij : i ≠ j) (v t : List I)
    (x : AppendIdx i v (t ++ [j])) :
    ∃ (s : List I) (L : List PG), x.oldTarget = s ++ [j] ∧
      cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) = PG.cross s.length :: L ∧
      Fits (s ++ [i]).length L ∧ SChain (s ++ [i]) (pl (s ++ [i]) L) t := by
  let d₀ := AppendShuffle.cast (appendLen v i) rfl x.1.2.2.2
  let a := (appendRunEquiv v.length).symm d₀
  have ha : appendRun v.length a = d₀ := (appendRunEquiv v.length).apply_symm_apply d₀
  have hw : cw (Categorification.TypeA.canWord (v.length + 1) (appendRun v.length a).1⁻¹) =
      cw (Categorification.TypeA.canWord (v ++ [i]).length x.1.2.2.2.1⁻¹) := by
    rw [ha, AppendShuffle.canWord_cast]
  have hl : x.oldTarget.length = v.length := by simp only [AppendIdx.oldTarget, length_tgt]
  have ht : tgt (x.oldTarget ++ [i])
      (cw (Categorification.TypeA.canWord (v.length + 1) (appendRun v.length a).1⁻¹)) = t ++ [j] := by
    rw [hw]
    exact tgt_eq (appendTail_cross_chain x)
  simpa only [hw] using appendRunWord_mixed_shape i j hij x.oldTarget t v.length hl a ht

end OddMath.QuiverHecke.ELVOld.CyclotomicCrossingTensor.Distinct
