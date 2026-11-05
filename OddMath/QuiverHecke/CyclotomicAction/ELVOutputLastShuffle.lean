/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.AppendShuffleRuns
import OddMath.QuiverHecke.ShuffleBasis

/-! # Output-last shuffle words

The output-last PBW expansion in `DeformedActionAssembly.md` §2 uses the
shuffle itself, rather than its inverse from the input-side append basis.
Its canonical word is the descending run. This distinction is needed to
move a first-position ELV relation past every nonlong output shuffle.
-/

noncomputable section
open Categorification.TypeA Equiv
namespace OddMath.QuiverHecke

/-- Output-last shuffles use descending words; input append tails use their
inverse ascending words. -/
theorem canWord_appendRun_forward (n : ℕ) (r : Fin (n + 1)) :
    canWord (n + 1) (appendRun n r).1 = descRun r.val (n - r.val) := by
  change canWord (n + 1) (runPerm n r.val)⁻¹ = _
  rw [runPerm, ← wordProd_reverse]
  change canWord (n + 1) (wordProd (n + 1) (descRun r.val (n - r.val))) = _
  cases n with
  | zero =>
    simpa only [Nat.zero_sub, descRun_zero, codeWord_nil] using
      (canWord_wordProd_codeWord (m := 1) (c := []) isCode_nil (by decide))
  | succ n =>
    have hc : IsCode (r.val :: idCode n) :=
      ⟨by rw [length_idCode]; omega, isCode_idCode n⟩
    have hw : codeWord (r.val :: idCode n) = descRun r.val (n + 1 - r.val) := by
      simp only [codeWord_cons, codeWord_idCode, length_idCode, List.nil_append]
    rw [← hw]
    exact canWord_wordProd_codeWord hc (by simp only [List.length_cons, length_idCode]; omega)

theorem cw_descRun (r n : ℕ) :
    cw (descRun r n) = (List.range' r n).map PG.cross := by
  simp only [cw, descRun, List.reverse_reverse]

/-- The long output-last shuffle moves the first colour to the last slot. -/
theorem outputLast_long_target {I : Type*} (i : I) (v : List I) :
    tgt (i :: v) (cw (descRun 0 v.length)) = v ++ [i] := by
  rw [cw_descRun]
  induction v with
  | nil => rfl
  | cons j v ih =>
    rw [List.length_cons, List.range'_succ, List.map_cons, tgt_cons]
    change tgt (j :: i :: v) ((List.range' 1 v.length).map PG.cross) = _
    have hs : (List.range' 1 v.length).map PG.cross =
        ((List.range' 0 v.length).map PG.cross).map (PG.shift 1) := by
      rw [show (1 : ℕ) = 0 + 1 from rfl, List.range'_succ_left]
      simp only [List.map_map]
      apply List.map_congr_left
      intro x _
      exact congrArg PG.cross (Nat.add_comm x 1)
    rw [hs]
    change tgt ([j] ++ (i :: v))
      (((List.range' 0 v.length).map PG.cross).map (PG.shift [j].length)) = _
    rw [tgt_shift, ih]
    rfl

theorem outputLast_last_block {I : Type*} {s t : List I} {j : I}
    {hlen : t.length + [j].length = s.length} (x : ShIdx hlen) :
    shR s t.length x.1.1 = [j] := by
  have hs : (shR s t.length x.1.1).length = 1 := by
    rw [length_shR]
    simp only [List.length_singleton] at hlen
    omega
  have hc : code (shR s t.length x.1.1).length x.2.2.1.2 = [] :=
    List.length_eq_zero_iff.mp (by rw [length_code, hs])
  have hp := x.2.2.tgt_cw
  simpa only [canWord, hc, codeWord_nil, cw_nil, tgt_nil] using hp

/-- Every admissible mixed output-last shuffle is a word on the tail after
the first strand. The first strand is a spectator throughout, not merely at
the two endpoints. -/
theorem outputLast_tail_word {I : Type*} {i j : I} (hij : i ≠ j) (v : List I)
    (n : ℕ) (hn : n + 1 = (i :: v).length) (d : Shuffle hn)
    (hj : shR (i :: v) n d.1 = [j]) :
    ∃ L : List ℕ, ValidWord v.length L ∧
      cw (canWord (i :: v).length d.1) = (cw L).map (PG.shift 1) := by
  have hnv : n = v.length := by simpa only [List.length_cons, Nat.add_right_cancel_iff] using hn
  subst n
  obtain ⟨r, rfl⟩ := (appendRunEquiv v.length).surjective d
  simp only [appendRunEquiv_apply] at hj ⊢
  have hword : canWord (i :: v).length (appendRun v.length r).1 =
      descRun r.val (v.length - r.val) := canWord_appendRun_forward v.length r
  have hr : 0 < r.val := by
    by_contra h
    have hr0 : r.val = 0 := by omega
    rw [shR, shTop, hword, hr0, Nat.sub_zero, outputLast_long_target,
      List.drop_left] at hj
    exact hij (List.singleton_inj.mp hj)
  refine ⟨descRun (r.val - 1) (v.length - r.val), ?_, ?_⟩
  · intro a ha
    rw [mem_descRun] at ha
    have hrv := r.isLt
    omega
  · have hshift := List.range'_succ_left (s := r.val - 1) (n := v.length - r.val) (step := 1)
    rw [show r.val - 1 + 1 = r.val from by omega] at hshift
    rw [hword, cw_descRun, cw_descRun, hshift]
    simp only [List.map_map]
    apply List.map_congr_left
    intro a _
    exact congrArg PG.cross (Nat.add_comm a 1)

/-- The two output blocks of a mixed shuffle have a first-colour spectator
factorization, with the actual lower word of the tail retained. -/
theorem outputLast_tail_factor {I : Type*} {i j : I} (hij : i ≠ j) (v : List I)
    (n : ℕ) (hn : n + 1 = (i :: v).length) (d : Shuffle hn)
    (hj : shR (i :: v) n d.1 = [j]) :
    ∃ (s : List I) (L : List ℕ), ValidWord v.length L ∧
      shL (i :: v) n d.1 = i :: s ∧ tgt v (cw L) = s ++ [j] ∧
      cw (canWord (i :: v).length d.1) = (cw L).map (PG.shift 1) := by
  obtain ⟨L, hL, hw⟩ := outputLast_tail_word hij v n hn d hj
  have ht : shL (i :: v) n d.1 ++ [j] = i :: tgt v (cw L) := by
    rw [← hj, shL_append_shR, shTop, hw]
    exact tgt_shift [i] v (cw L)
  cases hs : shL (i :: v) n d.1 with
  | nil =>
    simp only [hs, List.nil_append] at ht
    exact (hij (List.cons.inj ht).1.symm).elim
  | cons c s =>
    simp only [hs, List.cons_append] at ht
    have hhead : c = i := (List.cons.inj ht).1
    have htail : s ++ [j] = tgt v (cw L) := (List.cons.inj ht).2
    subst c
    exact ⟨s, L, hL, rfl, htail.symm, hw⟩

end OddMath.QuiverHecke
