/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.AppendContentShortWord
import OddMath.QuiverHecke.CyclotomicAction.ELVChronologicalShort
import OddMath.QuiverHecke.CyclotomicAction.ELVPrependCoordinates
noncomputable section
open CategoryTheory StringDiagrams MonoidalCategory Categorification.TypeA
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)

 theorem positioned_short_mem (i : I) (v s t : List I) (gs : List PG)
    (hf : Fits (i :: s).length gs)
    (hc : SChain ((i :: s) ++ [i]) (pl ((i :: s) ++ [i]) gs) (t ++ [i]))
    (r : hom D Sc cutoff v (s ++ [i])) :
    projection D Sc cutoff i v (t ++ [i])
      (insert D Sc cutoff i v (s ++ [i]) r ≫
        affineUnit D Sc cutoff _ _ (cl D Sc _ _ gs hc)) ∈
      chronologicalShortSpan D Sc cutoff i v t := by
  have ht : tgt (i :: s) gs = t := by
    have he := tgt_eq hc
    rw [tgt_append_right [i] hf] at he
    exact List.append_cancel_right he
  have hsmall : SChain (i :: s) (pl (i :: s) gs) t := by
    simpa only [ht] using sChain_pl (i :: s) gs
  apply Submodule.subset_span
  refine ⟨s, r, affineUnit D Sc cutoff _ _ (cl D Sc _ _ gs hsmall), ?_⟩
  rw [rightContext_affineUnit]
  congr 3
  exact (cl_whiskerRight D Sc gs hsmall [i] hf)

theorem positioned_short_mem_of_eq (i : I) (v q s t : List I) (hs : q = s ++ [i])
    (gs : List PG) (hf : Fits (i :: s).length gs)
    (hc : SChain (i :: q) (pl (i :: q) gs) (t ++ [i]))
    (r : hom D Sc cutoff v q) :
    projection D Sc cutoff i v (t ++ [i])
      (insert D Sc cutoff i v q r ≫ affineUnit D Sc cutoff _ _ (cl D Sc _ _ gs hc)) ∈
        chronologicalShortSpan D Sc cutoff i v t := by
  subst q
  exact positioned_short_mem D Sc cutoff i v s t gs hf hc r

theorem prepend_short_mem (i : I) (v t : List I)
    (x : PrependIdx i v (t ++ [i]))
    (hx : x.1.2.2.2 ≠ longPrependShuffle v.length)
    (r : hom D Sc cutoff v x.oldTarget) :
    projection D Sc cutoff i v (t ++ [i])
      (insert D Sc cutoff i v x.oldTarget r ≫
        affineUnit D Sc cutoff _ _ (prependTail D Sc x)) ∈
      chronologicalShortSpan D Sc cutoff i v t := by
  have hv : 0 < v.length := by
    cases v with
    | nil =>
      apply False.elim
      apply hx
      apply Subtype.ext
      apply Equiv.ext
      intro z
      apply Fin.ext
      have h₁ := (x.1.2.2.2.1 z).isLt
      have h₂ := ((longPrependShuffle (([] : List I).length)).1 z).isLt
      simp only [List.length_nil] at h₁ h₂ ⊢
      omega
    | cons a v => simp
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hv)
  have hlen : x.oldTarget.length = n + 1 := by
    simp [PrependIdx.oldTarget, hn]
  obtain ⟨s, j, hs⟩ : ∃ s j, x.oldTarget = s ++ [j] := by
    generalize x.oldTarget = q at hlen ⊢
    induction q using List.reverseRecOn with
    | nil => simp at hlen
    | append_singleton q j ih => exact ⟨q, j, rfl⟩
  have hsl : s.length = n := by rw [hs] at hlen; simp only [List.length_append,
    List.length_singleton] at hlen; omega
  have hf : Fits (i :: s).length (cw (canWord (v.length + 1) x.1.2.2.2.1⁻¹)) := by
    apply fits_cw
    intro b hb
    have hb' : b < n := by
      have aux (m : ℕ) (u : PrependShuffle m) (hu : u ≠ longPrependShuffle m)
          (hm : m = n + 1) : ∀ b ∈ canWord (m + 1) u.1⁻¹, b < n := by
        subst m
        exact canWord_prependShort_lt n u hu
      exact aux v.length x.1.2.2.2 hx hn b hb
    simp only [List.length_cons, hsl]
    omega
  have he := x.moving_target
  rw [hs] at he
  change tgt ((i :: s) ++ [j]) _ = _ at he
  rw [tgt_append_right [j] hf] at he
  have hj : j = i := by
    have hh := congrArg List.getLast? he
    simpa using hh
  subst j
  have hfull : Fits (i :: s).length
      (((List.replicate x.1.1 0).map PG.dot) ++
        cw (canWord (v.length + 1) x.1.2.2.2.1⁻¹)) := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hg
      have hb0 := (List.mem_replicate.mp hb).2
      subst b
      simp [PG.pos, PG.width]
    · exact hf g hg
  unfold prependTail
  exact positioned_short_mem_of_eq D Sc cutoff i v x.oldTarget s t hs _ hfull _ r

end OddMath.QuiverHecke.ELVOld
