import OddMath.Frontier.OwlGeneralStage

/-! The Omission Word Lemma (EKL arXiv:1111.1320v1, Lemma 2.18, p. 15), in its literal
termwise form, for an explicit all-rank class of reduced words of the longest element.

The printed lemma quantifies over every reduced expression; that is false in rank five
(`OwlDirect.owl_trichotomy_false`, `OwlBraid.owl_trichotomy_false`), and braid moves do
not transport it (`OwlBraid.braid_transport_false`).  The printed proof treats one chosen
ordering (`OmissionCanonical.trichotomy`).

`OwlClass n` consists of the words commutation-equivalent to a word of `Stage n (n+1)`:
starting from the empty word, repeatedly
* prepend the next descending chain `n, n-1, ..., n-r` (the printed block step, now for
  an arbitrary previously built word, `OwlGeneralStage.relOWL_step`), and
* optionally reverse the occupied top letters `i ↦ 2n+1-r-i`, realised on the carrier
  by the signed partial variable reversal (`OwlGeneralStage.relOWL_flip`).
It contains the commutation classes of the block word and of its diagram flip
(`blockClass_owlClass`), is closed under the diagram flip `i ↦ n-i`
(`owlClass_flip`) and under distant commutation, and excludes the rank-five braid
target (`not_owlClass_braid_target`).

Consumer: (2.64) for every word of the class with no residual hypothesis. -/
namespace OddMath.Frontier.OwlGeneral
open OddMath.SkewPolynomial (SkewPolynomial)
open NilCoxeterWords OmissionWord OwlGeneralStage
noncomputable section

/-- The proved OWL class: commutation classes of the stage-built words. -/
def OwlClass (n : ℕ) (w : Word n) : Prop :=
  ∃ v : Word n, Stage n (n+1) v ∧ CommEquiv w v

theorem owl_class (n : ℕ) (w : Word n) (h : OwlClass n w) : OwlBraid.OWLFor w := by
  obtain ⟨v, hs, hc⟩ := h
  exact owl_of_commEquiv hc.symm (owl_of_stage v hs)

/-- Every word of the class is a reduced expression of the longest element. -/
theorem owlClass_reduced_longest (n : ℕ) (w : Word n) (h : OwlClass n w) :
    Reduced w ∧ permutation w = LongestElementary.longest (n+2) := by
  obtain ⟨v, hs, hc⟩ := h
  have hp : permutation v = LongestElementary.longest (n+2) := permutation_of_stage v hs
  have hr : Reduced v := by
    obtain ⟨h, hl⟩ := stage_length hs
    have hb := OmissionCanonical.word_reduced n
    unfold Reduced at hb ⊢
    rw [hl, hp, ← OmissionCanonical.word_permutation n, ← hb, OmissionCanonical.word_blocks]
  exact ⟨reduced_of_commEquiv hc.symm hr, (permutation_of_commEquiv hc).trans hp⟩

/-- Main theorem.  EKL arXiv:1111.1320v1, Lemma 2.18 (p. 15), literal termwise form,
for every word of `OwlClass n`, every rank: for every marking, either the marked action
kills the joint kernel, or no letter is marked, or the omission word is non-reduced. -/
theorem owl_general (n : ℕ) (w : Word n) (h : OwlClass n w) :
    ∀ m : Marked n, erase m = w → Trichotomy m :=
  fun m hm => owl_class n w h m ((mem_markings m w).mpr hm)

/-- Consumer: EKL (2.64) for every word of the class, with no residual hypothesis. -/
theorem left_kernel_owl_class (n : ℕ) (w : Word n) (h : OwlClass n w)
    (f g : SkewPolynomial (n+2)) (hf : f ∈ OddSymmetricKernel.kernelSubring n) :
    LongestDivided.applyWord w (f*g) =
      SignedPermutation.skewAction (LongestElementary.longest (n+2)) f *
        LongestDivided.applyWord w g :=
  longest_left_kernel_of_trichotomy w (owlClass_reduced_longest n w h).2
    (owl_class n w h) f g hf

/-- The full-stage block word is the printed block word. -/
theorem stage_word (n : ℕ) : Stage n (n+1) (OmissionCanonical.word n) := by
  rw [OmissionCanonical.word_blocks]
  exact stage_blocks (n+1) le_rfl

theorem stage_top_flip {n : ℕ} {v : Word n} (hs : Stage n (n+1) v) :
    Stage n (n+1) (v.map Fin.rev) := by
  have := Stage.flip hs
  rwa [show flipL n (n+1) = Fin.rev from funext flipL_top] at this

/-- The commutation classes of the block word and of its flip lie in the class. -/
theorem blockClass_owlClass (n : ℕ) (w : Word n) (h : BlockClass n w) : OwlClass n w := by
  rcases h with h | h
  · exact ⟨_, stage_word n, h⟩
  · exact ⟨_, stage_top_flip (stage_word n), h⟩

/-- Closure under the diagram flip `i ↦ n - i`. -/
theorem owlClass_flip (n : ℕ) (w : Word n) (h : OwlClass n w) : OwlClass n (w.map Fin.rev) := by
  obtain ⟨v, hs, hc⟩ := h
  exact ⟨_, stage_top_flip hs, commEquiv_flip hc⟩

/-- Closure under commutation equivalence. -/
theorem owlClass_of_commEquiv (n : ℕ) {u w : Word n} (h : OwlClass n u) (hc : CommEquiv w u) :
    OwlClass n w := by
  obtain ⟨v, hs, hc'⟩ := h
  exact ⟨v, hs, hc.trans hc'⟩

/-- Sharpness in rank five: the braid target of `OwlBraid` is a reduced word of the
longest element outside the class (the lemma fails for it). -/
theorem not_owlClass_braid_target : ¬ OwlClass 3 OwlBraid.tgt :=
  fun h => OwlBraid.owl_tgt_false (owl_class 3 _ h)

/-- Distant commutation moves permute the letters of a word. -/
theorem perm_of_commEquiv {n : ℕ} {u w : Word n} (h : CommEquiv u w) : u.Perm w := by
  unfold CommEquiv at h
  induction h with
  | refl => exact List.Perm.refl _
  | tail _ hs ih =>
    obtain ⟨p, q, i, j, _, rfl, rfl⟩ := hs
    exact ih.trans (List.Perm.append_left p (List.Perm.swap j i q))

/-- A rank-five word of the class: the descending chain `3 2 1 0` followed by the flipped
stage-three block word. -/
def stageExample : Word 3 := [3,2,1,0,1,2,3,1,2,1]

theorem stage_example : Stage 3 4 stageExample := by
  have h := Stage.chain 3 (by omega) (Stage.flip (stage_blocks (n := 3) 3 (by omega)))
  have e : OmissionCanonical.down 3 (3-3) (3+1) (by omega) ++
      (OmissionCanonical.blocks 3 3 (by omega)).map (flipL 3 3) =
      stageExample := by decide
  rwa [e] at h

theorem owlClass_stageExample : OwlClass 3 stageExample :=
  ⟨_, stage_example, Relation.ReflTransGen.refl⟩

/-- The class strictly extends those two commutation classes: `stageExample` is not commutation-equivalent to the
block word or to its flip (the number of occurrences of the letter `1` differs). -/
theorem not_blockClass_stageExample : ¬ BlockClass 3 stageExample := by
  rintro (h | h)
  · have e := (perm_of_commEquiv h).count_eq (1 : Fin 4)
    revert e
    decide
  · have e := (perm_of_commEquiv h).count_eq (1 : Fin 4)
    revert e
    decide

end
end OddMath.Frontier.OwlGeneral
