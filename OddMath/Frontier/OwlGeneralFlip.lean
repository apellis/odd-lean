import OddMath.Frontier.OwlBraid
import OddMath.Frontier.OddSchubertAction

/-! Helper for `OwlGeneral`: the Omission Word Lemma (EKL arXiv:1111.1320v1, Lemma 2.18,
p. 15) for every reduced word in the commutation class of the block word or of its
diagram flip (`BlockClass`).  `OwlGeneral.lean` enlarges this class via `OwlGeneralStage`.

The printed lemma quantifies over every reduced expression of the longest element;
that statement is false in rank five (`OwlDirect.owl_trichotomy_false`,
`OwlBraid.owl_trichotomy_false`).  The printed proof treats one chosen ordering,
formalized as `OmissionCanonical.trichotomy`.  This module proves the lemma, in its
literal termwise form, for the largest class obtained from that word by operations
that provably transport it on the actual operators:

* distant commutation moves `i j ↦ j i` (`|i - j| ≥ 2`), via `OwlBraid.owl_commute`;
* the diagram flip `i ↦ n - i`, realised on the carrier by the signed variable
  reversal `x_k ↦ ε x_{N-1-k}`, which conjugates `s_i` to `s_{n-i}` and `∂_i` to
  `ε ∂_{n-i}` and preserves the joint kernel.

Consumer: the (2.64) left-kernel identity holds for every word of the class with no
residual hypothesis.  Braid moves do not transport the lemma
(`OwlBraid.braid_transport_false`); accordingly the class excludes the rank-five
braid target. -/
namespace OddMath.Frontier.OwlGeneral
open OddMath.SkewPolynomial (SkewPolynomial generator)
open NilCoxeterWords OmissionWord AllRankDivided OwlBraid
noncomputable section

variable {n : ℕ}

/-! ### Commutation classes -/

/-- One distant commutation move `p i j q ↦ p j i q` with `|i - j| ≥ 2`. -/
def CommStep (u v : Word n) : Prop :=
  ∃ (p q : Word n) (i j : Fin (n+1)), Distant i j ∧ u = p ++ i::j::q ∧ v = p ++ j::i::q

/-- Commutation equivalence: the reflexive-transitive closure of distant moves. -/
def CommEquiv (u v : Word n) : Prop := Relation.ReflTransGen CommStep u v

theorem CommStep.symm {u v : Word n} (h : CommStep u v) : CommStep v u := by
  obtain ⟨p, q, i, j, hd, rfl, rfl⟩ := h
  exact ⟨p, q, j, i, hd.symm, rfl, rfl⟩

theorem CommEquiv.symm {u v : Word n} (h : CommEquiv u v) : CommEquiv v u :=
  Relation.ReflTransGen.symmetric (fun _ _ h => CommStep.symm h) h

theorem CommEquiv.trans {u v w : Word n} (h : CommEquiv u v) (h' : CommEquiv v w) :
    CommEquiv u w :=
  Relation.ReflTransGen.trans h h'

theorem permutation_of_commStep {u v : Word n} (h : CommStep u v) :
    permutation u = permutation v := by
  obtain ⟨p, q, i, j, hd, rfl, rfl⟩ := h
  exact permutation_swap p q i j hd

theorem permutation_of_commEquiv {u v : Word n} (h : CommEquiv u v) :
    permutation u = permutation v := by
  induction h with
  | refl => rfl
  | tail _ hs ih => exact ih.trans (permutation_of_commStep hs)

theorem length_of_commEquiv {u v : Word n} (h : CommEquiv u v) : u.length = v.length := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
      obtain ⟨p, q, i, j, _, rfl, rfl⟩ := hs
      rw [ih]; simp

theorem reduced_of_commEquiv {u v : Word n} (h : CommEquiv u v) (hu : Reduced u) :
    Reduced v := by
  unfold Reduced at *
  rw [← length_of_commEquiv h, ← permutation_of_commEquiv h, hu]

theorem owl_of_commStep {u v : Word n} (h : CommStep u v) (hu : OWLFor u) : OWLFor v := by
  obtain ⟨p, q, i, j, hd, rfl, rfl⟩ := h
  exact owl_commute p q i j hd hu

/-- Commutation equivalence transports the all-markings termwise trichotomy. -/
theorem owl_of_commEquiv {u v : Word n} (h : CommEquiv u v) (hu : OWLFor u) : OWLFor v := by
  induction h with
  | refl => exact hu
  | tail _ hs ih => exact owl_of_commStep hs ih

/-- The block word satisfies the lemma for all markings (`OmissionCanonical.trichotomy`). -/
theorem owl_word (n : ℕ) : OWLFor (OmissionCanonical.word n) :=
  fun m hm => OmissionCanonical.trichotomy n m ((mem_markings m _).mp hm)

/-- EKL arXiv:1111.1320v1, Lemma 2.18 (p. 15), for every word commutation-equivalent to the
block word. -/
theorem owl_commutation_class (n : ℕ) (w : Word n)
    (h : CommEquiv w (OmissionCanonical.word n)) : OWLFor w :=
  owl_of_commEquiv h.symm (owl_word n)

/-! ### The diagram flip on the actual carrier -/

/-- The global sign of the variable reversal `k ↦ N-1-k`. -/
def eps (n : ℕ) : ℤ := SignedPermutation.epsilon (Fin.revPerm : Equiv.Perm (Fin (n+2)))

/-- The signed variable reversal `x_k ↦ ε x_{N-1-k}`, a ring automorphism. -/
def phi : SkewPolynomial (n+2) ≃+* SkewPolynomial (n+2) :=
  SignedPermutation.skewAction (Fin.revPerm : Equiv.Perm (Fin (n+2)))

theorem eps_sq (n : ℕ) : eps n * eps n = 1 := by
  unfold eps SignedPermutation.epsilon
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Fin.revPerm : Equiv.Perm (Fin (n+2)))) with h | h <;>
    simp [h]

theorem revPerm_mul_self :
    (Fin.revPerm : Equiv.Perm (Fin (n+2))) * Fin.revPerm = 1 := by
  ext i; simp

theorem phi_phi (f : SkewPolynomial (n+2)) : phi (phi f) = f := by
  unfold phi
  rw [← SignedPermutation.action_mul, revPerm_mul_self, SignedPermutation.action_one]

theorem phi_generator (j : Fin (n+2)) : phi (generator j) = eps n • generator j.rev := by
  unfold phi eps
  rw [SignedPermutation.action_generator]
  rfl

theorem rev_castSucc (i : Fin (n+1)) : (i.castSucc).rev = i.rev.succ := by
  apply Fin.ext; simp [Fin.val_rev]; omega

theorem rev_succ (i : Fin (n+1)) : (i.succ).rev = i.rev.castSucc := by
  apply Fin.ext; simp [Fin.val_rev]

theorem rev_eq_castSucc (i : Fin (n+1)) (j : Fin (n+2)) :
    j.rev = i.castSucc ↔ j = i.rev.succ := by
  constructor
  · intro h; rw [← Fin.rev_rev j, h, rev_castSucc]
  · intro h; rw [h, ← rev_castSucc, Fin.rev_rev]

theorem rev_eq_succ (i : Fin (n+1)) (j : Fin (n+2)) :
    j.rev = i.succ ↔ j = i.rev.castSucc := by
  constructor
  · intro h; rw [← Fin.rev_rev j, h, rev_succ]
  · intro h; rw [h, ← rev_succ, Fin.rev_rev]

theorem revPerm_mul_swap (i : Fin (n+1)) :
    (Fin.revPerm : Equiv.Perm (Fin (n+2))) * Equiv.swap i.castSucc i.succ =
      Equiv.swap i.rev.castSucc i.rev.succ * Fin.revPerm := by
  rw [Equiv.mul_swap_eq_swap_mul]
  simp only [Fin.revPerm_apply, rev_castSucc, rev_succ]
  rw [Equiv.swap_comm]

/-- `φ ∘ s_i = s_{n-i} ∘ φ` on the actual signed simple actions. -/
theorem phi_s (i : Fin (n+1)) (f : SkewPolynomial (n+2)) : phi (s i f) = s i.rev (phi f) := by
  unfold phi s
  rw [← SignedPermutation.action_mul, ← SignedPermutation.action_mul, revPerm_mul_swap]

/-- The conjugate `ε • φ ∘ ∂_i ∘ φ`, bundled as a linear map. -/
def conjDivided (i : Fin (n+1)) : SkewPolynomial (n+2) →ₗ[ℤ] SkewPolynomial (n+2) where
  toFun f := eps n • phi (divided i (phi f))
  map_add' f g := by simp only [map_add, smul_add]
  map_smul' c f := by
    simp only [map_zsmul, RingHom.id_apply]
    rw [smul_comm]

/-- `∂_{n-i} ∘ φ = ε • φ ∘ ∂_i`, from the uniqueness of the twisted derivation. -/
theorem phi_divided (i : Fin (n+1)) (f : SkewPolynomial (n+2)) :
    divided i.rev (phi f) = eps n • phi (divided i f) := by
  have hD : conjDivided i = divided i.rev := by
    apply divided_unique
    · show eps n • phi (divided i (phi 1)) = 0
      rw [map_one, divided_one, map_zero, smul_zero]
    · intro j
      show eps n • phi (divided i (phi (generator j))) = _
      rw [phi_generator, map_zsmul, divided_generator, map_zsmul, smul_smul, eps_sq, one_smul]
      have hiff : (j.rev = i.castSucc ∨ j.rev = i.succ) ↔
          (j = i.rev.castSucc ∨ j = i.rev.succ) := by
        rw [rev_eq_castSucc, rev_eq_succ]; exact Or.comm
      by_cases h : j = i.rev.castSucc ∨ j = i.rev.succ
      · rw [if_pos (hiff.mpr h), if_pos h, map_one]
      · rw [if_neg (mt hiff.mp h), if_neg h, map_zero]
    · intro f g
      show eps n • phi (divided i (phi (f*g))) =
        eps n • phi (divided i (phi f)) * g + s i.rev f * (eps n • phi (divided i (phi g)))
      rw [map_mul, divided_mul, map_add, map_mul, map_mul, phi_phi, phi_s, phi_phi, smul_add,
        smul_mul_assoc, mul_smul_comm]
  have := LinearMap.congr_fun hD (phi f)
  rw [← this]
  show eps n • phi (divided i (phi (phi f))) = _
  rw [phi_phi]

theorem phi_kernel {f : SkewPolynomial (n+2)} (hf : f ∈ OddSymmetricKernel.kernelSubring n) :
    phi f ∈ OddSymmetricKernel.kernelSubring n := by
  rw [OddSymmetricKernel.mem_kernelSubring] at hf ⊢
  intro j
  have h := phi_divided j.rev f
  rw [Fin.rev_rev] at h
  rw [h, hf j.rev, map_zero, smul_zero]

/-- The diagram flip on marked words: letters `i ↦ n - i`, marks unchanged. -/
def flipMarked (m : Marked n) : Marked n := m.map (fun a => (a.1.rev, a.2))

theorem flipMarked_flipMarked (m : Marked n) : flipMarked (flipMarked m) = m := by
  simp [flipMarked, Function.comp_def]

theorem erase_flip (m : Marked n) : erase (flipMarked m) = (erase m).map Fin.rev := by
  simp [flipMarked, erase, Function.comp_def]

theorem omission_flip (m : Marked n) : omission (flipMarked m) = (omission m).map Fin.rev := by
  induction m with
  | nil => rfl
  | cons a m ih =>
      rcases a with ⟨i, b⟩
      cases b <;> simp [flipMarked, omission] at ih ⊢ <;> exact ih

theorem map_rev_rev (w : Word n) : (w.map Fin.rev).map Fin.rev = w := by
  simp [Function.comp_def]

/-- The flipped hybrid is a unit multiple of the flipped original. -/
theorem hybrid_flip (m : Marked n) (f : SkewPolynomial (n+2)) :
    ∃ c : ℤ, c * c = 1 ∧ hybrid (flipMarked m) (phi f) = c • phi (hybrid m f) := by
  induction m with
  | nil => exact ⟨1, by norm_num, by simp [flipMarked, hybrid]⟩
  | cons a m ih =>
      obtain ⟨c, hc, h⟩ := ih
      rcases a with ⟨i, b⟩
      cases b
      · refine ⟨c, hc, ?_⟩
        simp only [flipMarked, List.map_cons, hybrid, if_true, if_false,
          Bool.false_eq_true] at h ⊢
        rw [h, map_zsmul, phi_s]
      · refine ⟨c * eps n, ?_, ?_⟩
        · calc c * eps n * (c * eps n) = (c * c) * (eps n * eps n) := by ring
            _ = 1 := by rw [hc, eps_sq, one_mul]
        · simp only [flipMarked, List.map_cons, hybrid, if_true, if_false,
            Bool.false_eq_true] at h ⊢
          rw [h, map_zsmul, phi_divided, smul_smul]

theorem length_reflect (p : Perm n) :
    length (LongestElementary.longest (n+2) * p * LongestElementary.longest (n+2)) =
      length p := by
  have h1 := OddSchubertAction.length_mul_longest (LongestElementary.longest (n+2) * p)
  have h2 := OddSchubertAction.length_longest_mul p
  omega

theorem reduced_reflect (w : Word n) : Reduced (w.map Fin.rev) ↔ Reduced w := by
  unfold Reduced
  rw [OmissionCanonical.permutation_reflect, length_reflect, List.length_map]

theorem trichotomy_flip (m : Marked n) (h : Trichotomy m) : Trichotomy (flipMarked m) := by
  rcases h with hz | ha | hr
  · left
    intro g hg
    obtain ⟨c, -, hc⟩ := hybrid_flip m (phi g)
    rw [phi_phi] at hc
    rw [hc, hz _ (phi_kernel hg), map_zero, smul_zero]
  · right; left
    intro a ha'
    simp only [flipMarked, List.mem_map] at ha'
    obtain ⟨b, hb, rfl⟩ := ha'
    exact ha b hb
  · right; right
    rw [omission_flip, reduced_reflect]
    exact hr

/-- The diagram flip transports the all-markings termwise trichotomy (every rank). -/
theorem owl_flip (w : Word n) (h : OWLFor w) : OWLFor (w.map Fin.rev) := by
  intro m hm
  rw [mem_markings] at hm
  have hm' : flipMarked m ∈ markings w := by
    rw [mem_markings, erase_flip, hm, map_rev_rev]
  have := trichotomy_flip _ (h _ hm')
  rwa [flipMarked_flipMarked] at this

theorem distant_rev {i j : Fin (n+1)} (h : Distant i j) : Distant i.rev j.rev := by
  unfold Distant at *
  simp only [Fin.val_rev]
  have := i.isLt; have := j.isLt
  omega

theorem commStep_flip {u v : Word n} (h : CommStep u v) :
    CommStep (u.map Fin.rev) (v.map Fin.rev) := by
  obtain ⟨p, q, i, j, hd, rfl, rfl⟩ := h
  exact ⟨p.map Fin.rev, q.map Fin.rev, i.rev, j.rev, distant_rev hd, by simp, by simp⟩

theorem commEquiv_flip {u v : Word n} (h : CommEquiv u v) :
    CommEquiv (u.map Fin.rev) (v.map Fin.rev) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail (commStep_flip hs)

/-! ### The proved class -/

/-- The proved OWL class: reduced words commutation-equivalent to the block word
`OmissionCanonical.word n` or to its diagram flip `i ↦ n - i`. -/
def BlockClass (n : ℕ) (w : Word n) : Prop :=
  CommEquiv w (OmissionCanonical.word n) ∨
    CommEquiv w ((OmissionCanonical.word n).map Fin.rev)

theorem owl_blockClass (n : ℕ) (w : Word n) (h : BlockClass n w) : OWLFor w := by
  rcases h with h | h
  · exact owl_commutation_class n w h
  · have h' := commEquiv_flip h
    rw [map_rev_rev] at h'
    have := owl_flip _ (owl_commutation_class n _ h')
    rwa [map_rev_rev] at this

theorem permutation_flip_word (n : ℕ) :
    permutation ((OmissionCanonical.word n).map Fin.rev) = LongestElementary.longest (n+2) := by
  rw [OmissionCanonical.permutation_reflect, OmissionCanonical.word_permutation,
    LongestElementary.longest_involutive, one_mul]

/-- Every word of the class is a reduced expression of the longest element. -/
theorem blockClass_reduced_longest (n : ℕ) (w : Word n) (h : BlockClass n w) :
    Reduced w ∧ permutation w = LongestElementary.longest (n+2) := by
  rcases h with h | h
  · exact ⟨reduced_of_commEquiv h.symm (OmissionCanonical.word_reduced n),
      (permutation_of_commEquiv h).trans (OmissionCanonical.word_permutation n)⟩
  · exact ⟨reduced_of_commEquiv h.symm ((reduced_reflect _).mpr (OmissionCanonical.word_reduced n)),
      (permutation_of_commEquiv h).trans (permutation_flip_word n)⟩

/-- Block-class form of EKL arXiv:1111.1320v1, Lemma 2.18 (p. 15), in its literal termwise
form, for every reduced word commutation-equivalent to the block word or to its diagram
flip: for every marking, either the marked action kills the joint kernel, or no letter
is marked, or the omission word is non-reduced. -/
theorem owl_blockClass_trichotomy (n : ℕ) (w : Word n) (h : BlockClass n w) :
    ∀ m : Marked n, erase m = w → Trichotomy m :=
  fun m hm => owl_blockClass n w h m ((mem_markings m w).mpr hm)

/-- Lemma 2.18, literal termwise form, for the commutation class of the block word. -/
theorem owl_commutation_class_trichotomy (n : ℕ) (w : Word n)
    (h : CommEquiv w (OmissionCanonical.word n)) :
    ∀ m : Marked n, erase m = w → Trichotomy m :=
  owl_blockClass_trichotomy n w (Or.inl h)

/-- Consumer: EKL (2.64) for every word of the class, with no residual hypothesis:
`D_w (f g) = f^{w₀} D_w(g)` for `f` in the joint kernel and arbitrary `g`. -/
theorem left_kernel_blockClass (n : ℕ) (w : Word n) (h : BlockClass n w)
    (f g : SkewPolynomial (n+2)) (hf : f ∈ OddSymmetricKernel.kernelSubring n) :
    LongestDivided.applyWord w (f*g) =
      SignedPermutation.skewAction (LongestElementary.longest (n+2)) f *
        LongestDivided.applyWord w g :=
  longest_left_kernel_of_trichotomy w (blockClass_reduced_longest n w h).2
    (owl_blockClass n w h) f g hf

/-- Consumer: EKL (2.64) for the commutation class of the block word. -/
theorem left_kernel_commutation_class (n : ℕ) (w : Word n)
    (h : CommEquiv w (OmissionCanonical.word n))
    (f g : SkewPolynomial (n+2)) (hf : f ∈ OddSymmetricKernel.kernelSubring n) :
    LongestDivided.applyWord w (f*g) =
      SignedPermutation.skewAction (LongestElementary.longest (n+2)) f *
        LongestDivided.applyWord w g :=
  left_kernel_blockClass n w (Or.inl h) f g hf

/-- Sharpness in rank five: the braid target of `OwlBraid` is a reduced word of the
longest element outside the class (the lemma fails for it). -/
theorem not_blockClass_braid_target : ¬ BlockClass 3 OwlBraid.tgt :=
  fun h => owl_tgt_false (owl_blockClass 3 _ h)

end
end OddMath.Frontier.OwlGeneral
