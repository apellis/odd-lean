import OddMath.Frontier.OwlGeneral

/-! Audit for the general OWL module: every headline restated with the local
definitions unfolded (the class is restated through the inductive `Stage` and the
unfolded commutation move) and no residual hypothesis, plus transitive axioms. -/
namespace OddMath.Frontier.OwlGeneralAudit
open OddMath.SkewPolynomial (SkewPolynomial)
open NilCoxeterWords OmissionWord

/-- The distant commutation move, unfolded. -/
abbrev Move {n : ℕ} (u v : Word n) : Prop :=
  ∃ (p q : Word n) (i j : Fin (n+1)), (i.val+1 < j.val ∨ j.val+1 < i.val) ∧
    u = p ++ i::j::q ∧ v = p ++ j::i::q

/-- Commutation class of the block word, restated: every word commutation-equivalent to the block word satisfies the
literal trichotomy for every marking. -/
example (n : ℕ) (w : Word n)
    (h : Relation.ReflTransGen Move w (OmissionCanonical.word n)) :
    ∀ m : Marked n, erase m = w →
      (∀ f ∈ OddSymmetricKernel.kernelSubring n, hybrid m f = 0) ∨
      (∀ a ∈ m, a.2 = false) ∨ ¬ Reduced (omission m) :=
  OwlGeneral.owl_commutation_class_trichotomy n w h

/-- Main theorem restated: every word commutation-equivalent to a word of the stage
family satisfies the literal trichotomy for every marking. -/
example (n : ℕ) (w : Word n)
    (h : ∃ v : Word n, OwlGeneralStage.Stage n (n+1) v ∧ Relation.ReflTransGen Move w v) :
    ∀ m : Marked n, erase m = w →
      (∀ f ∈ OddSymmetricKernel.kernelSubring n, hybrid m f = 0) ∨
      (∀ a ∈ m, a.2 = false) ∨ ¬ Reduced (omission m) :=
  OwlGeneral.owl_general n w h

/-- The block word and its diagram flip, with their commutation classes, lie in the class. -/
example (n : ℕ) (w : Word n)
    (h : Relation.ReflTransGen Move w (OmissionCanonical.word n) ∨
      Relation.ReflTransGen Move w ((OmissionCanonical.word n).map Fin.rev)) :
    ∀ m : Marked n, erase m = w →
      (∀ f ∈ OddSymmetricKernel.kernelSubring n, hybrid m f = 0) ∨
      (∀ a ∈ m, a.2 = false) ∨ ¬ Reduced (omission m) :=
  OwlGeneral.owl_general n w (OwlGeneral.blockClass_owlClass n w h)

/-- Consumer restated: EKL (2.64) with no OWL hypothesis, for every word of the class. -/
example (n : ℕ) (w : Word n)
    (h : ∃ v : Word n, OwlGeneralStage.Stage n (n+1) v ∧ Relation.ReflTransGen Move w v)
    (f g : SkewPolynomial (n+2)) (hf : ∀ i : Fin (n+1), AllRankDivided.divided i f = 0) :
    LongestDivided.applyWord w (f*g) =
      SignedPermutation.skewAction (LongestElementary.longest (n+2)) f *
        LongestDivided.applyWord w g :=
  OwlGeneral.left_kernel_owl_class n w h f g hf

/-- Class members are reduced expressions of the longest element. -/
example (n : ℕ) (w : Word n)
    (h : ∃ v : Word n, OwlGeneralStage.Stage n (n+1) v ∧ Relation.ReflTransGen Move w v) :
    Reduced w ∧ permutation w = LongestElementary.longest (n+2) :=
  OwlGeneral.owlClass_reduced_longest n w h

/-- The relative block step restated: prepending the descending chain `n, ..., n-r` to any
stage-`r` word with the relative property yields the relative property at stage `r+1`. -/
example (n r : ℕ) (hr : r+1 ≤ n+1) (v : Word n)
    (hpv : permutation v = permutation (OmissionCanonical.blocks n r (by omega)))
    (hv : ∀ m : Marked n, erase m = v → Reduced (omission m) →
      (∀ f, (∀ i : Fin (n+1), n+1-r ≤ i.val → AllRankDivided.divided i f = 0) →
        hybrid m f = 0) ∨ m = allFalse v) :
    ∀ m : Marked n, erase m = OmissionCanonical.down n (n-r) (r+1) (by omega) ++ v →
      Reduced (omission m) →
      (∀ f, (∀ i : Fin (n+1), n+1-(r+1) ≤ i.val → AllRankDivided.divided i f = 0) →
        hybrid m f = 0) ∨
      m = allFalse (OmissionCanonical.down n (n-r) (r+1) (by omega) ++ v) :=
  OwlGeneralStage.relOWL_step hr v hpv hv

/-- Flip transport restated (every rank). -/
example (n : ℕ) (w : Word n) (h : ∀ m ∈ markings w, Trichotomy m) :
    ∀ m ∈ markings (w.map Fin.rev), Trichotomy m :=
  OwlGeneral.owl_flip w h

/-- Operator conjugation laws of the flip, restated. -/
example (n : ℕ) (i : Fin (n+1)) (f : SkewPolynomial (n+2)) :
    AllRankDivided.divided i.rev
        (SignedPermutation.skewAction (Fin.revPerm : Equiv.Perm (Fin (n+2))) f) =
      SignedPermutation.epsilon (Fin.revPerm : Equiv.Perm (Fin (n+2))) •
        SignedPermutation.skewAction (Fin.revPerm : Equiv.Perm (Fin (n+2)))
          (AllRankDivided.divided i f) :=
  OwlGeneral.phi_divided i f

example (n : ℕ) (i : Fin (n+1)) (f : SkewPolynomial (n+2)) :
    SignedPermutation.skewAction (Fin.revPerm : Equiv.Perm (Fin (n+2))) (AllRankDivided.s i f) =
      AllRankDivided.s i.rev
        (SignedPermutation.skewAction (Fin.revPerm : Equiv.Perm (Fin (n+2))) f) :=
  OwlGeneral.phi_s i f

/-- Strictness restated: a rank-five word of the class outside the commutation classes of
the block word and of its flip. -/
example : (∃ v : Word 3, OwlGeneralStage.Stage 3 4 v ∧
      Relation.ReflTransGen Move ([3,2,1,0,1,2,3,1,2,1] : Word 3) v) ∧
    ¬ (Relation.ReflTransGen Move ([3,2,1,0,1,2,3,1,2,1] : Word 3) (OmissionCanonical.word 3) ∨
      Relation.ReflTransGen Move ([3,2,1,0,1,2,3,1,2,1] : Word 3)
        ((OmissionCanonical.word 3).map Fin.rev)) :=
  ⟨OwlGeneral.owlClass_stageExample, OwlGeneral.not_blockClass_stageExample⟩

/-- Sharpness restated: the rank-five braid target is outside the class. -/
example : ¬ ∃ v : Word 3, OwlGeneralStage.Stage 3 4 v ∧
    Relation.ReflTransGen Move OwlBraid.tgt v :=
  OwlGeneral.not_owlClass_braid_target

#print axioms OwlGeneral.owl_general
#print axioms OwlGeneral.owl_class
#print axioms OwlGeneral.left_kernel_owl_class
#print axioms OwlGeneral.owlClass_reduced_longest
#print axioms OwlGeneral.blockClass_owlClass
#print axioms OwlGeneral.owlClass_flip
#print axioms OwlGeneral.owlClass_of_commEquiv
#print axioms OwlGeneral.owlClass_stageExample
#print axioms OwlGeneral.not_blockClass_stageExample
#print axioms OwlGeneral.not_owlClass_braid_target
#print axioms OwlGeneral.owl_commutation_class
#print axioms OwlGeneral.owl_commutation_class_trichotomy
#print axioms OwlGeneral.left_kernel_commutation_class
#print axioms OwlGeneral.owl_flip
#print axioms OwlGeneral.owl_of_commEquiv
#print axioms OwlGeneral.phi_divided
#print axioms OwlGeneral.phi_s
#print axioms OwlGeneral.phi_kernel
#print axioms OwlGeneralStage.relOWL_step
#print axioms OwlGeneralStage.relOWL_flip
#print axioms OwlGeneralStage.psi_divided
#print axioms OwlGeneralStage.psi_relKernel
#print axioms OwlGeneralStage.length_conj_rho
#print axioms OwlGeneralStage.owl_of_stage
#print axioms OwlGeneralStage.permutation_of_stage
#print axioms OwlBraid.owl_commute

end OddMath.Frontier.OwlGeneralAudit
