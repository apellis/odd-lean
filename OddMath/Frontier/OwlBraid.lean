import OddMath.Frontier.OmissionCanonical
import OddMath.Frontier.ElementaryRelations
import OddMath.Frontier.DividedDistant

/-! Braid moves and the arbitrary-longest-word OWL of EKL 1111.1320v1.

Carrier: the actual integral skew-polynomial ring with the actual operators
`AllRankDivided.s`, `AllRankDivided.divided`; markings, `hybrid`, `omission` and
`Trichotomy` are exactly `OmissionWord`'s (rightmost letter acts first; a FALSE mark
selects the simple action and is an omission letter).

Positive half (every rank): a single commutation move `i j ↦ j i` (`|i-j| ≥ 2`)
transports the all-markings termwise trichotomy `OWLFor`.

Negative half (rank N = 5, n = 3): starting from the Lean canonical word, two
commutation moves give `src`, which therefore satisfies `OWLFor`; the single braid
move `3 2 3 ↦ 2 3 2` at the left end gives `tgt`, a reduced word of the longest
element on which `OWLFor` FAILS (marking FTTTTTFFFF, kernel input `e₃ e₂`, hybrid
value `-4`).  Hence braid transport of the termwise trichotomy is false, and so is
the statement for all reduced words of the longest element.  No quotient, symmetrizer or
cancellation between markings is used or claimed. -/
namespace OddMath.Frontier.OwlBraid
open OddMath.SkewPolynomial (SkewPolynomial generator)
open AllRankDivided NilCoxeterWords OmissionWord FiniteCompleteElementary PlacticEvaluation
noncomputable section

section General
variable {n : ℕ}

/-- Commuting (distant) letters of the nil-Coxeter word. -/
def Distant (i j : Fin (n+1)) : Prop := i.val+1 < j.val ∨ j.val+1 < i.val

theorem Distant.symm {i j : Fin (n+1)} (h : Distant i j) : Distant j i := Or.symm h

/-- All markings of `w` satisfy the literal termwise trichotomy. -/
def OWLFor (w : Word n) : Prop := ∀ m ∈ markings w, Trichotomy m

theorem hybrid_append (p q : Marked n) (f : SkewPolynomial (n+2)) :
    hybrid (p ++ q) f = hybrid p (hybrid q f) := by
  induction p with
  | nil => rfl
  | cons a p ih => rcases a with ⟨i,b⟩; cases b <;> simp [hybrid, ih]

theorem hybrid_neg (p : Marked n) (f : SkewPolynomial (n+2)) :
    hybrid p (-f) = -hybrid p f := by
  induction p with
  | nil => rfl
  | cons a p ih => rcases a with ⟨i,b⟩; cases b <;> simp [hybrid, ih, map_neg]

theorem omission_append (p q : Marked n) : omission (p ++ q) = omission p ++ omission q := by
  induction p with
  | nil => rfl
  | cons a p ih => rcases a with ⟨i,b⟩; cases b <;> simp [omission, ih]

private theorem distant_ne {i j : Fin (n+1)} (h : Distant i j) :
    i.castSucc ≠ j.castSucc ∧ i.castSucc ≠ j.succ ∧ i.succ ≠ j.castSucc ∧ i.succ ≠ j.succ := by
  unfold Distant at h
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro e <;> have hv := congrArg Fin.val e <;>
    simp only [Fin.coe_castSucc, Fin.val_succ] at hv <;> omega

/-- `divided i ∘ s j = -(s j ∘ divided i)` for distant letters: EKL (2.60) with
disjoint endpoints, on the actual operators. -/
theorem divided_s_distant (i j : Fin (n+1)) (h : Distant i j) (f : SkewPolynomial (n+2)) :
    divided i (s j f) = -s j (divided i f) := by
  obtain ⟨h1, h2, h3, h4⟩ := distant_ne h
  have := NonadjacentDivided.covariance_disjoint i.castSucc i.succ j.castSucc j.succ
    (adjacent_ne i) (adjacent_ne j) h1 h2 h3 h4 f
  rw [NonadjacentDivided.adjacent] at this
  exact this

theorem s_s_distant (i j : Fin (n+1)) (h : Distant i j) (f : SkewPolynomial (n+2)) :
    s i (s j f) = s j (s i f) := by
  obtain ⟨h1, h2, h3, h4⟩ := distant_ne h
  exact NonadjacentDivided.action_disjoint i.castSucc i.succ j.castSucc j.succ h1 h2 h3 h4 f

/-- Two adjacent distant marked letters commute up to a global sign. -/
theorem op_swap (i j : Fin (n+1)) (h : Distant i j) (b c : Bool) (f : SkewPolynomial (n+2)) :
    hybrid [(i,b),(j,c)] f = hybrid [(j,c),(i,b)] f ∨
      hybrid [(i,b),(j,c)] f = -hybrid [(j,c),(i,b)] f := by
  cases b <;> cases c <;> simp only [hybrid, if_true, if_false, Bool.false_eq_true]
  · left; exact s_s_distant i j h f
  · right; rw [divided_s_distant j i h.symm f, neg_neg]
  · right; exact divided_s_distant i j h f
  · right; exact DividedDistant.divided_distant_neg i j h f

theorem hybrid_swap (p q : Marked n) (i j : Fin (n+1)) (h : Distant i j) (b c : Bool)
    (f : SkewPolynomial (n+2)) :
    hybrid (p ++ (i,b)::(j,c)::q) f = hybrid (p ++ (j,c)::(i,b)::q) f ∨
      hybrid (p ++ (i,b)::(j,c)::q) f = -hybrid (p ++ (j,c)::(i,b)::q) f := by
  have e1 : p ++ (i,b)::(j,c)::q = p ++ ([(i,b),(j,c)] ++ q) := rfl
  have e2 : p ++ (j,c)::(i,b)::q = p ++ ([(j,c),(i,b)] ++ q) := rfl
  rw [e1, e2, hybrid_append, hybrid_append, hybrid_append, hybrid_append]
  rcases op_swap i j h b c (hybrid q f) with e | e
  · left; rw [e]
  · right; rw [e, hybrid_neg]

theorem permutation_swap (p q : Word n) (i j : Fin (n+1)) (h : Distant i j) :
    permutation (p ++ i::j::q) = permutation (p ++ j::i::q) := by
  simp only [permutation_append, permutation]
  rw [← mul_assoc (simple i), simple_distant i j h, mul_assoc]

theorem reduced_swap (p q : Word n) (i j : Fin (n+1)) (h : Distant i j)
    (hr : Reduced (p ++ i::j::q)) : Reduced (p ++ j::i::q) := by
  unfold Reduced at *
  rw [← permutation_swap p q i j h, ← hr]
  simp

theorem omission_reduced_swap (p q : Marked n) (i j : Fin (n+1)) (h : Distant i j)
    (b c : Bool) (hr : Reduced (omission (p ++ (i,b)::(j,c)::q))) :
    Reduced (omission (p ++ (j,c)::(i,b)::q)) := by
  rw [omission_append] at hr ⊢
  cases b <;> cases c <;>
    simp only [omission, if_true, if_false, Bool.false_eq_true] at hr ⊢
  · exact reduced_swap _ _ i j h hr
  all_goals exact hr

/-- One commutation move transports the literal trichotomy of a single marking. -/
theorem trichotomy_swap (p q : Marked n) (i j : Fin (n+1)) (h : Distant i j) (b c : Bool)
    (ht : Trichotomy (p ++ (i,b)::(j,c)::q)) : Trichotomy (p ++ (j,c)::(i,b)::q) := by
  rcases ht with hz | ha | hr
  · left
    intro f hf
    rcases hybrid_swap p q i j h b c f with e | e
    · rw [← e]; exact hz f hf
    · have z := hz f hf
      rw [e, neg_eq_zero] at z
      exact z
  · right; left
    intro a ha'
    apply ha
    simp only [List.mem_append, List.mem_cons] at ha' ⊢
    tauto
  · right; right
    intro hr'
    exact hr (omission_reduced_swap p q j i h.symm c b hr')

/-- Commutation moves transport the all-markings termwise trichotomy (every rank). -/
theorem owl_commute (p q : Word n) (i j : Fin (n+1)) (h : Distant i j)
    (hw : OWLFor (p ++ i::j::q)) : OWLFor (p ++ j::i::q) := by
  intro m hm
  rw [mem_markings] at hm
  unfold erase at hm
  obtain ⟨m1, m2, rfl, h1, h2⟩ := List.map_eq_append_iff.mp hm
  obtain ⟨x, m3, rfl, hx, h3⟩ := List.map_eq_cons_iff.mp h2
  obtain ⟨y, r, rfl, hy, h4⟩ := List.map_eq_cons_iff.mp h3
  rcases x with ⟨xj, xb⟩
  rcases y with ⟨yi, yb⟩
  simp only at hx hy
  rw [hx, hy]
  apply trichotomy_swap m1 r i j h yb xb
  apply hw
  rw [mem_markings]
  unfold erase
  simp [h1, h4]

end General

/-! ### The rank-five braid step -/

/-- The Lean canonical word at n = 3 (`OmissionCanonical.word 3`). -/
def canon : Word 3 := [3,2,1,0,3,2,1,3,2,3]
/-- Two commutation moves from `canon`. -/
def src : Word 3 := [3,2,3,1,0,2,1,3,2,3]
/-- One braid move `3 2 3 ↦ 2 3 2` from `src`. -/
def tgt : Word 3 := [2,3,2,1,0,2,1,3,2,3]

theorem canon_eq : OmissionCanonical.word 3 = canon := by decide

theorem owl_canon : OWLFor canon := by
  intro m hm
  rw [← canon_eq] at hm
  exact OmissionCanonical.trichotomy 3 m ((mem_markings m _).mp hm)

theorem d03 : Distant (0 : Fin 4) 3 := by unfold Distant; decide
theorem d13 : Distant (1 : Fin 4) 3 := by unfold Distant; decide

/-- `src` is reached from the canonical word by commutation moves only. -/
theorem owl_src : OWLFor src :=
  owl_commute [3,2] [0,2,1,3,2,3] 1 3 d13
    (owl_commute [3,2,1] [2,1,3,2,3] 0 3 d03 owl_canon)

theorem tgt_reduced : Reduced tgt := by decide
theorem src_reduced : Reduced src := by decide

theorem tgt_longest : permutation tgt = LongestElementary.longest 5 := by
  ext i; fin_cases i <;> rfl

theorem src_longest : permutation src = LongestElementary.longest 5 := by
  ext i; fin_cases i <;> rfl

/-- The witness marking FTTTTTFFFF on `tgt` (left to right). -/
def tm : Marked 3 := [(2,false),(3,true),(2,true),(1,true),(0,true),(2,true),
  (1,false),(3,false),(2,false),(3,false)]

theorem tm_erase : erase tm = tgt := rfl
theorem tm_mem : tm ∈ markings tgt := (mem_markings tm tgt).mpr tm_erase
theorem tm_omission : omission tm = [2,1,3,2,3] := rfl
theorem tm_omission_reduced : Reduced (omission tm) := by decide
theorem tm_not_allFalse : ¬ ∀ a ∈ tm, a.2 = false := by
  intro h
  exact Bool.noConfusion (h (3,true) (by simp [tm]))

def E2 : SkewPolynomial 5 := elementaryPoly 5 2
def E3 : SkewPolynomial 5 := elementaryPoly 5 3

theorem input_kernel : E3 * E2 ∈ OddSymmetricKernel.kernelSubring 3 :=
  Subring.mul_mem _ (OddSymmetricKernel.elementary_mem 3 3)
    (OddSymmetricKernel.elementary_mem 3 2)

theorem E2_eq : E2 =
    tildeGenerator 0 * (tildeGenerator 1 + tildeGenerator 2 + tildeGenerator 3 + tildeGenerator 4)
    + tildeGenerator 1 * (tildeGenerator 2 + tildeGenerator 3 + tildeGenerator 4)
    + tildeGenerator 2 * (tildeGenerator 3 + tildeGenerator 4)
    + tildeGenerator 3 * tildeGenerator 4 := by
  simp [E2, elementaryPoly_eq_strictSum, FiniteWords.strictSum_succ]
  noncomm_ring

theorem E3_eq : E3 =
    tildeGenerator 0 * (tildeGenerator 1 * (tildeGenerator 2 + tildeGenerator 3 + tildeGenerator 4)
      + tildeGenerator 2 * (tildeGenerator 3 + tildeGenerator 4) + tildeGenerator 3 * tildeGenerator 4)
    + tildeGenerator 1 * (tildeGenerator 2 * (tildeGenerator 3 + tildeGenerator 4)
      + tildeGenerator 3 * tildeGenerator 4)
    + tildeGenerator 2 * (tildeGenerator 3 * tildeGenerator 4) := by
  simp [E3, elementaryPoly_eq_strictSum, FiniteWords.strictSum_succ]
  noncomm_ring

/-- The four rightmost FALSE letters of `tm`, in action order s3, s2, s3, s1. -/
def sig (f : SkewPolynomial 5) : SkewPolynomial 5 := s 1 (s 3 (s 2 (s 3 f)))

theorem sig_mul (f g : SkewPolynomial 5) : sig (f * g) = sig f * sig g := by
  simp [sig, map_mul]
theorem sig_add (f g : SkewPolynomial 5) : sig (f + g) = sig f + sig g := by
  simp [sig, map_add]
theorem sig_neg (f : SkewPolynomial 5) : sig (-f) = -sig f := by simp [sig, map_neg]

theorem sig_generator_0 : sig (generator 0) = generator 0 := by
  simp only [sig, s_generator, map_neg, neg_neg]; rfl
theorem sig_generator_1 : sig (generator 1) = generator 2 := by
  simp only [sig, s_generator, map_neg, neg_neg]; rfl
theorem sig_generator_2 : sig (generator 2) = generator 4 := by
  simp only [sig, s_generator, map_neg, neg_neg]; rfl
theorem sig_generator_3 : sig (generator 3) = generator 3 := by
  simp only [sig, s_generator, map_neg, neg_neg]; rfl
theorem sig_generator_4 : sig (generator 4) = generator 1 := by
  simp only [sig, s_generator, map_neg, neg_neg]; rfl

theorem tilde0 : tildeGenerator (0 : Fin 5) = generator 0 := by
  rw [tildeGenerator, show ((0 : Fin 5).val) = 0 from rfl]; norm_num
theorem tilde1 : tildeGenerator (1 : Fin 5) = -generator 1 := by
  rw [tildeGenerator, show ((1 : Fin 5).val) = 1 from rfl]; norm_num
theorem tilde2 : tildeGenerator (2 : Fin 5) = generator 2 := by
  rw [tildeGenerator, show ((2 : Fin 5).val) = 2 from rfl]; norm_num
theorem tilde3 : tildeGenerator (3 : Fin 5) = -generator 3 := by
  rw [tildeGenerator, show ((3 : Fin 5).val) = 3 from rfl]; norm_num
theorem tilde4 : tildeGenerator (4 : Fin 5) = generator 4 := by
  rw [tildeGenerator, show ((4 : Fin 5).val) = 4 from rfl]; norm_num

theorem sig_E3 : sig E3 =
    generator 0 * (-generator 2 * (generator 4 - generator 3 + generator 1)
      + generator 4 * (-generator 3 + generator 1) - generator 3 * generator 1)
    - generator 2 * (generator 4 * (-generator 3 + generator 1) - generator 3 * generator 1)
    + generator 4 * (-generator 3 * generator 1) := by
  rw [E3_eq]
  simp only [tilde0, tilde1, tilde2, tilde3, tilde4, sig_add, sig_neg, sig_mul, sig_generator_0,
    sig_generator_1, sig_generator_2, sig_generator_3, sig_generator_4]
  noncomm_ring

theorem sig_E2 : sig E2 =
    generator 0 * (-generator 2 + generator 4 - generator 3 + generator 1)
    - generator 2 * (generator 4 - generator 3 + generator 1)
    + generator 4 * (-generator 3 + generator 1)
    - generator 3 * generator 1 := by
  rw [E2_eq]
  simp only [tilde0, tilde1, tilde2, tilde3, tilde4, sig_add, sig_neg, sig_mul, sig_generator_0,
    sig_generator_1, sig_generator_2, sig_generator_3, sig_generator_4]
  noncomm_ring

/-! Leibniz chain values (computed by exact arithmetic, re-proved here). A-chains
carry `sig E3` up to its third divided action; B-chains carry two divided actions on
`sig E2`. -/

set_option maxRecDepth 8000

macro "chain_eval" : tactic => `(tactic| (
  simp (config := {decide := true}) only [map_add, map_sub, map_neg, map_mul, divided_mul,
    s_generator, divided_generator, Equiv.swap_apply_def, neg_neg, if_true, if_false,
    zero_mul, one_mul, mul_zero, mul_one, neg_zero, add_zero, zero_add, sub_zero, zero_sub,
    divided_one, map_one, map_zero, neg_mul, mul_neg] <;> norm_num))

theorem A0 : divided (1 : Fin 4) (divided 0 (divided 2 (sig E3))) = 0 := by
  rw [sig_E3]; chain_eval
theorem A1 : divided (2 : Fin 4) (s 1 (divided 0 (divided 2 (sig E3)))) = 0 := by
  rw [sig_E3]; chain_eval
theorem A2 : divided (3 : Fin 4) (s 2 (s 1 (divided 0 (divided 2 (sig E3))))) = 0 := by
  rw [sig_E3]; chain_eval
theorem A3 : divided (2 : Fin 4) (divided 1 (s 0 (divided 2 (sig E3)))) = 0 := by
  rw [sig_E3]; chain_eval
theorem A4 : divided (3 : Fin 4) (s 2 (divided 1 (s 0 (divided 2 (sig E3))))) = 0 := by
  rw [sig_E3]; chain_eval
theorem A5 : divided (3 : Fin 4) (divided 2 (s 1 (s 0 (divided 2 (sig E3))))) = 0 := by
  rw [sig_E3]; chain_eval
theorem A6 : divided (2 : Fin 4) (divided 1 (divided 0 (s 2 (sig E3)))) = (2 : ℤ) • 1 := by
  rw [sig_E3]; chain_eval
theorem A7 : divided (3 : Fin 4) (s 2 (divided 1 (divided 0 (s 2 (sig E3))))) = (2 : ℤ) • 1 := by
  rw [sig_E3]; chain_eval
theorem A8 : divided (3 : Fin 4) (divided 2 (s 1 (divided 0 (s 2 (sig E3))))) = (2 : ℤ) • 1 := by
  rw [sig_E3]; chain_eval
theorem A9 : divided (3 : Fin 4) (divided 2 (divided 1 (s 0 (s 2 (sig E3))))) = 0 := by
  rw [sig_E3]; chain_eval

theorem B0 : divided (1 : Fin 4) (divided 0 (sig E2)) = 0 := by rw [sig_E2]; chain_eval
theorem B1 : divided (2 : Fin 4) (divided 0 (sig E2)) = 0 := by rw [sig_E2]; chain_eval
theorem B2 : divided (3 : Fin 4) (divided 0 (sig E2)) = 0 := by rw [sig_E2]; chain_eval
theorem B3 : divided (2 : Fin 4) (divided 1 (sig E2)) = (2 : ℤ) • 1 := by
  rw [sig_E2]; chain_eval
theorem B4 : divided (3 : Fin 4) (divided 1 (sig E2)) = 0 := by rw [sig_E2]; chain_eval
theorem B5 : divided (0 : Fin 4) (divided 2 (sig E2)) = 0 := by rw [sig_E2]; chain_eval
theorem B6 : divided (1 : Fin 4) (divided 2 (sig E2)) = (-2 : ℤ) • 1 := by
  rw [sig_E2]; chain_eval
theorem B7 : divided (2 : Fin 4) (divided 2 (sig E2)) = 0 := by rw [sig_E2]; chain_eval
theorem B8 : divided (3 : Fin 4) (divided 2 (sig E2)) = 0 := by rw [sig_E2]; chain_eval

theorem hybrid_unfold (F : SkewPolynomial 5) : hybrid tm F =
    s 2 (divided 3 (divided 2 (divided 1 (divided 0 (divided 2 (sig F)))))) := rfl

/-- Kernel-checked witness value on the braid target. -/
theorem hybrid_value : hybrid tm (E3 * E2) = (-4 : ℤ) • 1 := by
  have a0 := A0; have a1 := A1; have a2 := A2; have a3 := A3; have a4 := A4
  have a5 := A5; have a6 := A6; have a7 := A7; have a8 := A8; have a9 := A9
  have b0 := B0; have b1 := B1; have b2 := B2; have b3 := B3; have b4 := B4
  have b5 := B5; have b6 := B6; have b7 := B7; have b8 := B8
  rw [hybrid_unfold, sig_mul]
  generalize sig E3 = A at a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 ⊢
  generalize sig E2 = B at b0 b1 b2 b3 b4 b5 b6 b7 b8 ⊢
  simp only [divided_mul, map_add, map_mul, map_zero, zero_mul, zero_add, add_zero, mul_zero,
    a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, b0, b1, b2, b3, b4, b5, b6, b7, b8,
    map_zsmul, divided_one, map_one, smul_zero]
  simp only [smul_mul_smul_comm, one_mul, map_zsmul, map_one, smul_smul]
  norm_num

theorem neg_four_ne_zero : ((-4 : ℤ) • (1 : SkewPolynomial 5)) ≠ 0 := by
  intro h
  have h0 := congrArg (fun p : SkewPolynomial 5 => p 0) h
  have h1 : (1 : SkewPolynomial 5) 0 = 1 := by
    show (Finsupp.single (0 : Fin 5 → ℕ) (1 : ℤ)) 0 = 1
    exact Finsupp.single_eq_same
  simp only [Finsupp.smul_apply, Finsupp.coe_zero, Pi.zero_apply, h1] at h0
  norm_num at h0

theorem tm_not_trichotomy : ¬ Trichotomy tm := by
  rintro (hz | ha | hr)
  · exact neg_four_ne_zero (hybrid_value.symm.trans (hz _ input_kernel))
  · exact tm_not_allFalse ha
  · exact hr tm_omission_reduced

theorem owl_tgt_false : ¬ OWLFor tgt := fun h => tm_not_trichotomy (h tm tm_mem)

/-- The braid step itself: `src = 3 2 3 · r`, `tgt = 2 3 2 · r`. -/
theorem src_braid : src = [] ++ (3 : Fin 4) :: 2 :: 3 :: [1,0,2,1,3,2,3] := rfl
theorem tgt_braid : tgt = [] ++ (2 : Fin 4) :: 3 :: 2 :: [1,0,2,1,3,2,3] := rfl

/-- A single braid move need not transport the all-markings
termwise trichotomy, even between reduced words of the longest element, from a word
that is commutation-equivalent to the Lean canonical word. -/
theorem braid_transport_false :
    ¬ ∀ (p q : Word 3) (i j : Fin 4), (i.val = j.val+1 ∨ j.val = i.val+1) →
      OWLFor (p ++ i::j::i::q) → OWLFor (p ++ j::i::j::q) := by
  intro h
  exact owl_tgt_false (h [] [1,0,2,1,3,2,3] 3 2 (Or.inl rfl) owl_src)

/-- Consequence: OWL for every reduced word of the longest element is false at N = 5. -/
theorem t2_false :
    ¬ ∀ w : Word 3, Reduced w → permutation w = LongestElementary.longest 5 → OWLFor w :=
  fun h => owl_tgt_false (h tgt tgt_reduced tgt_longest)

/-- The source word of the failing braid move does satisfy OWL (both ends reduced longest). -/
theorem braid_step_summary :
    Reduced src ∧ permutation src = LongestElementary.longest 5 ∧ OWLFor src ∧
    Reduced tgt ∧ permutation tgt = LongestElementary.longest 5 ∧ ¬ OWLFor tgt :=
  ⟨src_reduced, src_longest, owl_src, tgt_reduced, tgt_longest, owl_tgt_false⟩

/-- OWL for every reduced word of the longest element is false
(witness at n = 3 on `tgt ≠ OmissionCanonical.word 3`). -/
theorem owl_trichotomy_false :
    ¬ ∀ (n : Nat) (w : NilCoxeterWords.Word n) (_hw : NilCoxeterWords.Reduced w)
        (_hp : NilCoxeterWords.permutation w = LongestElementary.longest (n+2))
        (m : OmissionWord.Marked n) (_hm : OmissionWord.erase m = w), OmissionWord.Trichotomy m :=
  fun h => tm_not_trichotomy (h 3 tgt tgt_reduced tgt_longest tm tm_erase)

theorem tgt_ne_canonical : tgt ≠ OmissionCanonical.word 3 := by rw [canon_eq]; decide

end
end OddMath.Frontier.OwlBraid
