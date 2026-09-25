import OddMath.Frontier.NilCoxeterWords
import OddMath.Frontier.IntervalAnnihilation

/-! Literal EKL1111.1320v1 (2.58) marking expansion. Rightmost acts first;
false marks select simple actions and are precisely the omission letters.
The arbitrary-longest-word OWL is a separate obligation, not an assumption
hidden in this expansion. -/
namespace OddMath.Frontier.OmissionWord
open OddMath.SkewPolynomial (SkewPolynomial)
open NilCoxeterWords LongestDivided AllRankDivided
noncomputable section

abbrev Marked (n : ℕ) := List (Fin (n+1) × Bool)

def erase {n : ℕ} (m : Marked n) : Word n := m.map Prod.fst

def omission {n : ℕ} : Marked n → Word n
  | [] => []
  | (i,b)::m => if b then omission m else i::omission m

def hybrid {n : ℕ} : Marked n → SkewPolynomial (n+2) → SkewPolynomial (n+2)
  | [], f => f
  | (i,b)::m, f => if b then divided i (hybrid m f) else s i (hybrid m f)

/-- A literal exhaustive enumeration of independent markings, without quotients. -/
def markings {n : ℕ} : Word n → List (Marked n)
  | [] => [[]]
  | i::w => (markings w).map (List.cons (i,true)) ++
      (markings w).map (List.cons (i,false))

@[simp] theorem erase_nil {n : ℕ} : erase ([] : Marked n) = [] := rfl
@[simp] theorem erase_cons {n : ℕ} (i : Fin (n+1)) (b : Bool) (m : Marked n) :
    erase ((i,b)::m) = i::erase m := rfl

/-- Exactly the marked lists with this underlying word occur in the sum. -/
theorem mem_markings {n : ℕ} (m : Marked n) (w : Word n) :
    m ∈ markings w ↔ erase m = w := by
  induction w generalizing m with
  | nil => simp [markings, erase]
  | cons i w ih =>
      cases m with
      | nil => simp [markings, erase]
      | cons a m =>
          rcases a with ⟨j,b⟩
          cases b <;> simp [markings, erase, ih, List.mem_map, and_assoc, and_comm, eq_comm]

theorem markings_length {n : ℕ} (w : Word n) : (markings w).length = 2^w.length := by
  induction w with
  | nil => simp [markings]
  | cons i w ih => simp [markings, ih, pow_succ, Nat.mul_two]

theorem markings_nodup {n : ℕ} (w : Word n) : (markings w).Nodup := by
  induction w with
  | nil => simp [markings]
  | cons i w ih =>
      rw [markings, List.nodup_append]
      refine ⟨ih.map (fun _ _ h => (List.cons.inj h).2), ih.map (fun _ _ h => (List.cons.inj h).2), ?_⟩
      intro a ha hb
      simp only [List.mem_map] at ha hb
      obtain ⟨x, _, rfl⟩ := ha
      obtain ⟨y, _, h⟩ := hb
      simp at h

/-- Full generalized Leibniz, with every marking and the printed factor order. -/
theorem generalized_leibniz {n : ℕ} (w : Word n) (f g : SkewPolynomial (n+2)) :
    applyWord w (f*g) = ((markings w).map
      (fun m => hybrid m f * applyWord (omission m) g)).sum := by
  induction w with
  | nil => simp [markings, hybrid, omission]
  | cons i w ih =>
      rw [applyWord_cons, ih]
      simp only [markings, List.map_append, List.sum_append, List.map_map,
        Function.comp_def, hybrid, omission, Bool.true_eq, if_true, Bool.false_eq_true,
        if_false, applyWord_cons]
      induction markings w with
      | nil => simp
      | cons m ms ihs =>
          simp only [List.map_cons, List.sum_cons, map_add, divided_mul]
          rw [ihs]
          abel

@[simp] theorem hybrid_zero {n : ℕ} (m : Marked n) : hybrid m 0 = 0 := by
  induction m with
  | nil => rfl
  | cons a m ih => rcases a with ⟨i,b⟩; cases b <;> simp [hybrid, ih]

/-- Literal source trichotomy; declaring this predicate does NOT prove it. -/
def Trichotomy {n : ℕ} (m : Marked n) : Prop :=
  (∀ f ∈ OddSymmetricKernel.kernelSubring n, hybrid m f = 0) ∨
  (∀ a ∈ m, a.2 = false) ∨ ¬Reduced (omission m)

/-- The unique marking with no divided action on the left factor. -/
def allFalse {n : ℕ} (w : Word n) : Marked n := w.map (fun i => (i,false))

@[simp] theorem erase_allFalse {n : ℕ} (w : Word n) : erase (allFalse w) = w := by
  simp [erase, allFalse, Function.comp_def]

@[simp] theorem omission_allFalse {n : ℕ} (w : Word n) : omission (allFalse w) = w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
      change i :: omission (allFalse w) = i :: w
      rw [ih]

theorem hybrid_allFalse {n : ℕ} (w : Word n) (f : SkewPolynomial (n+2)) :
    hybrid (allFalse w) f = SignedPermutation.skewAction (permutation w) f := by
  induction w with
  | nil => simp [allFalse, hybrid, permutation]
  | cons i w ih =>
      simp only [allFalse, List.map_cons, hybrid, Bool.false_eq_true, if_false,
        permutation, SignedPermutation.action_mul]
      rw [show hybrid (List.map (fun i => (i,false)) w) f =
        SignedPermutation.skewAction (permutation w) f from ih]
      rfl

theorem all_false_iff {n : ℕ} (m : Marked n) :
    (∀ a ∈ m, a.2 = false) ↔ m = allFalse (erase m) := by
  induction m with
  | nil => simp [allFalse, erase]
  | cons a m ih =>
      rcases a with ⟨i,b⟩
      rw [List.forall_mem_cons]
      change (b = false ∧ ∀ a ∈ m, a.2 = false) ↔
        (i,b)::m = (i,false)::allFalse (erase m)
      simp only [List.cons.injEq, Prod.mk.injEq, true_and, ← ih]

/-- Each nonexceptional term vanishes; no cancellation or symmetrizer is used. -/
theorem term_zero_of_trichotomy {n : ℕ} (m : Marked n) (h : Trichotomy m)
    (hne : m ≠ allFalse (erase m)) (f g : SkewPolynomial (n+2))
    (hf : f ∈ OddSymmetricKernel.kernelSubring n) :
    hybrid m f * applyWord (omission m) g = 0 := by
  rcases h with hz | ha | hr
  · rw [hz f hf, zero_mul]
  · exact (hne ((all_false_iff m).mp ha)).elim
  · rw [nonreduced_operator_zero _ hr]
    simp

/-- CONDITIONAL consumer: the explicit hypothesis is exactly the missing OWL.
This is not a proof of OWL or an unconditional proof of source (2.64). -/
theorem left_kernel_of_trichotomy {n : ℕ} (w : Word n)
    (hOWL : ∀ m ∈ markings w, Trichotomy m)
    (f g : SkewPolynomial (n+2)) (hf : f ∈ OddSymmetricKernel.kernelSubring n) :
    applyWord w (f*g) = SignedPermutation.skewAction (permutation w) f * applyWord w g := by
  classical
  rw [generalized_leibniz, ← List.sum_toFinset _ (markings_nodup w)]
  rw [Finset.sum_eq_single_of_mem (allFalse w)]
  · rw [hybrid_allFalse, omission_allFalse]
  · simp [mem_markings]
  · intro m hm hne
    have hm' := List.mem_toFinset.mp hm
    apply term_zero_of_trichotomy m (hOWL m hm') _ f g hf
    rwa [(mem_markings m w).mp hm']

/-- Source (2.64) for a longest word, still explicitly CONDITIONAL on OWL. -/
theorem longest_left_kernel_of_trichotomy {n : ℕ} (w : Word n)
    (hp : permutation w = LongestElementary.longest (n+2))
    (hOWL : ∀ m ∈ markings w, Trichotomy m)
    (f g : SkewPolynomial (n+2)) (hf : f ∈ OddSymmetricKernel.kernelSubring n) :
    applyWord w (f*g) =
      SignedPermutation.skewAction (LongestElementary.longest (n+2)) f * applyWord w g := by
  rw [left_kernel_of_trichotomy w hOWL f g hf, hp]

end
end OddMath.Frontier.OmissionWord
