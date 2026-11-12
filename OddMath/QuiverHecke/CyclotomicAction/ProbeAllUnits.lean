import OddMath.QuiverHecke.CyclotomicAction.ProbeMixedCornerRelations
import OddMath.QuiverHecke.CyclotomicAction.ProbeUnitPropagation

/-! # All-position units in the actual cofinal probe

Induction over positions uses both source and swapped word corners. Equal
colours use direct nilHecke units; distinct colours use the actual signed
slides and both Q remainders. The proof works over the original ground ring,
without finite-dimensionality, residue fields, or Nakayama descent.

The hypothesis `[Fact Sc.PureNilpotent]` on declarations here is a route-only intermediate
hypothesis for parameters with pure terms: homogeneous parameters supply it
(`ScalarData.NoPure.pureNilpotent`) and truncated Rees parameters satisfy it
(`BWWReesParameters.truncated_pureNilpotent`).
-/
noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
  {k : Type w} [CommRing k] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  [Fintype I]

omit [Fintype I] in
private theorem probeWord_split_two {n : ℕ} (s : Word I (n+1))
    (r : ℕ) (hr : r+1 < n+1) :
    ∃ (pre : List I) (i j : I) (post : List I),
      pre.length = r ∧ s.val = pre ++ [i,j] ++ post := by
  have hdrop : 2 ≤ (s.val.drop r).length := by
    rw [List.length_drop, s.property]
    omega
  cases hd : s.val.drop r with
  | nil => simp [hd] at hdrop
  | cons i rest =>
    cases ht : rest with
    | nil => simp [hd, ht] at hdrop
    | cons j post =>
      refine ⟨s.val.take r, i, j, post, ?_, ?_⟩
      · rw [List.length_take, s.property, Nat.min_eq_left (by omega)]
      · have hs := List.take_append_drop r s.val
        rw [hd, ht] at hs
        simpa only [List.cons_append, List.nil_append, List.append_assoc] using hs.symm

/-- Every literal dot in every word corner of the prescribed cofinal probe
is a unit, directly over the given commutative ground ring. -/
theorem probeWord_dots_isUnit [Fact Sc.PureNilpotent] (m : I → ℕ) (n : ℕ) :
    ∀ r < n+1, ∀ s : Word I (n+1),
      IsUnit (cyclotomicWordEnd D Sc (probePolynomial (probeDotExponent D) m) s
        (dotE D Sc s.val r)) := by
  intro r
  induction r with
  | zero =>
    intro _ s
    exact probe_firstDot_isUnit D Sc m s
  | succ r ih =>
    intro hr s
    obtain ⟨pre, i, j, post, hpre, hs⟩ := probeWord_split_two s r hr
    have hn : n = pre.length + post.length + 1 := by
      have hlen := congrArg List.length hs
      rw [s.property] at hlen
      simp only [List.length_append, List.length_cons, List.length_nil] at hlen
      omega
    subst n
    have hsword : s = probeMixedWord pre post i j := Subtype.ext hs
    subst s
    have hsrc := ih (by omega) (probeMixedWord pre post i j)
    have htgt := ih (by omega) (probeMixedWord pre post j i)
    rw [← hpre] at hsrc htgt ⊢
    by_cases hij : i = j
    · subst j
      exact cyclotomicBlock_dot_isUnit D Sc (probePolynomial (probeDotExponent D) m)
        pre post i hsrc
    · exact probeMixedCorner_dot_isUnit D Sc (probePolynomial (probeDotExponent D) m)
        pre post i j hij hsrc htgt

end OddMath.QuiverHecke
