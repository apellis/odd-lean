import OddMath.SKM.Nondegeneracy
import OddMath.SKM.PositiveMatchingDots
import Mathlib.Data.List.Sort

/-! # Sorted bottom-dot serializers for upward matching choices -/
noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord DTMove
open scoped Classical
variable {I : Type*} {a b : List (Letter I)}
namespace MatchingBasisChoice

def bottomPositions (F : MatchingBasisChoice a b) (R : F.members)
    (n : MatchingStrand a R.val → ℕ) : List ℕ :=
  ((leftEnds₂ a R.val).flatMap fun j =>
    List.replicate (strandCounts n j) (a.length - 1 - j)).mergeSort (· ≤ ·)

theorem bottomPositions_pairwise (F : MatchingBasisChoice a b) (R : F.members) (n) :
    (F.bottomPositions R n).Pairwise (· ≤ ·) :=
  List.pairwise_mergeSort' _ _

theorem bottomPositions_bound (F : MatchingBasisChoice a b)
    (hbottom : ∀ R : F.members, ∀ j ∈ leftEnds₂ a R.val, j < a.length)
    (R : F.members) (n) : ∀ p ∈ F.bottomPositions R n, p < a.length := by
  intro p hp
  have hp' := (List.mergeSort_perm _ _).mem_iff.mp hp
  obtain ⟨j, hj, hpj⟩ := List.mem_flatMap.mp hp'
  have he := List.eq_of_mem_replicate hpj
  have := hbottom R j hj
  omega

private theorem count_flatMap_replicate {α β : Type*} [BEq β] [LawfulBEq β]
    (s : List α) (hs : s.Nodup) (q : α → β) (n : α → ℕ)
    (hq : ∀ x ∈ s, ∀ y ∈ s, q x = q y → x = y) {j : α} (hj : j ∈ s) :
    (s.flatMap fun x => List.replicate (n x) (q x)).count (q j) = n j := by
  induction s with
  | nil => simp at hj
  | cons x s ih =>
    obtain ⟨hx, hs⟩ := List.nodup_cons.mp hs
    rcases List.mem_cons.mp hj with rfl | hj
    · have hz : (s.flatMap fun y => List.replicate (n y) (q y)).count (q j) = 0 := by
        apply List.count_eq_zero.mpr
        intro hm
        obtain ⟨y, hy, hyq⟩ := List.mem_flatMap.mp hm
        have hxy := hq j List.mem_cons_self y (List.mem_cons_of_mem _ hy)
          (List.eq_of_mem_replicate hyq)
        exact hx (hxy ▸ hy)
      simp [hz]
    · have hne : q j ≠ q x := by
        intro he
        have := hq j (List.mem_cons_of_mem _ hj) x List.mem_cons_self he
        exact hx (this ▸ hj)
      have hi := ih hs (fun y hy z hz => hq y (List.mem_cons_of_mem _ hy)
        z (List.mem_cons_of_mem _ hz)) hj
      simp [List.count_replicate, Ne.symm hne, hi]

theorem bottomPositions_count (F : MatchingBasisChoice a b)
    (hbottom : ∀ R : F.members, ∀ j ∈ leftEnds₂ a R.val, j < a.length)
    (R : F.members) (n) (j : MatchingStrand a R.val) :
    (F.bottomPositions R n).count (a.length - 1 - j.val) = n j := by
  unfold bottomPositions
  rw [(List.mergeSort_perm _ _).count_eq]
  have hq : ∀ x ∈ leftEnds₂ a R.val, ∀ y ∈ leftEnds₂ a R.val,
      a.length - 1 - x = a.length - 1 - y → x = y := by
    intro x hx y hy hxy
    have := hbottom R x hx
    have := hbottom R y hy
    omega
  simpa only [strandCounts_apply] using count_flatMap_replicate
    (leftEnds₂ a R.val) (nodup_leftEnds₂ a R.val) (fun x => a.length - 1 - x)
    (strandCounts n) hq j.property

theorem bottomPositions_injective (F : MatchingBasisChoice a b)
    (hbottom : ∀ R : F.members, ∀ j ∈ leftEnds₂ a R.val, j < a.length) (R : F.members) :
    Function.Injective (F.bottomPositions R) := by
  intro n m he
  funext j
  have hc := congrArg (fun l : List ℕ => l.count (a.length - 1 - j.val)) he
  simpa only [F.bottomPositions_count hbottom] using hc

private theorem dotPts_bottom (js : List ℕ) (R : List (TMove (Letter I))) :
    dotPts (js.map .dt ++ R.map .tm) = js.map (fun j => (0, j)) := by
  induction js with
  | nil =>
    induction R with
    | nil => rfl
    | cons m R ih => simpa [dotPts] using ih
  | cons j js ih => simpa [dotPts] using congrArg ((0, j) :: ·) ih

private theorem tmoves_bottom (js : List ℕ) (R : List (TMove (Letter I))) :
    tmoves (js.map .dt ++ R.map .tm) = R := by
  induction js with
  | nil => simp
  | cons j js ih => simpa [tmoves] using ih

/-- Same matching representatives, with all dots sorted at their bottom endpoints. -/
def atBottomSorted (F : MatchingBasisChoice a b)
    (hbottom : ∀ R : F.members, ∀ j ∈ leftEnds₂ a R.val, j < a.length) : MatchingBasisChoice a b where
  members := F.members
  matching := F.matching
  unique := F.unique
  complete := F.complete
  points _ j := (0, a.length - 1 - j)
  onStrand R j hj := onStrand₂_bottom (F.matching R.val R.property).1 (hbottom R j hj)
  serialize R n := (F.bottomPositions R n).map .dt ++ R.val.map .tm
  decorates R n := by
    constructor
    · exact tmoves_bottom _ _
    · rw [dotPts_bottom]
      have hp := (List.mergeSort_perm
        ((leftEnds₂ a R.val).flatMap fun j => List.replicate (strandCounts n j) (a.length - 1 - j))
        (· ≤ ·)).map (fun j => (0, j))
      simpa only [bottomPositions, List.map_flatMap, List.map_replicate] using hp

/-- Every literal upward boundary satisfies the bottom-endpoint condition;
the serializer construction therefore has no additional geometric premise. -/
theorem positive_bottom_bound (s t : List I)
    (F : MatchingBasisChoice (s.map up) (t.map up))
    (R : F.members) (j : ℕ) (hj : j ∈ leftEnds₂ (s.map up) R.val) : j < (s.map up).length := by
  have hs : (List.ofFn fun r : Fin s.length => (true, s.get r)) = s.map up := by
    simpa only [List.map_ofFn, Function.comp_def, up] using
      congrArg (List.map (fun i : I => (true, i))) (List.ofFn_get s)
  have ht : (List.ofFn fun r : Fin t.length => (true, t.get r)) = t.map up := by
    simpa only [List.map_ofFn, Function.comp_def, up] using
      congrArg (List.map (fun i : I => (true, i))) (List.ofFn_get t)
  have hm : IsMatching₂ (List.ofFn fun r : Fin s.length => (true, s.get r))
      (List.ofFn fun r : Fin t.length => (true, t.get r)) R.val := by
    simpa only [hs, ht] using (F.matching R.val R.property).1
  have h := (positive_mem_leftEnds₂ s.get t.get hm j).mp (by simpa only [hs] using hj)
  simpa only [List.length_map] using h

def atBottomSortedUp (s t : List I) (F : MatchingBasisChoice (s.map up) (t.map up)) :
    MatchingBasisChoice (s.map up) (t.map up) :=
  F.atBottomSorted (F.positive_bottom_bound s t)

end MatchingBasisChoice
end OddMath.SKM
