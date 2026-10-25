import OddMath.SKM.PointedMatching

/-! Build genuine complete choices from indexed pointed representatives. -/
noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
universe u v
variable {I : Type u} {a b : List (Letter I)}

namespace PointedMatching

def serializeAs (F : PointedMatching a b) {R : List (TMove (Letter I))}
    (h : F.moves = R) (n : MatchingStrand a R → ℕ) : List (DTMove I) := by
  subst R
  exact F.serialize n

theorem serializeAs_decorates (F : PointedMatching a b) {R : List (TMove (Letter I))}
    (h : F.moves = R) (n : MatchingStrand a R → ℕ) :
    Decorates₂ a R F.points (strandCounts n) (F.serializeAs h n) := by
  subst R
  exact F.decorates n
end PointedMatching

namespace IndexedMatchingChoice
variable {J : Type v} (D : J → PointedMatching a b)
  (hu : ∀ i j, Iso (pairing₂ a (D i).moves) (pairing₂ a (D j).moves) → i = j)
  (hc : ∀ R, IsMatching₂ a b R → StrictReduced₂ a R →
    ∃ j, Iso (pairing₂ a (D j).moves) (pairing₂ a R))

include hu in
theorem moves_injective : Function.Injective (fun j => (D j).moves) := by
  intro i j h
  apply hu i j
  change (D i).moves = (D j).moves at h
  rw [h]
  exact Iso.refl _

def indexEquiv : J ≃ Set.range (fun j => (D j).moves) :=
  _root_.Equiv.ofInjective _ (moves_injective D hu)

def picked (R : Set.range (fun j => (D j).moves)) : PointedMatching a b :=
  D ((indexEquiv D hu).symm R)

 theorem picked_moves (R : Set.range (fun j => (D j).moves)) : (picked D hu R).moves = R.val :=
  congrArg Subtype.val ((indexEquiv D hu).apply_symm_apply R)

@[simp] theorem picked_index (j : J) : picked D hu (indexEquiv D hu j) = D j := by
  simp only [picked, Equiv.symm_apply_apply]

def choice : MatchingBasisChoice a b where
  members := Set.range (fun j => (D j).moves)
  matching R hR := by
    have h := picked_moves D hu ⟨R, hR⟩
    change (picked D hu ⟨R, hR⟩).moves = R at h
    rw [← h]
    exact ⟨(picked D hu ⟨R, hR⟩).matching, (picked D hu ⟨R, hR⟩).strict⟩
  unique R hR S hS hi := by
    obtain ⟨i, rfl⟩ := hR
    obtain ⟨j, rfl⟩ := hS
    exact congrArg (fun j => (D j).moves) (hu i j hi)
  complete R hR hr := by
    obtain ⟨j, hj⟩ := hc R hR hr
    exact ⟨(D j).moves, ⟨j, rfl⟩, hj⟩
  points R := (picked D hu R).points
  onStrand R j hj := by
    have h := picked_moves D hu R
    rw [← h] at hj ⊢
    exact (picked D hu R).onStrand j hj
  serialize R := (picked D hu R).serializeAs (picked_moves D hu R)
  decorates R n := (picked D hu R).serializeAs_decorates (picked_moves D hu R) n

/-- The constructed choice's labels are the indexed representatives' actual
strand multiplicities, without a chosen permutation of dot positions. -/
def labelsEquiv : (Σ j : J, MatchingStrand a (D j).moves → ℕ) ≃ (choice D hu hc).Labels :=
  _root_.Equiv.sigmaCongr (indexEquiv D hu) (fun _ => _root_.Equiv.refl _)

 theorem layers_labelsEquiv (j : J) (n : MatchingStrand a (D j).moves → ℕ) :
    (choice D hu hc).layers (labelsEquiv D hu hc ⟨j, n⟩) = (D j).layers n := by
  change dLay a ((picked D hu (indexEquiv D hu j)).serializeAs _ _) = _
  simp only [picked_index]
  rfl

end IndexedMatchingChoice
end OddMath.SKM
