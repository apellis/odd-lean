import OddMath.QuiverHecke.SwappedAssembly.VacuumPaths

/-! # The occupied reservoir path of an upward word

SwappedActionAssembly §6 and SwappedVacuumCoordinates §2: construct the
all-reservoir path of every upward labelled word at probe content zero.
The initial reservoir content is the word content plus its specified
terminal content. This supplies the path used in the vacuum word corner,
without a path-existence premise or a factor-action hypothesis.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly.SPath
open OddMath.SKM
universe u
variable {I X : Type u}

/-- Formal colour content, before applying any weight-lattice map. -/
def wordContent : List (Col I X) → I →₀ ℕ
  | [] => 0
  | c :: w => Finsupp.single c.l.2 1 + wordContent w

private theorem reservoir_step (i : I) (c : I →₀ ℕ) :
    nextSector (true, i) false (0, Finsupp.single i 1 + c) = (0, c) := by
  simp [nextSector]

private def reservoirCons {w : List (Col I X)} {t : I →₀ ℕ}
    (i : I) (r : X) (c : I →₀ ℕ) (p : SPath w (0, c) (0, t)) :
    SPath (⟨(true, i), r⟩ :: w) (0, Finsupp.single i 1 + c) (0, t) := by
  refine .cons ⟨(true, i), r⟩ false _ ?_ ((reservoir_step i c).symm ▸ p)
  change 1 ≤ (Finsupp.single i 1 + c : I →₀ ℕ) i
  simp only [Finsupp.add_apply, Finsupp.single_eq_same]
  omega

/-- The actual occupied reservoir path, for every upward word and every
terminal reservoir content, including repeated colours. -/
def reservoirPath : (w : List (Col I X)) → (∀ c ∈ w, c.l.1 = true) →
    (c : I →₀ ℕ) → SPath w (0, wordContent w + c) (0, c)
  | [], _, c => by simpa [wordContent] using (SPath.nil (X := X) (0, c))
  | ⟨(false, i), r⟩ :: w, hw, _ => by
      have h := hw ⟨(false, i), r⟩ List.mem_cons_self
      cases h
  | ⟨(true, i), r⟩ :: w, hw, c => by
      simpa only [wordContent, add_assoc] using
        reservoirCons i r (wordContent w + c)
          (reservoirPath w (fun d hd => hw d (List.mem_cons_of_mem _ hd)) c)

end OddMath.QuiverHecke.SwappedAssembly.SPath
