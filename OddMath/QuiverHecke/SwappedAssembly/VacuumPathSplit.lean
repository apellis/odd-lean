import OddMath.QuiverHecke.SwappedAssembly.VacuumPaths

/-! # Splitting upward paths into the probe vacuum

SwappedVacuumCoordinates §§2, 5–7. An upward summand path from `(0, c_S)` to the
probe vacuum `(0, 0)` through a word `l ++ m ++ r` passes through sectors of probe
content zero at both junctions (`split_three`), and a single upward strand at probe
content zero is a reservoir step (`single_up`). These are the path data consumed by
the dot and crossing layer observations.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly.SPath
open OddMath.SKM
universe u
variable {I X : Type u}

/-- A path through the empty word joins equal sectors. -/
theorem nil_eq {s t : Sector I} (p : SPath ([] : List (Col I X)) s t) : s = t := by
  cases p; rfl

/-- An upward path through `l ++ m ++ r` into the probe vacuum splits into upward
paths at probe content zero. -/
theorem split_three {l m r : List (Col I X)} {cS : I →₀ ℕ}
    (pa : SPath (l ++ m ++ r) (0, cS) (0, 0)) (hw : ∀ c ∈ l ++ m ++ r, c.l.1 = true) :
    ∃ c c' : I →₀ ℕ, Nonempty (SPath l (0, cS) (0, c)) ∧ Nonempty (SPath m (0, c) (0, c')) ∧
      Nonempty (SPath r (0, c') (0, 0)) := by
  obtain ⟨t₂, plm, pr⟩ := split (l ++ m) pa
  obtain ⟨t₁, pl, pm⟩ := split l plm
  have hr : ∀ c ∈ r, c.l.1 = true := fun c hc => hw c (List.mem_append_right _ hc)
  have hm : ∀ c ∈ m, c.l.1 = true := fun c hc =>
    hw c (List.mem_append_left _ (List.mem_append_right _ hc))
  have h₂ : t₂.1 = 0 := le_antisymm (probe_le_of_upward pr hr) zero_le
  have h₁ : t₁.1 = 0 := le_antisymm ((probe_le_of_upward pm hm).trans h₂.le) zero_le
  obtain ⟨a₁, c⟩ := t₁
  obtain ⟨a₂, c'⟩ := t₂
  simp only at h₁ h₂
  subst h₁ h₂
  exact ⟨c, c', ⟨pl⟩, ⟨pm⟩, ⟨pr⟩⟩

/-- A single upward strand at probe content zero ending at probe content zero is a
reservoir step. -/
theorem single_up {col : Col I X} {i : I} (hi : col.l = (true, i)) {c c' : I →₀ ℕ}
    (p : SPath [col] (0, c) (0, c')) :
    StepValid (true, i) false (0, c) ∧ c' = c - Finsupp.single i 1 := by
  obtain ⟨l, w⟩ := col
  simp only at hi
  subst hi
  cases p with
  | cons _ side _ hv q =>
    have he := nil_eq q
    cases side with
    | true =>
      exfalso
      simp only [nextSector, Prod.mk.injEq] at he
      have := congrArg (fun f : I →₀ ℕ => f i) he.1
      simp at this
    | false =>
      simp only [nextSector, Prod.mk.injEq] at he
      exact ⟨hv, he.2.symm⟩

/-- Two upward strands at probe content zero ending at probe content zero are
reservoir steps. -/
theorem two_up {col₁ col₂ : Col I X} {i j : I} (hi : col₁.l = (true, i))
    (hj : col₂.l = (true, j)) {c c' : I →₀ ℕ} (p : SPath [col₁, col₂] (0, c) (0, c')) :
    StepValid (true, i) false (0, c) ∧
      StepValid (true, j) false (nextSector (true, i) false (0, c)) ∧
      c' = c - Finsupp.single i 1 - Finsupp.single j 1 := by
  obtain ⟨l₁, w₁⟩ := col₁
  simp only at hi
  subst hi
  cases p with
  | cons _ side _ hv q =>
    have hup : ∀ d ∈ [col₂], d.l.1 = true := by
      intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      subst hd
      rw [hj]
    have hside : side = false := side_eq_false_of_upward_probe_zero i side q hup rfl
    subst hside
    obtain ⟨hv₂, hc'⟩ := single_up hj (c := c - Finsupp.single i 1) q
    exact ⟨hv, hv₂, hc'⟩

end OddMath.QuiverHecke.SwappedAssembly.SPath
