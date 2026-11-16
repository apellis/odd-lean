import OddMath.QuiverHecke.SwappedAssembly.Sectors

/-! # Upward summand paths at the probe vacuum

SwappedActionAssembly §6 and SwappedVacuumCoordinates §2: an upward path
ending at probe content zero can use only the reservoir summand. Hence
there is at most one path between its given sectors. This is the path
uniqueness used to collapse the middle-path sum in the vacuum corner of
the swapped layer action; it makes no assumption about a factor action.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedAssembly.SPath
open OddMath.SKM
universe u
variable {I X : Type u}

/-- Upward strands can only increase the probe content along a path. -/
theorem probe_le_of_upward {w : List (Col I X)} {s t : Sector I}
    (p : SPath w s t) (hw : ∀ c ∈ w, c.l.1 = true) : s.1 ≤ t.1 := by
  induction p with
  | nil s => exact le_rfl
  | cons c side s hv p ih =>
    have hc := hw c List.mem_cons_self
    have hp := ih (fun d hd => hw d (List.mem_cons_of_mem _ hd))
    rcases c with ⟨⟨b, i⟩, r⟩
    cases b with
    | false => cases hc
    | true =>
      cases side with
      | false => exact hp
      | true =>
        exact (le_add_of_nonneg_right (show 0 ≤ Finsupp.single i 1 from zero_le)).trans hp

/-- At probe content zero the first upward strand must use the reservoir. -/
theorem side_eq_false_of_upward_probe_zero {w : List (Col I X)}
    {s t : Sector I} (i : I) (side : Bool)
    (p : SPath w (nextSector (true, i) side s) t)
    (hw : ∀ c ∈ w, c.l.1 = true) (ht : t.1 = 0) : side = false := by
  cases side with
  | false => rfl
  | true =>
    have hi : s.1 i + 1 ≤ 0 := by
      simpa [nextSector, ht] using (probe_le_of_upward p hw i)
    omega

/-- Every upward path into the probe vacuum is the same reservoir path,
including repeated colours and arbitrary external weight labels. -/
theorem subsingleton_of_upward_probe_zero {w : List (Col I X)} {s t : Sector I}
    (hw : ∀ c ∈ w, c.l.1 = true) (ht : t.1 = 0) :
    Subsingleton (SPath w s t) := by
  induction w generalizing s with
  | nil => infer_instance
  | cons c w ih =>
    constructor
    intro p q
    cases p with
    | cons c side s hv p =>
      cases q with
      | cons c side' s hv' q =>
        have hc := hw c List.mem_cons_self
        have hw' : ∀ d ∈ w, d.l.1 = true :=
          fun d hd => hw d (List.mem_cons_of_mem _ hd)
        rcases c with ⟨⟨b, i⟩, r⟩
        cases b with
        | false => cases hc
        | true =>
          have hs := side_eq_false_of_upward_probe_zero i side p hw' ht
          have hs' := side_eq_false_of_upward_probe_zero i side' q hw' ht
          subst side
          subst side'
          have hpq := (ih hw').elim p q
          cases hpq
          rfl

/-- The finite middle-path sum at an occupied probe-vacuum corner has one
term, for arbitrary coefficient values. -/
theorem sum_of_upward_probe_zero {w : List (Col I X)} {s t : Sector I}
    (hw : ∀ c ∈ w, c.l.1 = true) (ht : t.1 = 0)
    {A : Type*} [AddCommMonoid A] [Fintype (SPath w s t)]
    (f : SPath w s t → A) (p : SPath w s t) : ∑ q, f q = f p := by
  let := subsingleton_of_upward_probe_zero (s := s) hw ht
  exact Fintype.sum_subsingleton f p

end OddMath.QuiverHecke.SwappedAssembly.SPath
