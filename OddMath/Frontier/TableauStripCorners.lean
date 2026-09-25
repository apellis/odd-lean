import OddMath.Frontier.TableauCorner

/-!
Geometric prerequisite for Fulton, Young Tableaux §1.1, printed p11 / PDF23:
a horizontal skew shape can be removed from right to left. English zero-based
coordinates. This does not remove tableau entries or prove a word inverse.
-/
namespace OddMath.Frontier.TableauStripCorners

-- Definitions copied unchanged from the frozen admission contract.
def Horizontal (μ ν : YoungDiagram) : Prop :=
  μ.cells ⊆ ν.cells ∧
    (∀ p ∈ ν.cells \ μ.cells, ∀ q ∈ ν.cells \ μ.cells, p.2 = q.2 → p = q)
def PeelsTo (μ : YoungDiagram) : YoungDiagram → List (ℕ × ℕ) → Prop
  | ν, [] => ν = μ
  | ν, p :: ps => ∃ hp : TableauCorner.IsCorner ν p,
      PeelsTo μ (TableauCorner.eraseShape ν p hp) ps

/-- A rightmost actual skew cell is an outside corner of the outer shape. -/
theorem rightmost_corner (μ ν : YoungDiagram) (p : ℕ × ℕ)
    (h : Horizontal μ ν) (hp : p ∈ ν.cells \ μ.cells)
    (hm : ∀ q ∈ ν.cells \ μ.cells, q.2 ≤ p.2) : TableauCorner.IsCorner ν p := by
  obtain ⟨hpν, hpμ⟩ := Finset.mem_sdiff.mp hp
  refine ⟨hpν, ?_, ?_⟩
  · intro hb
    have hbμ : (p.1 + 1, p.2) ∉ μ.cells := by
      intro hbμ
      exact hpμ (μ.up_left_mem (Nat.le_succ _) le_rfl hbμ)
    have he := h.2 (p.1 + 1, p.2) (Finset.mem_sdiff.mpr ⟨hb, hbμ⟩) p hp rfl
    have hf := congrArg Prod.fst he
    simp only [Prod.fst] at hf
    omega
  · intro hr
    have hrμ : (p.1, p.2 + 1) ∉ μ.cells := by
      intro hrμ
      exact hpμ (μ.up_left_mem le_rfl (Nat.le_succ _) hrμ)
    have hc := hm (p.1, p.2 + 1) (Finset.mem_sdiff.mpr ⟨hr, hrμ⟩)
    simp only [Prod.snd] at hc
    omega

private theorem erase_horizontal (μ ν : YoungDiagram) (p : ℕ × ℕ)
    (h : Horizontal μ ν) (hp : p ∈ ν.cells \ μ.cells)
    (hc : TableauCorner.IsCorner ν p) : Horizontal μ (TableauCorner.eraseShape ν p hc) := by
  refine ⟨?_, ?_⟩
  · intro q hq
    apply Finset.mem_erase.mpr
    refine ⟨?_, h.1 hq⟩
    intro he
    subst q
    exact (Finset.mem_sdiff.mp hp).2 hq
  · intro q hq r hr he
    exact h.2 q (Finset.mem_sdiff.mpr
      ⟨(Finset.mem_erase.mp (Finset.mem_sdiff.mp hq).1).2, (Finset.mem_sdiff.mp hq).2⟩)
      r (Finset.mem_sdiff.mpr
      ⟨(Finset.mem_erase.mp (Finset.mem_sdiff.mp hr).1).2, (Finset.mem_sdiff.mp hr).2⟩) he

private theorem erase_difference (μ ν : YoungDiagram) (p : ℕ × ℕ)
    (hc : TableauCorner.IsCorner ν p) :
    (TableauCorner.eraseShape ν p hc).cells \ μ.cells = (ν.cells \ μ.cells).erase p := by
  ext q
  simp only [TableauCorner.erase_cells, Finset.mem_sdiff, Finset.mem_erase]
  tauto

/-- Every exact strictly right-to-left enumeration is a valid dependent erasure chain. -/
theorem peel_order (μ ν : YoungDiagram) (ps : List (ℕ × ℕ))
    (h : Horizontal μ ν) (ho : ps.Pairwise (fun p q => q.2 < p.2))
    (he : ps.toFinset = ν.cells \ μ.cells) : PeelsTo μ ν ps := by
  induction ps generalizing ν with
  | nil =>
    apply YoungDiagram.ext
    apply Finset.Subset.antisymm
    · apply Finset.sdiff_eq_empty_iff_subset.mp
      exact he.symm
    · exact h.1
  | cons p ps ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp ho
    have hp : p ∈ ν.cells \ μ.cells := by
      rw [← he]
      simp
    have hm : ∀ q ∈ ν.cells \ μ.cells, q.2 ≤ p.2 := by
      intro q hq
      rw [← he, List.mem_toFinset] at hq
      rcases List.mem_cons.mp hq with hqp | hq
      · subst q
        exact le_rfl
      · exact (hhead q hq).le
    have hc := rightmost_corner μ ν p h hp hm
    refine ⟨hc, ih (TableauCorner.eraseShape ν p hc) (erase_horizontal μ ν p h hp hc) htail ?_⟩
    have hn : p ∉ ps.toFinset := by
      intro hm
      exact Nat.lt_irrefl _ (hhead p (List.mem_toFinset.mp hm))
    rw [erase_difference, ← he]
    simp [hn]

-- A finite set with injective column projection admits a decreasing enumeration.
-- The induction here constructs a list only; validity is supplied by peel_order.
private theorem decreasing_enumeration (s : Finset (ℕ × ℕ))
    (hi : ∀ p ∈ s, ∀ q ∈ s, p.2 = q.2 → p = q) :
    ∃ ps : List (ℕ × ℕ), ps.Pairwise (fun p q => q.2 < p.2) ∧ ps.toFinset = s := by
  induction s using Finset.strongInductionOn with
  | _ s ih =>
    by_cases he : s = ∅
    · exact ⟨[], by simp, by simpa using he.symm⟩
    · obtain ⟨p, hp, hm⟩ := Finset.exists_max_image s Prod.snd (Finset.nonempty_iff_ne_empty.mpr he)
      have hsmall : ∀ q ∈ s.erase p, ∀ r ∈ s.erase p, q.2 = r.2 → q = r := by
        intro q hq r hr heq
        exact hi q (Finset.mem_erase.mp hq).2 r (Finset.mem_erase.mp hr).2 heq
      obtain ⟨ps, ho, hps⟩ := ih (s.erase p) (Finset.erase_ssubset hp) hsmall
      refine ⟨p :: ps, List.pairwise_cons.mpr ⟨?_, ho⟩, ?_⟩
      · intro q hq
        have hqe : q ∈ s.erase p := by
          rw [← hps]
          exact List.mem_toFinset.mpr hq
        obtain ⟨hne, hqs⟩ := Finset.mem_erase.mp hqe
        have hle := hm q hqs
        have hnc : q.2 ≠ p.2 := fun heq => hne (hi q hqs p hp heq)
        omega
      · rw [List.toFinset_cons, hps, Finset.insert_erase hp]

/-- An exact right-to-left valid erasure order exists, including for the empty strip. -/
theorem exists_peel_order (μ ν : YoungDiagram) (h : Horizontal μ ν) :
    ∃ ps : List (ℕ × ℕ), ps.Pairwise (fun p q => q.2 < p.2) ∧
      ps.toFinset = ν.cells \ μ.cells ∧ PeelsTo μ ν ps := by
  obtain ⟨ps, ho, he⟩ := decreasing_enumeration (ν.cells \ μ.cells) h.2
  exact ⟨ps, ho, he, peel_order μ ν ps h ho he⟩

#print axioms Horizontal
#print axioms PeelsTo
#print axioms rightmost_corner
#print axioms erase_horizontal
#print axioms erase_difference
#print axioms peel_order
#print axioms decreasing_enumeration
#print axioms exists_peel_order
end OddMath.Frontier.TableauStripCorners
