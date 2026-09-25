import OddMath.Frontier.SignedKostkaInvertibility

/-!
# Exhaustive finite degree-shape indexing

All Young diagrams of a fixed size, with no supplied finite family or alphabet
restriction. This discharges the indexing gap for the genuine signed Kostka
inverse; it does not assert a complete-function product expansion or symmetry.
-/
namespace OddMath.Frontier.DegreeShapes
open scoped BigOperators

/-- The literal family of every Young diagram of degree `d`. -/
def DegreeShape (d : ℕ) := {μ : YoungDiagram // μ.card = d}

/-- Downward closure forces each coordinate to be smaller than the total size. -/
theorem cell_lt_card (μ : YoungDiagram) (p : ℕ × ℕ)
    (hp : p ∈ μ.cells) : p.1 < μ.card ∧ p.2 < μ.card := by
  have hr : p.2 < μ.rowLen p.1 := YoungDiagram.mem_iff_lt_rowLen.mp hp
  have hc : p.1 < μ.colLen p.2 := YoungDiagram.mem_iff_lt_colLen.mp hp
  have hrle : μ.rowLen p.1 ≤ μ.card := by
    rw [YoungDiagram.rowLen_eq_card]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hcle : μ.colLen p.2 ≤ μ.card := by
    rw [YoungDiagram.colLen_eq_card]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  exact ⟨lt_of_lt_of_le hc hcle, lt_of_lt_of_le hr hrle⟩

/-- Every degree-`d` diagram injects by its actual cells into the finite powerset
of the `d` by `d` grid. No enumeration or coverage hypothesis is an input. -/
noncomputable def degreeFintype (d : ℕ) : Fintype (DegreeShape d) := by
  classical
  let f : DegreeShape d → ↥((Finset.range d ×ˢ Finset.range d).powerset) :=
    fun μ => ⟨μ.val.cells, Finset.mem_powerset.mpr (by
      intro p hp
      have h := cell_lt_card μ.val p hp
      rw [μ.property] at h
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr h.1, Finset.mem_range.mpr h.2⟩)⟩
  apply Fintype.ofInjective f
  intro μ ν h
  apply Subtype.ext
  apply YoungDiagram.ext
  exact congrArg Subtype.val h

/-- Integral inversion for the actual signed tableau-count matrix on ALL shapes
of degree `d`, including the singleton family of degree zero. -/
theorem degree_unique_solution (d : ℕ) (b : DegreeShape d → ℤ) :
    letI := degreeFintype d
    ∃! c : DegreeShape d → ℤ, ∀ j,
      ∑ i, c i * TableauDominance.signedKostka i.val j.val = b j := by
  classical
  letI := degreeFintype d
  exact SignedKostkaInvertibility.kostka_unique_solution
    (fun μ : DegreeShape d => μ.val) Subtype.val_injective b

end OddMath.Frontier.DegreeShapes
