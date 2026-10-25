import OddMath.SKM.UpwardWordTransport

/-! Exact normalization of top dots for the closure detector. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} (cs : CScalars Sc)

/-- Reordering top dots has no lower-crossing or lower-dot remainder.
This is the zero-error specialization of the actual interchange proof. -/
theorem top_dots_perm_eq {t : List (Letter I)} {is js : List ℕ} (h : is.Perm js)
    (hb : ∀ i ∈ is, i < t.length) (μ : X) {s v : List (Letter I)}
    (P Q : List (XLayer I)) (hP : XChain s P t) :
    ∃ p : ZMod 2, xev cs μ s v (P ++ dotsOn t is ++ Q) =
      zsign k p • xev cs μ s v (P ++ dotsOn t js ++ Q) := by
  obtain ⟨p, hp⟩ := dotsOn_perm (cs := cs) (ν := μ) (t₀ := v) (n := 0) h hb P Q hP
  have hzero : LtL D Sc cs μ s v 0 = ⊥ := by
    apply Submodule.span_eq_bot.mpr
    rintro f ⟨L, hL, _⟩
    omega
  rw [hzero, Submodule.mem_bot] at hp
  exact ⟨p, sub_eq_zero.mp hp⟩

/-- Convert the positive-dot correction syntax to actual top-boundary dot
positions, preserving the exact dot count. -/
theorem upDotsOnly_eq_dotsOn {W : List (Letter I)} {L : List (LayerData I)}
    (hL : SChain W L W) (hd : UpDotsOnly L) :
    ∃ is : List ℕ, L.map ofL = dotsOn W is ∧ is.length = L.length ∧
      ∀ i ∈ is, i < W.length := by
  induction L generalizing W with
  | nil => exact ⟨[], rfl, rfl, by simp⟩
  | cons x L ih =>
    obtain ⟨u, i, v, rfl⟩ := hd x List.mem_cons_self
    have he : W = u ++ up i :: v := by simpa [SChain, Shape.dom] using hL.1
    subst W
    have ht : SChain (u ++ up i :: v) L (u ++ up i :: v) := by
      simpa [Shape.cod] using hL.2
    obtain ⟨is, his, hn, hb⟩ := ih ht (fun x hx => hd x (List.mem_cons_of_mem _ hx))
    refine ⟨u.length :: is, ?_, by simp [hn], ?_⟩
    · simp only [List.map_cons, dotsOn_cons, dotOn_eq, his]
      simp [xDotL, ofL, xwhL]
    · intro j hj
      rcases List.mem_cons.mp hj with rfl | hj
      · simp
      · exact hb j hj

/-- A nonempty closure correction appended to top dots strictly increases
their number while leaving the skeleton untouched. -/
theorem positiveWordDots_append_top {t : List (Letter I)} (L : PositiveWordDots t)
    (P : List (XLayer I)) (is : List ℕ) :
    ∃ js : List ℕ,
      P ++ dotsOn t is ++ L.val.map ofL = P ++ dotsOn t js ∧
      is.length < js.length ∧ ∀ j ∈ js, j ∈ is ∨ j < t.length := by
  obtain ⟨ns, hns, hn, hb⟩ := upDotsOnly_eq_dotsOn L.property.1 L.property.2.1
  refine ⟨is ++ ns, ?_, ?_, ?_⟩
  · rw [hns, dotsOn_append, List.append_assoc]
  · rw [List.length_append, hn]
    exact Nat.lt_add_of_pos_right L.property.2.2
  · intro j hj
    rcases List.mem_append.mp hj with hj | hj
    · exact Or.inl hj
    · exact Or.inr (hb j hj)

/-- Dot-only correction layers carry no crossings. -/
theorem upDotsOnly_xcnt {W : List (Letter I)} {L : List (LayerData I)}
    (hL : SChain W L W) (hd : UpDotsOnly L) : xcnt (L.map ofL) = 0 := by
  obtain ⟨is, his, _, _⟩ := upDotsOnly_eq_dotsOn hL hd
  rw [his, xcnt_dotsOn]

end OddMath.SKM
