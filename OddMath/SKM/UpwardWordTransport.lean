import OddMath.SKM.PositiveDotTransport
import OddMath.SKM.SpanOneSided

/-! Repeated upward transport with a prescribed constant full-SYM coefficient. -/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams Presentation
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} (cs : CScalars Sc)

/-- A literal list of upward dot layers, with no crossings or extrema. -/
def UpDotsOnly (L : List (LayerData I)) : Prop :=
  ∀ x ∈ L, ∃ a i b, x = (a, Shape.dot i, b)

theorem UpDotsOnly.append {A B : List (LayerData I)}
    (hA : UpDotsOnly A) (hB : UpDotsOnly B) : UpDotsOnly (A ++ B) := by
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hA x hx
  · exact hB x hx

/-- Actual dot-only expressions followed by a full rightmost coefficient. -/
def wordDotSpan (μ : X) (W : List (Letter I)) (N : ℕ) :
    Submodule k ((pres D Sc).obj (ob D μ W) ⟶ (pres D Sc).obj (ob D μ W)) :=
  Submodule.span k {f | ∃ L : List (LayerData I), SChain W L W ∧ UpDotsOnly L ∧ N ≤ L.length ∧
    ∃ p : SYM D k, f = cl D Sc μ W W L ≫ bubAt D Sc μ W (betaSYM cs μ p)}

theorem wordDotSpan_bubAt (μ : X) (W : List (Letter I)) (p : SYM D k) :
    bubAt D Sc μ W (betaSYM cs μ p) ∈ wordDotSpan cs μ W 0 := by
  apply Submodule.subset_span
  refine ⟨[], ?_, ?_, by simp, p, ?_⟩
  · simp [SChain]
  · intro x hx; simp at hx
  · simp [cl_nil]

theorem wordDotSpan_mono {μ : X} {W : List (Letter I)} {N M : ℕ} (h : N ≤ M) :
    wordDotSpan cs μ W M ≤ wordDotSpan cs μ W N := by
  apply Submodule.span_mono
  rintro f ⟨L, hL, hd, hn, p, rfl⟩
  exact ⟨L, hL, hd, h.trans hn, p, rfl⟩

/-- Prepending actual dots retains a quantitative positive-dot bound. -/
theorem wordDotSpan_prepend {μ : X} {W : List (Letter I)} {N M : ℕ}
    {L : List (LayerData I)} (hL : SChain W L W) (hd : UpDotsOnly L) (hn : N ≤ L.length)
    {f : (pres D Sc).obj (ob D μ W) ⟶ (pres D Sc).obj (ob D μ W)}
    (hf : f ∈ wordDotSpan cs μ W M) : cl D Sc μ W W L ≫ f ∈ wordDotSpan cs μ W (N + M) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨A, hA, hdA, hnA, p, rfl⟩ := hf
    rw [← Category.assoc, cl_comp hL hA]
    exact Submodule.subset_span ⟨L ++ A, hL.append hA, hd.append hdA,
      by simpa only [List.length_append] using Nat.add_le_add hn hnA, p, rfl⟩
  | zero => rw [Limits.comp_zero]; exact Submodule.zero_mem _
  | add f g _ _ hf hg => rw [Preadditive.comp_add]; exact Submodule.add_mem _ hf hg
  | smul a f _ hf => rw [Linear.comp_smul]; exact Submodule.smul_mem _ _ hf

theorem wordDotSpan_cast {μ : X} {W W' : List (Letter I)} (h : W = W') {N : ℕ}
    {f : (pres D Sc).obj (ob D μ W) ⟶ (pres D Sc).obj (ob D μ W)}
    (hf : f ∈ wordDotSpan cs μ W N) : wordCast μ h h f ∈ wordDotSpan cs μ W' N := by
  subst W'
  exact hf

theorem upDotsOnly_placed (P Q : List (Letter I)) (i : I) (n : ℕ) :
    UpDotsOnly ((dotsLay (up i) n).map (whL P Q)) := by
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  have hy' : y = ([], Shape.dot i, []) := by
    simp only [dotsLay, dotsL, List.mem_replicate] at hy
    exact hy.2
  subst y
  exact ⟨P, i, Q, by simp [whL]⟩

/-- An actual one-strand positive error remains positive after transporting
its coefficients through the remaining upward suffix. -/
theorem plcL_positiveDots_word {μ : X} {P Q : List (Letter I)} {j : I}
    (ih : ∀ (P' : List (Letter I)) (p : SYM D k),
      plcL D Sc μ P' Q [] [] (betaSYM cs (wt D μ Q) p) ∈
        wordDotSpan cs μ (P' ++ [] ++ Q) 0)
    {f} (hf : f ∈ dotSlideAtLeast cs (wt D μ Q) (up j) 1) :
    plcL D Sc μ P Q [up j] [up j] f ∈ wordDotSpan cs μ (P ++ [up j] ++ Q) 1 := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨a, ha, γ, hγ, _, rfl⟩ := hf
    change γ ∈ bubbleSpan cs (wt D (wt D μ Q) []) at hγ
    rw [← betaSYM_range] at hγ
    obtain ⟨p, rfl⟩ := hγ
    rw [plcL_comp, plcL_cl, plcL_plcL_right]
    have hb := wordDotSpan_cast cs (W' := P ++ [up j] ++ Q) (by simp) (ih (P ++ [up j]) p)
    exact wordDotSpan_prepend cs (N := 1) (M := 0)
      ((sChain_dotsLay (up j) a).wh P Q rfl rfl)
      (upDotsOnly_placed P Q j a) (by simpa [dotsLay, dotsL] using ha) hb
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add f g _ _ hf hg => rw [map_add]; exact Submodule.add_mem _ hf hg
  | smul a f _ hf => rw [map_smul]; exact Submodule.smul_mem _ _ hf

/-- Across an arbitrary upward word, the zero-dot coefficient is literally
unchanged and every correction has a nonempty actual list of upward dots. -/
theorem betaSYM_upward_word_difference (μ : X) :
    ∀ (q : List I) (P : List (Letter I)) (p : SYM D k),
      plcL D Sc μ P (ups q) [] [] (betaSYM cs (wt D μ (ups q)) p) -
        bubAt D Sc μ (P ++ [] ++ ups q) (betaSYM cs μ p) ∈
        wordDotSpan cs μ (P ++ [] ++ ups q) 1
  | [], P, p => by
    change plcL D Sc μ P [] [] [] (betaSYM cs μ p) -
      bubAt D Sc μ (P ++ [] ++ []) (betaSYM cs μ p) ∈ wordDotSpan cs μ (P ++ [] ++ []) 1
    rw [plcL_nil_eq_bubAt, sub_self]
    exact Submodule.zero_mem _
  | j :: q, P, p => by
    have ih₀ : ∀ (P' : List (Letter I)) (r : SYM D k),
        plcL D Sc μ P' (ups q) [] [] (betaSYM cs (wt D μ (ups q)) r) ∈
          wordDotSpan cs μ (P' ++ [] ++ ups q) 0 := by
      intro P' r
      have H := Submodule.add_mem _
        (wordDotSpan_mono cs (Nat.zero_le 1) (betaSYM_upward_word_difference μ q P' r))
        (wordDotSpan_bubAt cs μ (P' ++ [] ++ ups q) r)
      simpa only [sub_add_cancel] using H
    have hs := plcL_positiveDots_word cs (P := P) ih₀
      (betaSYM_slide_difference cs (wt D μ (ups q)) j p)
    rw [map_sub] at hs
    simp only [lbub, rbub] at hs
    rw [plcL_plcL_left, plcL_plcL_right] at hs
    have hr := wordDotSpan_cast cs (W' := P ++ [up j] ++ ups q) (by simp)
      (betaSYM_upward_word_difference μ q (P ++ [up j]) p)
    rw [map_sub] at hr
    simp only [wt_nil] at hs
    have H := Submodule.add_mem _ hs hr
    rw [sub_add_sub_cancel] at H
    have H' := wordDotSpan_cast cs (W' := P ++ [] ++ up j :: ups q) (by simp) H
    rw [map_sub, wordCast_symm_wordCast] at H'
    change plcL D Sc μ P (up j :: ups q) [] []
      (betaSYM cs (wt D (wt D μ (ups q)) [up j]) p) -
        bubAt D Sc μ (P ++ [] ++ up j :: ups q) (betaSYM cs μ p) ∈
          wordDotSpan cs μ (P ++ [] ++ up j :: ups q) 1
    simpa only [← bubAt_congr] using H'

/-- Nonempty literal dot lists on a fixed word. -/
def PositiveWordDots (W : List (Letter I)) :=
  {L : List (LayerData I) // SChain W L W ∧ UpDotsOnly L ∧ 0 < L.length}

/-- Finite actual positive-dot corrections with full coefficients on the right. -/
def positiveWordExpansion (μ : X) (W : List (Letter I)) :
    (PositiveWordDots W →₀ SYM D k) →ₗ[k]
      ((pres D Sc).obj (ob D μ W) ⟶ (pres D Sc).obj (ob D μ W)) :=
  Finsupp.lsum k (fun L =>
    { toFun := fun p => cl D Sc μ W W L.val ≫ bubAt D Sc μ W (betaSYM cs μ p)
      map_add' := by intros; simp only [map_add, Preadditive.comp_add]
      map_smul' := by intros; simp only [map_smul, Linear.comp_smul, RingHom.id_apply] })

theorem positiveWordExpansion_single (μ : X) (W : List (Letter I))
    (L : PositiveWordDots W) (p : SYM D k) :
    positiveWordExpansion cs μ W (Finsupp.single L p) =
      cl D Sc μ W W L.val ≫ bubAt D Sc μ W (betaSYM cs μ p) :=
  Finsupp.lsum_single k _ L p

theorem wordDotSpan_one_le_range (μ : X) (W : List (Letter I)) :
    wordDotSpan cs μ W 1 ≤ (positiveWordExpansion cs μ W).range := by
  apply Submodule.span_le.mpr
  rintro f ⟨L, hL, hd, hn, p, rfl⟩
  exact ⟨Finsupp.single ⟨L, hL, hd, hn⟩ p,
    positiveWordExpansion_single cs μ W ⟨L, hL, hd, hn⟩ p⟩

/-- Native finite repeated-word slide: unchanged constant coefficient and
strictly positive actual dot corrections. -/
theorem betaSYM_exists_positiveWordExpansion (μ : X) (q : List I)
    (P : List (Letter I)) (p : SYM D k) :
    ∃ z : PositiveWordDots (P ++ [] ++ ups q) →₀ SYM D k,
      plcL D Sc μ P (ups q) [] [] (betaSYM cs (wt D μ (ups q)) p) =
        bubAt D Sc μ (P ++ [] ++ ups q) (betaSYM cs μ p) +
          positiveWordExpansion cs μ (P ++ [] ++ ups q) z := by
  obtain ⟨z, hz⟩ := wordDotSpan_one_le_range cs μ (P ++ [] ++ ups q)
    (betaSYM_upward_word_difference cs μ q P p)
  exact ⟨z, by rw [hz]; abel⟩

end OddMath.SKM
