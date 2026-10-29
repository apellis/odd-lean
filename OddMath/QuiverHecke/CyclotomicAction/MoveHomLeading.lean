/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.AppendContentMoveCoordinates

/-!
# Signed top-crossing part of the moving chain

The polynomial decorations are retained in their chronological positions.
At equal colours the leading decoration is `(v-u)^2` in even parity and
`-(v^2-u^2)^2` in odd parity. Multiplication in `End` reverses categorical
composition, so these decorate the output of the crossing. The theorem
`moveHom_sub_leading_mem_low` discards every choice of a crossing-free
summand in the prescribed chain, at arbitrary word length. Collecting these
decorations into one ordered polynomial is a separate normal-ordering step.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
open scoped Classical
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- Composition adds crossing bounds, without identifying any leading scalar. -/
theorem filt_comp_mem {s t v : List I} {m n : ℕ}
    {f : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t)}
    {g : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D v)}
    (hf : f ∈ Filt D Sc s t m) (hg : g ∈ Filt D Sc t v n) :
    f ≫ g ∈ Filt D Sc s v (m + n) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨Q, hQ, hq, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨R, hR, hr, rfl⟩ := hg
      rw [cl_comp]
      exact cl_mem_filt D Sc _ (by simp only [crossCount_append]; omega)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [Preadditive.comp_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      rw [Linear.comp_smul]; exact Submodule.smul_mem _ c hx
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [Linear.smul_comp]; exact Submodule.smul_mem _ c hx

/-- A strict crossing bound stays strict after composition. -/
theorem filt_comp_low_mem {s t v : List I} {m n : ℕ}
    {f : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t)}
    {g : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D v)}
    (hf : f ∈ Filt D Sc s t m) (hg : g ∈ Low D Sc t v n) :
    f ≫ g ∈ Low D Sc s v (m + n) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨Q, hQ, hq, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨R, hR, hr, rfl⟩ := hg
      rw [cl_comp]
      exact cl_mem_low D Sc _ (by simp only [crossCount_append]; omega)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [Preadditive.comp_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      rw [Linear.comp_smul]; exact Submodule.smul_mem _ c hx
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [Linear.smul_comp]; exact Submodule.smul_mem _ c hx

/-- A strict bound also stays strict on the lower side of a composite. -/
theorem low_comp_filt_mem {s t v : List I} {m n : ℕ}
    {f : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t)}
    {g : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D v)}
    (hf : f ∈ Low D Sc s t m) (hg : g ∈ Filt D Sc t v n) :
    f ≫ g ∈ Low D Sc s v (m + n) := by
  induction hf using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨Q, hQ, hq, rfl⟩ := hf
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨R, hR, hr, rfl⟩ := hg
      rw [cl_comp]
      exact cl_mem_low D Sc _ (by simp only [crossCount_append]; omega)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [Preadditive.comp_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx =>
      rw [Linear.comp_smul]; exact Submodule.smul_mem _ c hx
  | zero => simp
  | add x y _ _ hx hy =>
    rw [Preadditive.add_comp]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx =>
    rw [Linear.smul_comp]; exact Submodule.smul_mem _ c hx

/-- Telescoping two specified leading terms preserves their exact coefficients. -/
theorem filtered_comp_sub_mem_low {s t v : List I} {m n : ℕ}
    {f f' : (pres D Sc).obj (ob D s) ⟶ (pres D Sc).obj (ob D t)}
    {g g' : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D v)}
    (hf : f ∈ Filt D Sc s t m) (hg' : g' ∈ Filt D Sc t v n)
    (hff' : f - f' ∈ Low D Sc s t m) (hgg' : g - g' ∈ Low D Sc t v n) :
    f ≫ g - f' ≫ g' ∈ Low D Sc s v (m + n) := by
  have h := (Low D Sc s v (m + n)).add_mem
    (filt_comp_low_mem D Sc hf hgg') (low_comp_filt_mem D Sc hff' hg')
  simpa only [Preadditive.comp_sub, Preadditive.sub_comp, sub_add_sub_cancel] using h

private theorem filt_eqToHom {s t : List I} (h : s = t) :
    eqToHom (congrArg (fun v => (pres D Sc).obj (ob D v)) h) ∈ Filt D Sc s t 0 := by
  subst t
  have hc := cl_mem_filt D Sc (show SChain s (pl s []) s from rfl) (n := 0) (by simp)
  simpa only [cl_nil, eqToHom_refl] using hc

private theorem filt_mul {s : List I} {m n : ℕ}
    {f g : End ((pres D Sc).obj (ob D s))}
    (hf : f ∈ Filt D Sc s s m) (hg : g ∈ Filt D Sc s s n) :
    f * g ∈ Filt D Sc s s (m + n) := by
  simpa only [End.mul_def, Nat.add_comm] using filt_comp_mem D Sc hg hf

private theorem filt_dot (s : List I) (a : ℕ) : dotE D Sc s a ∈ Filt D Sc s s 0 := by
  rw [dotE_eq_cl D Sc (sChain_dotAny s a)]
  exact cl_mem_filt D Sc _ (by simp [crossCount, PG.isCross])

/-- Signed leading same-colour polynomial, with no crossing-free summand. -/
def leadingSameIntertwiner (s : List I) (a : ℕ) (i : I) :
    End ((pres D Sc).obj (ob D s)) :=
  if D.parity i = 1 then
    -((dotE D Sc s (a + 1) ^ 2 - dotE D Sc s a ^ 2) ^ 2 * crossE D Sc s a)
  else (dotE D Sc s (a + 1) - dotE D Sc s a) ^ 2 * crossE D Sc s a

private theorem leadingSame_bounds (s : List I) (a : ℕ) (i : I) :
    leadingSameIntertwiner D Sc s a i ∈ Filt D Sc s s 1 ∧
    sameIntertwiner D Sc s a i - leadingSameIntertwiner D Sc s a i ∈ Filt D Sc s s 0 := by
  have hu := filt_dot D Sc s a
  have hv := filt_dot D Sc s (a + 1)
  have he := (Filt D Sc s s 0).sub_mem hv hu
  have hd := (Filt D Sc s s 0).sub_mem
    (show dotE D Sc s (a + 1) ^ 2 ∈ Filt D Sc s s 0 by
      simpa only [pow_two] using filt_mul D Sc hv hv)
    (show dotE D Sc s a ^ 2 ∈ Filt D Sc s s 0 by
      simpa only [pow_two] using filt_mul D Sc hu hu)
  have ht : crossE D Sc s a ∈ Filt D Sc s s 1 := by
    unfold crossE genE
    split_ifs with h
    · exact cl_mem_filt D Sc h (by simp [crossCount, PG.isCross])
    · exact Submodule.zero_mem _
  have hee : (dotE D Sc s (a + 1) - dotE D Sc s a) ^ 2 ∈
      Filt D Sc s s 0 := by simpa only [pow_two] using filt_mul D Sc he he
  have hdd : (dotE D Sc s (a + 1) ^ 2 - dotE D Sc s a ^ 2) ^ 2 ∈
      Filt D Sc s s 0 := by simpa only [pow_two] using filt_mul D Sc hd hd
  have hddt := filt_mul D Sc hdd ht
  have heet := filt_mul D Sc hee ht
  have hde := filt_mul D Sc hd he
  by_cases hp : D.parity i = 1
  · simp only [leadingSameIntertwiner, sameIntertwiner, hp, ite_true]
    constructor
    · exact (Filt D Sc s s 1).neg_mem hddt
    · rw [movingOdd_crossingCoefficient]
      simpa only [sub_neg_eq_add, sub_add_cancel] using hde
  · simp only [leadingSameIntertwiner, sameIntertwiner, hp, ite_false]
    constructor
    · exact heet
    · rw [movingEven_crossingCoefficient, add_sub_cancel_right]
      exact he

/-- The leading summand of an adjacent intertwiner, with its library sign. -/
def leadingIntertwinerHom (l r : List I) (i j : I) :
    (pres D Sc).obj (ob D (l ++ [i, j] ++ r)) ⟶
      (pres D Sc).obj (ob D (l ++ [j, i] ++ r)) :=
  if h : i = j then
    leadingSameIntertwiner D Sc (l ++ [i, j] ++ r) l.length i ≫ eqToHom (by rw [h])
  else cl D Sc _ _ [.cross l.length] (sChain_crossAt l r i j)

/-- Local leading term and discarded error have respectively one and zero crossings. -/
theorem leadingIntertwiner_bounds (l r : List I) (i j : I) :
    leadingIntertwinerHom D Sc l r i j ∈ Filt D Sc _ _ 1 ∧
    intertwinerHom D Sc l r i j - leadingIntertwinerHom D Sc l r i j ∈
      Filt D Sc _ _ 0 := by
  by_cases h : i = j
  · subst j
    simpa [leadingIntertwinerHom, intertwinerHom] using
      leadingSame_bounds D Sc (l ++ [i, i] ++ r) l.length i
  · simp only [leadingIntertwinerHom, intertwinerHom, dite_eq_right h, sub_self]
    exact ⟨cl_mem_filt D Sc _ (by simp [crossCount, PG.isCross]), Submodule.zero_mem _⟩

/-- Chronological product of the signed polynomial-decorated crossings. -/
def leadingMoveHom (i : I) : (l ν : List I) →
    (pres D Sc).obj (ob D (l ++ i :: ν)) ⟶ (pres D Sc).obj (ob D (l ++ ν ++ [i]))
  | l, [] => eqToHom (by simp)
  | l, j :: ν =>
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) (by simp)) ≫
        leadingIntertwinerHom D Sc l ν i j ≫
          eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t))
            (show l ++ [j, i] ++ ν = (l ++ [j]) ++ i :: ν by simp)) ≫
            leadingMoveHom i (l ++ [j]) ν ≫
              eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) (by simp))

private theorem leadingIntertwiner_filt (l r : List I) (i j : I) :
    intertwinerHom D Sc l r i j ∈ Filt D Sc _ _ 1 := by
  obtain ⟨hL, hE⟩ := leadingIntertwiner_bounds D Sc l r i j
  have h := (Filt D Sc _ _ 1).add_mem (filt_mono D Sc (by omega : 0 ≤ 1) hE) hL
  simpa only [sub_add_cancel] using h

private theorem moveHom_leading_bounds (i : I) (l ν : List I) :
    moveHom D Sc i l ν ∈ Filt D Sc _ _ ν.length ∧
    leadingMoveHom D Sc i l ν ∈ Filt D Sc _ _ ν.length ∧
    moveHom D Sc i l ν - leadingMoveHom D Sc i l ν ∈ Low D Sc _ _ ν.length := by
  induction ν generalizing l with
  | nil =>
    simp only [moveHom, leadingMoveHom, List.length_nil, sub_self]
    exact ⟨filt_eqToHom D Sc (by simp), filt_eqToHom D Sc (by simp), Submodule.zero_mem _⟩
  | cons j ν ih =>
    obtain ⟨hG, hL, hE⟩ := ih (l ++ [j])
    have hA := leadingIntertwiner_filt D Sc l ν i j
    obtain ⟨hB, hAB⟩ := leadingIntertwiner_bounds D Sc l ν i j
    have h0 := filt_eqToHom D Sc
      (show l ++ i :: j :: ν = l ++ [i, j] ++ ν by simp)
    have h1 := filt_eqToHom D Sc
      (show l ++ [j, i] ++ ν = (l ++ [j]) ++ i :: ν by simp)
    have h2 := filt_eqToHom D Sc
      (show (l ++ [j]) ++ ν ++ [i] = l ++ (j :: ν) ++ [i] by simp)
    have hG2 := filt_comp_mem D Sc hG h2
    have hL2 := filt_comp_mem D Sc hL h2
    have hE2 := low_comp_filt_mem D Sc hE h2
    rw [Preadditive.sub_comp] at hE2
    have hG1 := filt_comp_mem D Sc h1 hG2
    have hL1 := filt_comp_mem D Sc h1 hL2
    have hE1 := filt_comp_low_mem D Sc h1 hE2
    rw [Preadditive.comp_sub] at hE1
    have hGA := filt_comp_mem D Sc hA hG1
    have hLA := filt_comp_mem D Sc hB hL1
    have hEA := filtered_comp_sub_mem_low D Sc hA hL1
      (filt_le_low D Sc (by omega : 0 < 1) hAB) hE1
    have hG0 := filt_comp_mem D Sc h0 hGA
    have hL0 := filt_comp_mem D Sc h0 hLA
    have hE0 := filt_comp_low_mem D Sc h0 hEA
    rw [Preadditive.comp_sub] at hE0
    simpa only [moveHom, leadingMoveHom, List.length_cons, Nat.add_zero,
      Nat.zero_add, Nat.add_comm 1] using And.intro hG0 (And.intro hL0 hE0)

/-- Every discarded summand of the full prescribed chain has fewer crossings
than the old word. The remaining chain retains the explicit even positive and
odd negative polynomial factors, not an unspecified leading unit. -/
theorem moveHom_sub_leading_mem_low (i : I) (l ν : List I) :
    moveHom D Sc i l ν - leadingMoveHom D Sc i l ν ∈
      Low D Sc (l ++ i :: ν) (l ++ ν ++ [i]) ν.length :=
  (moveHom_leading_bounds D Sc i l ν).2.2

/-- The full moving-shuffle coordinates ignore all discarded summands of the
prescribed chain, including coordinates with nontrivial old permutations. -/
theorem moveHom_long_prepend_repr (i : I) (ν : List I)
    (x : PrependIdx i ν (ν ++ [i]))
    (hx : x.1.2.2.2 = longPrependShuffle ν.length) :
    (prependBasis D Sc (i := i) (s := ν) (t := ν ++ [i])).repr (moveHom D Sc i [] ν) x =
      (prependBasis D Sc (i := i) (s := ν) (t := ν ++ [i])).repr (leadingMoveHom D Sc i [] ν) x := by
  have h := prependBasis_long_repr_eq_zero_of_low D Sc i ν (ν ++ [i])
    (moveHom D Sc i [] ν - leadingMoveHom D Sc i [] ν)
    (moveHom_sub_leading_mem_low D Sc i [] ν) x hx
  simpa only [map_sub, Finsupp.sub_apply, sub_eq_zero] using h

end OddMath.QuiverHecke
