/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Preadditive.Mat
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.WindowCases

/-! # Block maps with an identity block

The auxiliary maps of §3 of `docs/Nondegeneracy/ProbeWindowInverse.md` are morphisms
`X ⊕ Oᶥ ⟶ Y ⊕ Oᵏ` of `Mat_ C` (`ProbeWindow.gObj`, `ProbeWindow.gMap`), given by a corner
`a : X ⟶ Y`, columns `B i : O ⟶ Y`, rows `Cc r : X ⟶ O` and a block `E i r : O ⟶ O`.

In the mixed cases (b), (c) there the block `E` is an identity block. Eliminating it leaves a
cap window (when the target is larger, `ProbeWindow.isIso_gMap_of_isCapInverse`) or a cup
window (when the source is larger, `ProbeWindow.isIso_gMap_of_isCupInverse`) whose corner is
`a - Σ Cc r ≫ B r`; the inverses are explicit, as in (9), (10), (12), (13) there.
-/

namespace OddMath.QuiverHecke.SwappedAssembly.ProbeWindow

open CategoryTheory

variable {C : Type*} [Category C] [Preadditive C]

/-- The object `Y ⊕ Oᶥ` of `Mat_ C`. -/
abbrev gObj (Y O : C) (ι : Type) [Fintype ι] [DecidableEq ι] : Mat_ C where
  ι := Option ι
  X o := @Option.rec ι (fun _ => C) Y (fun _ => O) o

variable {ι κ μ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype μ] [DecidableEq μ]

/-- The block map `X ⊕ Oᶥ ⟶ Y ⊕ Oᵏ` with corner `a`, columns `B`, rows `Cc` and block `E`. -/
def gMap {X Y O : C} (a : X ⟶ Y) (B : ι → (O ⟶ Y)) (Cc : κ → (X ⟶ O))
    (E : ι → κ → (O ⟶ O)) : gObj X O ι ⟶ gObj Y O κ :=
  fun o o' => match o, o' with
    | none, none => a
    | some i, none => B i
    | none, some r => Cc r
    | some i, some r => E i r

section Entries

variable {X Y O : C}

@[simp] lemma gMap_none_none (a : X ⟶ Y) (B : ι → (O ⟶ Y)) (Cc : κ → (X ⟶ O))
    (E : ι → κ → (O ⟶ O)) : (gMap a B Cc E none none : X ⟶ Y) = a := rfl
@[simp] lemma gMap_some_none (a : X ⟶ Y) (B : ι → (O ⟶ Y)) (Cc : κ → (X ⟶ O))
    (E : ι → κ → (O ⟶ O)) (i : ι) : (gMap a B Cc E (some i) none : O ⟶ Y) = B i := rfl
@[simp] lemma gMap_none_some (a : X ⟶ Y) (B : ι → (O ⟶ Y)) (Cc : κ → (X ⟶ O))
    (E : ι → κ → (O ⟶ O)) (r : κ) : (gMap a B Cc E none (some r) : X ⟶ O) = Cc r := rfl
@[simp] lemma gMap_some_some (a : X ⟶ Y) (B : ι → (O ⟶ Y)) (Cc : κ → (X ⟶ O))
    (E : ι → κ → (O ⟶ O)) (i : ι) (r : κ) :
    (gMap a B Cc E (some i) (some r) : O ⟶ O) = E i r := rfl

end Entries

/-- Every morphism `X ⊕ Oᶥ ⟶ Y ⊕ Oᵏ` is a block map. -/
lemma gMap_eta {X Y O : C} (f : gObj X O ι ⟶ gObj Y O κ) :
    f = gMap (f none none) (fun i => f (some i) none) (fun r => f none (some r))
      (fun i r => f (some i) (some r)) := by
  ext o o'
  rcases o with _ | i <;> rcases o' with _ | r <;> rfl

lemma gMap_comp {X Y Z O : C} (a : X ⟶ Y) (B : ι → (O ⟶ Y)) (Cc : κ → (X ⟶ O))
    (E : ι → κ → (O ⟶ O)) (a' : Y ⟶ Z) (B' : κ → (O ⟶ Z)) (Cc' : μ → (Y ⟶ O))
    (E' : κ → μ → (O ⟶ O)) :
    gMap a B Cc E ≫ gMap a' B' Cc' E' =
      gMap (a ≫ a' + ∑ r, Cc r ≫ B' r) (fun i => B i ≫ a' + ∑ r, E i r ≫ B' r)
        (fun m => a ≫ Cc' m + ∑ r, Cc r ≫ E' r m)
        (fun i m => B i ≫ Cc' m + ∑ r, E i r ≫ E' r m) := by
  ext o o'
  rw [Mat_.comp_apply, Fintype.sum_option]
  rcases o with _ | i <;> rcases o' with _ | m <;> rfl

lemma gMap_id (Y O : C) :
    𝟙 (gObj Y O κ) = gMap (𝟙 Y) (fun _ => 0) (fun _ => 0)
      (fun r r' => if r = r' then 𝟙 O else 0) := by
  ext o o'
  rcases o with _ | r <;> rcases o' with _ | r'
  · exact Mat_.id_apply_self _ _
  · exact Mat_.id_apply_of_ne _ _ _ (by simp)
  · exact Mat_.id_apply_of_ne _ _ _ (by simp)
  · by_cases h : r = r'
    · subst h; simp only [gMap_some_some, ↓reduceIte]; exact Mat_.id_apply_self _ _
    · simp only [gMap_some_some, h, ↓reduceIte]
      exact Mat_.id_apply_of_ne _ _ _ (by simpa using h)

lemma gMap_congr {X Y O : C} {a a' : X ⟶ Y} {B B' : ι → (O ⟶ Y)} {Cc Cc' : κ → (X ⟶ O)}
    {E E' : ι → κ → (O ⟶ O)} (ha : a = a') (hB : ∀ i, B i = B' i) (hC : ∀ r, Cc r = Cc' r)
    (hE : ∀ i r, E i r = E' i r) : gMap a B Cc E = gMap a' B' Cc' E' := by
  subst ha
  obtain rfl : B = B' := funext hB
  obtain rfl : Cc = Cc' := funext hC
  obtain rfl : E = E' := funext fun i => funext (hE i)
  rfl

/-- A cap window `[s; w]` with an entrywise inverse is an isomorphism `X ⊕ O⁰ ⟶ Y ⊕ Oʰ`. -/
theorem isIso_gMap_capWindow {X Y O : C} {h : ℕ} {s : X ⟶ Y} {w : Fin h → (X ⟶ O)}
    {j : Y ⟶ X} {A : Fin h → (O ⟶ X)} (H : IsCapInverse s w j A) :
    IsIso (gMap s (fun e : Empty => e.elim) w (fun e _ => e.elim)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  refine ⟨gMap j A (fun e : Empty => e.elim) (fun _ e => e.elim), ?_, ?_⟩
  · rw [gMap_comp, gMap_id]
    refine gMap_congr (by simpa using h5) (fun e => e.elim) (fun e => e.elim) (fun e => e.elim)
  · rw [gMap_comp, gMap_id]
    refine gMap_congr (by simpa using h1) (fun n => by simpa using h2 n)
      (fun m => by simpa using h3 m) (fun n m => by simpa using h4 n m)

/-- A cup window `[s, w]` with an entrywise inverse is an isomorphism `X ⊕ Oʰ ⟶ Y ⊕ O⁰`. -/
theorem isIso_gMap_cupWindow {X Y O : C} {h : ℕ} {s : X ⟶ Y} {w : Fin h → (O ⟶ Y)}
    {j : Y ⟶ X} {D : Fin h → (Y ⟶ O)} (H : IsCupInverse s w j D) :
    IsIso (gMap s w (fun e : Empty => e.elim) (fun _ e => e.elim)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  refine ⟨gMap j (fun e : Empty => e.elim) D (fun e _ => e.elim), ?_, ?_⟩
  · rw [gMap_comp, gMap_id]
    refine gMap_congr (by simpa using h1) (fun n => by simpa using h3 n)
      (fun m => by simpa using h2 m) (fun n m => by simpa using h4 n m)
  · rw [gMap_comp, gMap_id]
    refine gMap_congr (by simpa using h5) (fun e => e.elim) (fun e => e.elim) (fun e => e.elim)

/-- Normal form for the entries of products of block maps: expand sums over `ι ⊕ Fin m`,
evaluate the Kronecker deltas and distribute composition. -/
syntax "block_norm" (Lean.Parser.Tactic.location)? : tactic
macro_rules
  | `(tactic| block_norm $[$loc]?) => `(tactic| simp only [Fintype.sum_sum_type, Sum.elim_inl,
      Sum.elim_inr, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, ite_comp, comp_ite,
      Category.id_comp, Category.comp_id, Limits.zero_comp, Limits.comp_zero,
      Finset.sum_const_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ,
      ↓reduceIte, Preadditive.add_comp, Preadditive.comp_add, Preadditive.neg_comp,
      Preadditive.comp_neg, Preadditive.sub_comp, Preadditive.comp_sub, Preadditive.sum_comp,
      Preadditive.comp_sum, Category.assoc, Finset.sum_add_distrib, Finset.sum_neg_distrib,
      Finset.sum_sub_distrib, neg_neg, add_zero, zero_add, neg_zero, sub_zero] $[$loc]?)

/-- **Elimination of an identity block onto the target.** Let `M : X ⊕ Oᶥ ⟶ Y ⊕ (Oᶥ ⊕ Oᵐ)`
have block `E` the identity onto the first summand and zero onto the second. If the cap window
`[a - Σᵢ Cc (inl i) ≫ B i; Cc (inr t)]` has an entrywise inverse, `M` is an isomorphism. -/
theorem isIso_gMap_of_isCapInverse {X Y O : C} {m : ℕ} (a : X ⟶ Y) (B : ι → (O ⟶ Y))
    (Cc : ι ⊕ Fin m → (X ⟶ O)) {j : Y ⟶ X} {A : Fin m → (O ⟶ X)}
    (H : IsCapInverse (a - ∑ i, Cc (Sum.inl i) ≫ B i) (fun t => Cc (Sum.inr t)) j A) :
    IsIso (gMap a B Cc (fun i r => if r = Sum.inl i then 𝟙 O else 0)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  have R1 : ∀ {Z : C} (g : Y ⟶ Z), j ≫ a ≫ g = g + ∑ x, j ≫ Cc (Sum.inl x) ≫ B x ≫ g := by
    intro Z g
    have := congrArg (· ≫ g) h1
    block_norm at this
    rw [← sub_eq_zero] at this ⊢; rw [← this]; abel
  have R1' : j ≫ a = 𝟙 Y + ∑ x, j ≫ Cc (Sum.inl x) ≫ B x := by
    simpa using R1 (𝟙 Y)
  have R2 : ∀ (n : Fin m) {Z : C} (g : Y ⟶ Z),
      A n ≫ a ≫ g = ∑ x, A n ≫ Cc (Sum.inl x) ≫ B x ≫ g := by
    intro n Z g
    have := congrArg (· ≫ g) (h2 n)
    block_norm at this
    exact sub_eq_zero.1 this
  have R2' : ∀ n : Fin m, A n ≫ a = ∑ x, A n ≫ Cc (Sum.inl x) ≫ B x := fun n => by
    simpa using R2 n (𝟙 Y)
  have R5 : ∀ {Z : C} (g : X ⟶ Z), a ≫ j ≫ g =
      g + ∑ x, Cc (Sum.inl x) ≫ B x ≫ j ≫ g - ∑ t, Cc (Sum.inr t) ≫ A t ≫ g := by
    intro Z g
    have := congrArg (· ≫ g) h5
    block_norm at this
    rw [← sub_eq_zero] at this ⊢; rw [← this]; abel
  have R5' : a ≫ j = 𝟙 X + ∑ x, Cc (Sum.inl x) ≫ B x ≫ j - ∑ t, Cc (Sum.inr t) ≫ A t := by
    simpa using R5 (𝟙 X)
  have h3' : ∀ t, j ≫ Cc (Sum.inr t) = 0 := h3
  have h4' : ∀ n t, A n ≫ Cc (Sum.inr t) = if n = t then 𝟙 O else 0 := h4
  refine ⟨gMap j (Sum.elim (fun i => -(B i ≫ j)) A) (fun i => -(j ≫ Cc (Sum.inl i)))
    (Sum.elim (fun i' i => (if i' = i then 𝟙 O else 0) + B i' ≫ j ≫ Cc (Sum.inl i))
      (fun t i => -(A t ≫ Cc (Sum.inl i)))), ?_, ?_⟩
  · rw [gMap_comp, gMap_id]
    refine gMap_congr ?_ (fun i => ?_) (fun i => ?_) (fun i i' => ?_)
    · block_norm; rw [R5']; abel
    · block_norm; abel
    · block_norm; rw [R5]; abel
    · block_norm; abel
  · rw [gMap_comp, gMap_id]
    refine gMap_congr ?_ ?_ ?_ ?_
    · block_norm; rw [R1']; abel
    · rintro (i | t)
      · block_norm; rw [R1']; block_norm; abel
      · block_norm; rw [R2']; abel
    · rintro (i | t)
      · block_norm; abel
      · block_norm; rw [h3']
    · rintro (i | t) (i' | t')
      · block_norm; abel
      · block_norm; rw [h3', Limits.comp_zero, neg_zero]
      · block_norm; abel
      · block_norm; rw [h4']

/-- Elimination of an identity block when the source is larger: if the source is
`X ⊕ O^{κ ⊕ m}` and the block is the identity of `O^κ`, the map is an isomorphism as soon as
the reduced cup window `[a - Σ Cc r ≫ B r, B (inr n)]` has an entrywise inverse. -/
theorem isIso_gMap_of_isCupInverse {X Y O : C} {m : ℕ} (a : X ⟶ Y) (B : κ ⊕ Fin m → (O ⟶ Y))
    (Cc : κ → (X ⟶ O)) {j : Y ⟶ X} {D : Fin m → (Y ⟶ O)}
    (H : IsCupInverse (a - ∑ r, Cc r ≫ B (Sum.inl r)) (fun n => B (Sum.inr n)) j D) :
    IsIso (gMap a B Cc (fun i r => if i = Sum.inl r then 𝟙 O else 0)) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := H
  have R1 : ∀ {Z : C} (g : X ⟶ Z), a ≫ j ≫ g = g + ∑ x, Cc x ≫ B (Sum.inl x) ≫ j ≫ g := by
    intro Z g
    have := congrArg (· ≫ g) h1
    block_norm at this
    rw [← sub_eq_zero] at this ⊢; rw [← this]; abel
  have R1' : a ≫ j = 𝟙 X + ∑ x, Cc x ≫ B (Sum.inl x) ≫ j := by simpa using R1 (𝟙 X)
  have R2 : ∀ (n : Fin m) {Z : C} (g : O ⟶ Z),
      a ≫ D n ≫ g = ∑ x, Cc x ≫ B (Sum.inl x) ≫ D n ≫ g := by
    intro n Z g
    have := congrArg (· ≫ g) (h2 n)
    block_norm at this
    exact sub_eq_zero.1 this
  have R2' : ∀ n : Fin m, a ≫ D n = ∑ x, Cc x ≫ B (Sum.inl x) ≫ D n := fun n => by
    simpa using R2 n (𝟙 O)
  have R5 : ∀ {Z : C} (g : Y ⟶ Z), j ≫ a ≫ g =
      g + ∑ x, j ≫ Cc x ≫ B (Sum.inl x) ≫ g - ∑ t, D t ≫ B (Sum.inr t) ≫ g := by
    intro Z g
    have := congrArg (· ≫ g) h5
    block_norm at this
    rw [← sub_eq_zero] at this ⊢; rw [← this]; abel
  have R5' : j ≫ a = 𝟙 Y + ∑ x, j ≫ Cc x ≫ B (Sum.inl x) - ∑ t, D t ≫ B (Sum.inr t) := by
    simpa using R5 (𝟙 Y)
  have h3' : ∀ t, B (Sum.inr t) ≫ j = 0 := h3
  have h4' : ∀ t n, B (Sum.inr t) ≫ D n = if t = n then 𝟙 O else 0 := h4
  refine ⟨gMap j (fun r => -(B (Sum.inl r) ≫ j))
    (Sum.elim (fun r => -(j ≫ Cc r)) D)
    (fun r => Sum.elim (fun r' => (if r = r' then 𝟙 O else 0) + B (Sum.inl r) ≫ j ≫ Cc r')
      (fun n => -(B (Sum.inl r) ≫ D n))), ?_, ?_⟩
  · rw [gMap_comp, gMap_id]
    refine gMap_congr ?_ ?_ ?_ ?_
    · block_norm; rw [R1']; abel
    · rintro (i | t)
      · block_norm; abel
      · block_norm; rw [h3']
    · rintro (i | t)
      · block_norm; rw [R1]; abel
      · block_norm; rw [R2']; abel
    · rintro (i | t) (i' | t')
      · block_norm; abel
      · block_norm; abel
      · block_norm; rw [← Category.assoc, h3']; simp
      · block_norm; rw [h4']
  · rw [gMap_comp, gMap_id]
    refine gMap_congr ?_ (fun r => ?_) (fun r => ?_) (fun r r' => ?_)
    · block_norm; rw [R5']; abel
    · block_norm; rw [R5']; block_norm; abel
    · block_norm; abel
    · block_norm; abel

/-- The permutation of the `O`-summands of `Y ⊕ Oᶥ` along `e : ι ≃ κ`. -/
def gReindex (Y O : C) (e : ι ≃ κ) : gObj Y O ι ⟶ gObj Y O κ :=
  gMap (𝟙 Y) (fun _ => 0) (fun _ => 0) (fun i r => if e i = r then 𝟙 O else 0)

lemma gMap_comp_gReindex {X Y O : C} (a : X ⟶ Y) (B : ι → (O ⟶ Y)) (Cc : κ → (X ⟶ O))
    (E : ι → κ → (O ⟶ O)) (e : κ ≃ μ) :
    gMap a B Cc E ≫ gReindex Y O e =
      gMap a B (fun r => Cc (e.symm r)) (fun i r => E i (e.symm r)) := by
  unfold gReindex
  rw [gMap_comp]
  refine gMap_congr (by simp) (fun i => by simp) (fun r => ?_) (fun i r => ?_) <;>
    simp [← Equiv.eq_symm_apply, comp_ite]

lemma gReindex_comp_gMap {X Y O : C} (a : X ⟶ Y) (B : ι → (O ⟶ Y)) (Cc : κ → (X ⟶ O))
    (E : ι → κ → (O ⟶ O)) (e : μ ≃ ι) :
    gReindex X O e ≫ gMap a B Cc E = gMap a (fun i => B (e i)) Cc (fun i r => E (e i) r) := by
  unfold gReindex
  rw [gMap_comp]
  refine gMap_congr (by simp) (fun i => by simp [ite_comp]) (fun r => by simp) (fun i r => by simp [ite_comp])

instance (Y O : C) (e : ι ≃ κ) : IsIso (gReindex Y O e) := by
  refine ⟨gReindex Y O e.symm, ?_, ?_⟩
  · rw [gReindex, gMap_comp_gReindex, gMap_id]
    refine gMap_congr rfl (fun _ => rfl) (fun _ => rfl) (fun i r => ?_)
    simp
  · rw [gReindex, gMap_comp_gReindex, gMap_id]
    refine gMap_congr rfl (fun _ => rfl) (fun _ => rfl) (fun i r => ?_)
    simp

/-- Reindexing the target summands `Oᵏ` along `e : κ ≃ μ` preserves invertibility. -/
lemma isIso_gMap_of_reindex_target {X Y O : C} (a : X ⟶ Y) (B : ι → (O ⟶ Y))
    (Cc : μ → (X ⟶ O)) (E : ι → μ → (O ⟶ O)) (e : κ ≃ μ)
    (H : IsIso (gMap a B (fun r => Cc (e r)) (fun i r => E i (e r)))) :
    IsIso (gMap a B Cc E) := by
  have := gMap_comp_gReindex a B (fun r => Cc (e r)) (fun i r => E i (e r)) e
  simp only [Equiv.apply_symm_apply] at this
  rw [← this]
  infer_instance

/-- Reindexing the source summands `Oᶥ` along `e : μ ≃ ι` preserves invertibility. -/
lemma isIso_gMap_of_reindex_source {X Y O : C} (a : X ⟶ Y) (B : ι → (O ⟶ Y))
    (Cc : κ → (X ⟶ O)) (E : ι → κ → (O ⟶ O)) (e : μ ≃ ι)
    (H : IsIso (gMap a (fun i => B (e i)) Cc (fun i r => E (e i) r))) :
    IsIso (gMap a B Cc E) := by
  rw [← gReindex_comp_gMap] at H
  exact IsIso.of_isIso_comp_left (gReindex X O e) _

end OddMath.QuiverHecke.SwappedAssembly.ProbeWindow
