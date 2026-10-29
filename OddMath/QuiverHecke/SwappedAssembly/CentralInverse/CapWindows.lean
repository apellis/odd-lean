/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.CategoryTheory.Preadditive.Mat
import Mathlib.CategoryTheory.Preadditive.Opposite
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.Windows

/-! # Shifted cap windows

The cap-window map `F = [s; v₀, …, v_{h-1}] : X ⟶ Y ⊕ Oʰ` of
`docs/Nondegeneracy/ProbeWindowInverse.md` (2) is a morphism of `Mat_ C`
(`ProbeWindow.capMap`), and a two-sided inverse of it is the same as an entrywise inverse
family `(j, A)` (`ProbeWindow.IsCapInverse`, `ProbeWindow.isIso_capMap_iff`).

Shifting the window by `l ≤ h` dots, `F_l = [s; v_{-l}, …, v_{h-l-1}]`, preserves
invertibility (`ProbeWindow.exists_isCapInverse_shift`, (5) there): the first window identity
(`ProbeWindow.window_neg`) says `x^{-l} ≫ F = F_l ≫ T` for a triangular matrix `T` whose
diagonal is `q^l y^{-l}` and the identity (`ProbeWindow.tri`).

Cup windows `P = [s, u₀, …, u_{h-1}] : X ⊕ Oʰ ⟶ Y` (`u_n = u ≫ yⁿ`, (3) there) have entrywise
inverses `ProbeWindow.IsCupInverse`, which are cap inverses in `Cᵒᵖ`
(`ProbeWindow.isCupInverse_iff_op`). In `Cᵒᵖ` the slide reads
`s ≫ x - q • (y ≫ s) = u ≫ (-q • v)`, so the cap shift gives (6) there:
`ProbeWindow.exists_isCupInverse_shift`.
-/

namespace OddMath.QuiverHecke.SwappedAssembly.ProbeWindow

open CategoryTheory

variable {C : Type*} [Category C] [Preadditive C]

/-- The target `Y ⊕ Oʰ` of a cap window, as an object of `Mat_ C`. -/
abbrev capObj (Y O : C) (h : ℕ) : Mat_ C where
  ι := Option (Fin h)
  X o := @Option.rec (Fin h) (fun _ => C) Y (fun _ => O) o

/-- A single object `X` as an object of `Mat_ C`. -/
abbrev oneObj (X : C) : Mat_ C where
  ι := PUnit
  X _ := X

/-- A morphism of `C` as a `1 × 1` matrix. -/
def oneMap {X X' : C} (f : X ⟶ X') : oneObj X ⟶ oneObj X' := fun _ _ => f

@[simp] lemma oneMap_apply {X X' : C} (f : X ⟶ X') (i j) : (oneMap f i j : X ⟶ X') = f := rfl

lemma oneMap_comp {X X' X'' : C} (f : X ⟶ X') (g : X' ⟶ X'') :
    oneMap f ≫ oneMap g = oneMap (f ≫ g) := by
  ext i k; rw [Mat_.comp_apply]; simp

lemma oneMap_id (X : C) : oneMap (𝟙 X) = 𝟙 (oneObj X) := by
  ext ⟨⟩ ⟨⟩; exact (Mat_.id_apply_self (oneObj X) PUnit.unit).symm

instance {X X' : C} (f : X ⟶ X') [IsIso f] : IsIso (oneMap f) :=
  ⟨oneMap (inv f), by rw [oneMap_comp, IsIso.hom_inv_id, oneMap_id],
    by rw [oneMap_comp, IsIso.inv_hom_id, oneMap_id]⟩

/-- The cap-window map `[s; w₀, …, w_{h-1}] : X ⟶ Y ⊕ Oʰ`. -/
def capMap {X Y O : C} {h : ℕ} (s : X ⟶ Y) (w : Fin h → (X ⟶ O)) :
    oneObj X ⟶ capObj Y O h :=
  fun _ o => match o with
    | none => s
    | some n => w n

/-- Entrywise two-sided inverse `(j, A)` of the cap-window map `[s; w]`. -/
def IsCapInverse {X Y O : C} {h : ℕ} (s : X ⟶ Y) (w : Fin h → (X ⟶ O)) (j : Y ⟶ X)
    (A : Fin h → (O ⟶ X)) : Prop :=
  j ≫ s = 𝟙 Y ∧ (∀ n, A n ≫ s = 0) ∧ (∀ m, j ≫ w m = 0) ∧
    (∀ n m, A n ≫ w m = if n = m then 𝟙 O else 0) ∧ s ≫ j + ∑ n, w n ≫ A n = 𝟙 X

/-- The map `Y ⊕ Oʰ ⟶ X` with entries `j` and `A`. -/
def capInv {X Y O : C} {h : ℕ} (j : Y ⟶ X) (A : Fin h → (O ⟶ X)) :
    capObj Y O h ⟶ oneObj X :=
  fun o _ => match o with
    | none => j
    | some n => A n

/-- A triangular endomorphism of `Y ⊕ Oʰ`: `a` on `Y`, the identity on `Oʰ`, and the
column `B : Oʰ ⟶ Y`. -/
def tri {Y O : C} {h : ℕ} (a : Y ⟶ Y) (B : Fin h → (O ⟶ Y)) : capObj Y O h ⟶ capObj Y O h :=
  fun o o' => match o, o' with
    | none, none => a
    | none, some _ => 0
    | some n, none => B n
    | some n, some m => if n = m then 𝟙 O else 0

section Entries

variable {X Y O : C} {h : ℕ}

@[simp] lemma capMap_none (s : X ⟶ Y) (w : Fin h → (X ⟶ O)) (i) :
    (capMap s w i none : X ⟶ Y) = s := rfl
@[simp] lemma capMap_some (s : X ⟶ Y) (w : Fin h → (X ⟶ O)) (i) (n : Fin h) :
    (capMap s w i (some n) : X ⟶ O) = w n := rfl
@[simp] lemma capInv_none (j : Y ⟶ X) (A : Fin h → (O ⟶ X)) (i) :
    (capInv j A none i : Y ⟶ X) = j := rfl
@[simp] lemma capInv_some (j : Y ⟶ X) (A : Fin h → (O ⟶ X)) (i) (n : Fin h) :
    (capInv j A (some n) i : O ⟶ X) = A n := rfl
@[simp] lemma tri_none_none (a : Y ⟶ Y) (B : Fin h → (O ⟶ Y)) :
    (tri a B none none : Y ⟶ Y) = a := rfl
@[simp] lemma tri_none_some (a : Y ⟶ Y) (B : Fin h → (O ⟶ Y)) (m : Fin h) :
    (tri a B none (some m) : Y ⟶ O) = 0 := rfl
@[simp] lemma tri_some_none (a : Y ⟶ Y) (B : Fin h → (O ⟶ Y)) (n : Fin h) :
    (tri a B (some n) none : O ⟶ Y) = B n := rfl
@[simp] lemma tri_some_some (a : Y ⟶ Y) (B : Fin h → (O ⟶ Y)) (n m : Fin h) :
    (tri a B (some n) (some m) : O ⟶ O) = if n = m then 𝟙 O else 0 := rfl

@[simp] lemma capObj_id_none : ((𝟙 (capObj Y O h) : capObj Y O h ⟶ _) none none : Y ⟶ Y) =
    𝟙 Y := Mat_.id_apply_self _ _
@[simp] lemma capObj_id_some (n m : Fin h) :
    ((𝟙 (capObj Y O h) : capObj Y O h ⟶ _) (some n) (some m) : O ⟶ O) =
      if n = m then 𝟙 O else 0 := by
  by_cases hnm : n = m
  · subst hnm; simp only [↓reduceIte]; exact Mat_.id_apply_self _ _
  · simp only [hnm, ↓reduceIte]; exact Mat_.id_apply_of_ne _ _ _ (by simpa using hnm)
@[simp] lemma capObj_id_none_some (m : Fin h) :
    ((𝟙 (capObj Y O h) : capObj Y O h ⟶ _) none (some m) : Y ⟶ O) = 0 :=
  Mat_.id_apply_of_ne _ _ _ (by simp)
@[simp] lemma capObj_id_some_none (n : Fin h) :
    ((𝟙 (capObj Y O h) : capObj Y O h ⟶ _) (some n) none : O ⟶ Y) = 0 :=
  Mat_.id_apply_of_ne _ _ _ (by simp)
@[simp] lemma oneObj_id (i j) :
    ((𝟙 (oneObj X) : oneObj X ⟶ _) i j : X ⟶ X) = 𝟙 X :=
  Mat_.id_apply_self _ _

end Entries

theorem tri_comp {Y O : C} {h : ℕ} (a a' : Y ⟶ Y) (B B' : Fin h → (O ⟶ Y)) :
    tri a B ≫ tri a' B' = tri (a ≫ a') (fun n => B n ≫ a' + B' n) := by
  ext o o'
  rw [Mat_.comp_apply, Fintype.sum_option]
  rcases o with _ | n <;> rcases o' with _ | m <;>
    simp [ite_comp]

theorem tri_id {Y O : C} {h : ℕ} : tri (𝟙 Y) (fun _ : Fin h => (0 : O ⟶ Y)) = 𝟙 _ := by
  ext o o'
  rcases o with _ | n <;> rcases o' with _ | m <;> simp

theorem isIso_tri {Y O : C} {h : ℕ} (a : Y ⟶ Y) [IsIso a] (B : Fin h → (O ⟶ Y)) :
    IsIso (tri a B) :=
  ⟨tri (inv a) (fun n => -(B n ≫ inv a)), by
    rw [tri_comp, IsIso.hom_inv_id]; simp only [add_neg_cancel]; exact tri_id, by
    rw [tri_comp, IsIso.inv_hom_id]
    simp only [Preadditive.neg_comp, Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      neg_add_cancel]
    exact tri_id⟩

theorem isIso_capMap_iff {X Y O : C} {h : ℕ} (s : X ⟶ Y) (w : Fin h → (X ⟶ O)) :
    IsIso (capMap s w) ↔ ∃ j A, IsCapInverse s w j A := by
  constructor
  · intro hF
    let G := inv (capMap s w)
    have h1 := IsIso.hom_inv_id (capMap s w)
    have h2 := IsIso.inv_hom_id (capMap s w)
    have e2 : ∀ o o', (inv (capMap s w) ≫ capMap s w) o o' =
        (𝟙 (capObj Y O h) : capObj Y O h ⟶ _) o o' := fun o o' => by rw [h2]
    have e1 : (capMap s w ≫ inv (capMap s w)) PUnit.unit PUnit.unit =
        (𝟙 (oneObj X) : oneObj X ⟶ _) PUnit.unit PUnit.unit := by rw [h1]
    simp only [Mat_.comp_apply, Fintype.univ_punit, Finset.sum_singleton] at e2
    rw [Mat_.comp_apply, Fintype.sum_option] at e1
    refine ⟨G none PUnit.unit, fun n => G (some n) PUnit.unit, ?_, ?_, ?_, ?_, ?_⟩
    · simpa using e2 none none
    · intro n; simpa using e2 (some n) none
    · intro m; simpa using e2 none (some m)
    · intro n m; simpa using e2 (some n) (some m)
    · simpa using e1
  · rintro ⟨j, A, hjs, hAs, hjw, hAw, hsum⟩
    refine ⟨capInv j A, ?_, ?_⟩
    · ext i i'
      rw [Mat_.comp_apply, Fintype.sum_option]
      simpa using hsum
    · ext o o'
      rw [Mat_.comp_apply]
      rcases o with _ | n <;> rcases o' with _ | m <;>
        simp [hjs, hAs, hjw, hAw]

omit [Preadditive C] in
private lemma zpow_hom_comp {Z : C} (a : Aut Z) (m n : ℤ) :
    (a ^ m).hom ≫ (a ^ n).hom = (a ^ (m + n)).hom := by
  rw [add_comm, zpow_add, Aut.Aut_mul_def]; rfl

omit [Preadditive C] in
private lemma zpow_zero_hom {Z : C} (a : Aut Z) : (a ^ (0 : ℤ)).hom = 𝟙 Z := by
  rw [zpow_zero]; rfl

omit [Preadditive C] in
private lemma zpow_one_hom {Z : C} (a : Aut Z) : (a ^ (1 : ℤ)).hom = a.hom := by
  rw [zpow_one]

omit [Preadditive C] in
private lemma zpow_hom_congr {Z : C} (a : Aut Z) {m n : ℤ} (h : m = n) :
    (a ^ m).hom = (a ^ n).hom := by
  rw [h]

variable {X Y O : C}

/-- The column correction of the shifted cap window: `x^{-l} ≫ s` in terms of `s ≫ y^{-l}`
and dotted cup-cap terms, the form of the first window identity used for (5) of
`ProbeWindowInverse.md`. -/
theorem neg_shift_comp (s : X ⟶ Y) (x : Aut X) (y : Aut Y) (v : X ⟶ O) (u : O ⟶ Y) (q : ℤ)
    (hslide : s ≫ y.hom - q • (x.hom ≫ s) = v ≫ u) (l : ℕ) :
    (x ^ (-(l : ℤ))).hom ≫ s = q ^ l • (s ≫ (y ^ (-(l : ℤ))).hom) +
      ∑ n ∈ Finset.range l, q ^ n •
        ((x ^ ((n : ℤ) - l)).hom ≫ v ≫ u ≫ (y ^ (-(n : ℤ) - 1)).hom) := by
  have hy : y.hom ≫ (y ^ (-1 : ℤ)).hom = 𝟙 Y := by
    have := zpow_hom_comp y 1 (-1)
    rw [zpow_one_hom, show (1 : ℤ) + -1 = 0 by norm_num, zpow_zero_hom] at this
    exact this
  have hx : (x ^ (-1 : ℤ)).hom ≫ x.hom = 𝟙 X := by
    have := zpow_hom_comp x (-1) 1
    rw [zpow_one_hom, show (-1 : ℤ) + 1 = 0 by norm_num, zpow_zero_hom] at this
    exact this
  have h1 : (x ^ (-1 : ℤ)).hom ≫ s =
      q • (s ≫ (y ^ (-1 : ℤ)).hom) + (x ^ (-1 : ℤ)).hom ≫ v ≫ u ≫ (y ^ (-1 : ℤ)).hom := by
    have hs : s ≫ y.hom = q • (x.hom ≫ s) + v ≫ u := by rw [← hslide]; abel
    have := congrArg (fun f => (x ^ (-1 : ℤ)).hom ≫ f ≫ (y ^ (-1 : ℤ)).hom) hs
    simp only [Preadditive.add_comp, Preadditive.zsmul_comp, Preadditive.comp_add,
      Preadditive.comp_zsmul, Category.assoc, hy, Category.comp_id] at this
    have hx' : ∀ {Z : C} (g : X ⟶ Z), (x ^ (-1 : ℤ)).hom ≫ x.hom ≫ g = g := fun g => by
      rw [← Category.assoc, hx, Category.id_comp]
    rw [hx'] at this
    exact this
  induction l with
  | zero =>
    simp only [Nat.cast_zero, neg_zero, zpow_zero_hom, Category.id_comp, Category.comp_id,
      pow_zero, one_smul, Finset.range_zero, Finset.sum_empty, add_zero]
  | succ l ih =>
    have e : (x ^ (-((l + 1 : ℕ) : ℤ))).hom = (x ^ (-1 : ℤ)).hom ≫ (x ^ (-(l : ℤ))).hom := by
      rw [zpow_hom_comp]; congr 2; push_cast; ring
    have t1 : (x ^ (-1 : ℤ)).hom ≫ s ≫ (y ^ (-(l : ℤ))).hom =
        q • (s ≫ (y ^ (-((l + 1 : ℕ) : ℤ))).hom) +
          (x ^ ((l : ℤ) - ((l + 1 : ℕ) : ℤ))).hom ≫ v ≫ u ≫ (y ^ (-(l : ℤ) - 1)).hom := by
      rw [← Category.assoc, h1, Preadditive.add_comp, Preadditive.zsmul_comp]
      simp only [Category.assoc, zpow_hom_comp]
      congr 1
      · rw [zpow_hom_congr y (show (-1 : ℤ) + -(l : ℤ) = -((l + 1 : ℕ) : ℤ) by push_cast; ring)]
      · rw [zpow_hom_congr x (show (-1 : ℤ) = (l : ℤ) - ((l + 1 : ℕ) : ℤ) by push_cast; ring),
          zpow_hom_congr y (show (-1 : ℤ) + -(l : ℤ) = -(l : ℤ) - 1 by ring)]
    have t2 : ∀ n ∈ Finset.range l, (x ^ (-1 : ℤ)).hom ≫ (q ^ n •
        ((x ^ ((n : ℤ) - l)).hom ≫ v ≫ u ≫ (y ^ (-(n : ℤ) - 1)).hom)) =
        q ^ n • ((x ^ ((n : ℤ) - ((l + 1 : ℕ) : ℤ))).hom ≫ v ≫ u ≫
          (y ^ (-(n : ℤ) - 1)).hom) := by
      intro n _
      rw [Preadditive.comp_zsmul, ← Category.assoc, zpow_hom_comp,
        zpow_hom_congr x (show (-1 : ℤ) + ((n : ℤ) - l) = (n : ℤ) - ((l + 1 : ℕ) : ℤ) by
          push_cast; ring)]
    rw [e, Category.assoc, ih, Preadditive.comp_add, Preadditive.comp_zsmul, t1,
      Preadditive.comp_sum, Finset.sum_congr rfl t2, Finset.sum_range_succ, smul_add,
      smul_smul, ← pow_succ]
    abel

/-- **Shifted cap windows**, (5) of `ProbeWindowInverse.md`: if the cap window
`[s; v₀, …, v_{h-1}]` (`v_n = xⁿ ≫ v`) is invertible, so is `[s; v_{-l}, …, v_{h-l-1}]` for
every `l ≤ h`. -/
theorem exists_isCapInverse_shift (s : X ⟶ Y) (x : Aut X) (y : Aut Y) (v : X ⟶ O) (u : O ⟶ Y)
    (q : ℤ) (hq : q * q = 1) (hslide : s ≫ y.hom - q • (x.hom ≫ s) = v ≫ u) {h l : ℕ}
    (hl : l ≤ h) (h0 : ∃ j A, IsCapInverse s (fun n : Fin h => (x ^ (n : ℤ)).hom ≫ v) j A) :
    ∃ j A, IsCapInverse s (fun n : Fin h => (x ^ ((n : ℤ) - l)).hom ≫ v) j A := by
  rw [← isIso_capMap_iff] at h0 ⊢
  let B : Fin h → (O ⟶ Y) := fun n =>
    if (n : ℕ) < l then q ^ (n : ℕ) • (u ≫ (y ^ (-(n : ℤ) - 1)).hom) else 0
  have hql : q ^ l * q ^ l = 1 := by rw [← mul_pow, hq, one_pow]
  have ha : IsIso (q ^ l • (y ^ (-(l : ℤ))).hom) :=
    ⟨q ^ l • (y ^ (l : ℤ)).hom, by
      rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, hql, one_smul,
        zpow_hom_comp, neg_add_cancel, zpow_zero_hom], by
      rw [Preadditive.zsmul_comp, Preadditive.comp_zsmul, smul_smul, hql, one_smul,
        zpow_hom_comp, add_neg_cancel, zpow_zero_hom]⟩
  have hT := isIso_tri (q ^ l • (y ^ (-(l : ℤ))).hom) B
  have key : oneMap (x ^ (-(l : ℤ))).hom ≫
      capMap s (fun n : Fin h => (x ^ (n : ℤ)).hom ≫ v) =
      capMap s (fun n : Fin h => (x ^ ((n : ℤ) - l)).hom ≫ v) ≫
        tri (q ^ l • (y ^ (-(l : ℤ))).hom) B := by
    ext ⟨⟩ o
    rcases o with _ | m
    · simp only [Mat_.comp_apply, Fintype.sum_option, Fintype.univ_punit,
        Finset.sum_singleton, oneMap_apply, capMap_none, capMap_some, tri_none_none, tri_some_none]
      rw [neg_shift_comp s x y v u q hslide l]
      congr 1
      · rw [Preadditive.comp_zsmul]
      simp only [B]
      rw [Fin.sum_univ_eq_sum_range
        (fun n => ((x ^ ((n : ℤ) - l)).hom ≫ v) ≫
          (if n < l then q ^ n • (u ≫ (y ^ (-(n : ℤ) - 1)).hom) else 0)) h,
        ← Finset.sum_range_add_sum_Ico _ hl]
      rw [Finset.sum_eq_zero (s := Finset.Ico l h) (fun n hn => by
        rw [Finset.mem_Ico] at hn; simp [not_lt.mpr hn.1]), add_zero]
      refine Finset.sum_congr rfl fun n hn => ?_
      rw [Finset.mem_range] at hn
      simp [hn, Preadditive.comp_zsmul]
    · simp only [Mat_.comp_apply, Fintype.sum_option, Fintype.univ_punit,
        Finset.sum_singleton, oneMap_apply, capMap_none, capMap_some, tri_none_some, tri_some_some]
      rw [Finset.sum_eq_single m (fun b _ hb => by simp only [hb, ↓reduceIte, Limits.comp_zero])
        (by simp), ← Category.assoc, zpow_hom_comp]
      simp only [↓reduceIte, Category.comp_id]
      rw [zpow_hom_congr x (neg_add_eq_sub _ _), Limits.comp_zero, zero_add]
  have hcap : capMap s (fun n : Fin h => (x ^ ((n : ℤ) - l)).hom ≫ v) =
      oneMap (x ^ (-(l : ℤ))).hom ≫
        capMap s (fun n : Fin h => (x ^ (n : ℤ)).hom ≫ v) ≫
          inv (tri (q ^ l • (y ^ (-(l : ℤ))).hom) B) := by
    rw [← Category.assoc, key, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have : IsIso (x ^ (-(l : ℤ))).hom := Iso.isIso_hom (X := X) (Y := X) (x ^ (-(l : ℤ)))
  rw [hcap]
  infer_instance


/-! ### Shifted cup windows, by duality -/

section Cup

open Opposite

/-- Entrywise two-sided inverse `[j; D]` of the cup-window map `[s, w₀, …, w_{h-1}] :
X ⊕ Oʰ ⟶ Y`, (3) of `ProbeWindowInverse.md` in execution order. -/
def IsCupInverse {X Y O : C} {h : ℕ} (s : X ⟶ Y) (w : Fin h → (O ⟶ Y)) (j : Y ⟶ X)
    (D : Fin h → (Y ⟶ O)) : Prop :=
  s ≫ j = 𝟙 X ∧ (∀ n, s ≫ D n = 0) ∧ (∀ m, w m ≫ j = 0) ∧
    (∀ m n, w m ≫ D n = if m = n then 𝟙 O else 0) ∧ j ≫ s + ∑ n, D n ≫ w n = 𝟙 Y

omit [Preadditive C] in
private lemma op_eq_iff {X Y : C} (f g : X ⟶ Y) : f.op = g.op ↔ f = g :=
  ⟨fun h => Quiver.Hom.op_inj h, fun h => h ▸ rfl⟩

/-- A cup inverse is a cap inverse in the opposite category. -/
lemma isCupInverse_iff_op {X Y O : C} {h : ℕ} (s : X ⟶ Y) (w : Fin h → (O ⟶ Y)) (j : Y ⟶ X)
    (D : Fin h → (Y ⟶ O)) :
    IsCupInverse s w j D ↔
      IsCapInverse s.op (fun n => (w n).op) j.op (fun n => (D n).op) := by
  have e1 : j.op ≫ s.op = 𝟙 (op X) ↔ s ≫ j = 𝟙 X := op_eq_iff (s ≫ j) (𝟙 X)
  have e2 : ∀ n, (D n).op ≫ s.op = 0 ↔ s ≫ D n = 0 := fun n => op_eq_iff (s ≫ D n) 0
  have e3 : ∀ m, j.op ≫ (w m).op = 0 ↔ w m ≫ j = 0 := fun m => op_eq_iff (w m ≫ j) 0
  have e4 : ∀ n m, ((D n).op ≫ (w m).op = if n = m then 𝟙 (op O) else 0) ↔
      (w m ≫ D n = if m = n then 𝟙 O else 0) := fun n m => by
    by_cases hnm : n = m
    · subst hnm; simp only [↓reduceIte]; exact op_eq_iff (w n ≫ D n) (𝟙 O)
    · have hmn : ¬ m = n := fun h => hnm h.symm
      simp only [hnm, hmn, ↓reduceIte]; exact op_eq_iff (w m ≫ D n) 0
  have e5 : s.op ≫ j.op + ∑ n, (w n).op ≫ (D n).op = 𝟙 (op Y) ↔
      j ≫ s + ∑ n, D n ≫ w n = 𝟙 Y := by
    rw [← op_eq_iff (j ≫ s + ∑ n, D n ≫ w n) (𝟙 Y), op_add, op_sum]
    rfl
  unfold IsCupInverse IsCapInverse
  rw [e1, e5]
  simp only [e2, e3, e4]
  constructor
  · rintro ⟨a, b, c, d, e⟩; exact ⟨a, b, c, fun n m => d m n, e⟩
  · rintro ⟨a, b, c, d, e⟩; exact ⟨a, b, c, fun m n => d n m, e⟩

/-- An automorphism of `Y` as an automorphism of `op Y`. -/
def autOp {Y : C} (y : Aut Y) : Aut (op Y) := Iso.op y

omit [Preadditive C] in
@[simp] lemma autOp_hom {Y : C} (y : Aut Y) : (autOp y).hom = y.hom.op := rfl

omit [Preadditive C] in
private lemma aut_mul_hom {Z : C} (a b : Aut Z) : (a * b).hom = b.hom ≫ a.hom := rfl

omit [Preadditive C] in
private lemma aut_inv_hom {Z : C} (a : Aut Z) : (a⁻¹).hom = a.inv := rfl

omit [Preadditive C] in
lemma autOp_zpow_hom {Y : C} (y : Aut Y) (k : ℤ) :
    (autOp y ^ k).hom = ((y ^ k).hom).op := by
  induction k using Int.induction_on with
  | zero => rw [zpow_zero_hom, zpow_zero_hom, op_id]
  | succ i ih =>
    rw [zpow_add_one, aut_mul_hom, ih, autOp_hom, ← op_comp,
      ← zpow_one_hom y, zpow_hom_comp]
  | pred i ih =>
    rw [zpow_sub_one, aut_mul_hom, ih, aut_inv_hom]
    change y.inv.op ≫ _ = _
    rw [← op_comp, show y.inv = (y ^ (-1 : ℤ)).hom by rw [zpow_neg_one, aut_inv_hom],
      zpow_hom_comp, zpow_hom_congr y (show -(i : ℤ) + -1 = -(i : ℤ) - 1 by ring)]

/-- **Shifted cup windows**, (6) of `ProbeWindowInverse.md`: if the cup window
`[s, u₀, …, u_{h-1}]` (`u_n = u ≫ yⁿ`) is invertible, so is `[s, u_{-l}, …, u_{h-l-1}]` for
every `l ≤ h`. This is `exists_isCapInverse_shift` in the opposite category, with the slide
`s ≫ x - q • (y ≫ s) = u ≫ (-q • v)` there. -/
theorem exists_isCupInverse_shift (s : X ⟶ Y) (x : Aut X) (y : Aut Y) (v : X ⟶ O) (u : O ⟶ Y)
    (q : ℤ) (hq : q * q = 1) (hslide : s ≫ y.hom - q • (x.hom ≫ s) = v ≫ u) {h l : ℕ}
    (hl : l ≤ h) (h0 : ∃ j D, IsCupInverse s (fun n : Fin h => u ≫ (y ^ (n : ℤ)).hom) j D) :
    ∃ j D, IsCupInverse s (fun n : Fin h => u ≫ (y ^ ((n : ℤ) - l)).hom) j D := by
  have hslide' : s.op ≫ (autOp x).hom - q • ((autOp y).hom ≫ s.op) = u.op ≫ (-q • v.op) := by
    apply Quiver.Hom.unop_inj
    change x.hom ≫ s - q • (s ≫ y.hom) = (-q • v) ≫ u
    rw [Preadditive.zsmul_comp, ← hslide, smul_sub, smul_smul, neg_mul, hq]
    simp only [neg_smul, one_smul]
    abel
  obtain ⟨j, D, hjD⟩ := h0
  obtain ⟨j', A', h'⟩ := exists_isCapInverse_shift s.op (autOp y) (autOp x) u.op (-q • v.op) q
    hq hslide' hl ⟨j.op, fun n => (D n).op, by
      rw [isCupInverse_iff_op] at hjD
      convert hjD using 2
      simp only [autOp_zpow_hom, op_comp]⟩
  refine ⟨j'.unop, fun n => (A' n).unop, ?_⟩
  rw [isCupInverse_iff_op]
  convert h' using 2 <;> simp only [autOp_zpow_hom, op_comp, Quiver.Hom.op_unop]

end Cup

end OddMath.QuiverHecke.SwappedAssembly.ProbeWindow
