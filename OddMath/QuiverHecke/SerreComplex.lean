/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SerreWords
import OddMath.QuiverHecke.SplitComplex

/-!
# The categorical Serre complex

Brundan–Ellis, arXiv:1701.04133v2, Proposition 11.2 (Hill–Wang, arXiv:1202.2769v2,
Theorem 5.9), in the quiver Hecke supercategory `H`. For colours `i ≠ j` and `M = d_ij + 1`
let `word a = i^a j i^{M-a}` (`0 ≤ a ≤ M`, read from the left) with the idempotent
`e a = 1_{i^{(a)}} ⊗ 1_j ⊗ 1_{i^{(M-a)}}`, the product of the longest Demazure products of its
two colour blocks. The maps

* `upMap a : word a → word (a + 1)`: `e_a`, then the crossing of `j` with the `i` to its right,
  then that `i` carried to the left end;
* `downMap a : word (a + 1) → word a`: `e_{a+1}`, then the crossing of the `i` left of `j` with
  `j`, then that `i` carried to the right end,

satisfy `upMap a ≫ upMap (a + 1) = 0`, `downMap (a + 1) ≫ downMap a = 0` and
`e_a = c⁺ (upMap a ≫ downMap a) + c⁻ (downMap (a - 1) ≫ upMap (a - 1))` for units `c⁺`, `c⁻`
(one term at the ends). The proof is the Khovanov–Lauda computation: the composites differ by
the correction term of the braid relation (1.9) on `i j i`, of which only the term
`t_ij x^{a-1} z^{M-a-1}` survives the annihilators of HW Lemma 5.8; at the ends the double
crossing (1.7) does the same. Bar-consistency of the parameters is not needed.
-/

noncomputable section
open scoped Classical
namespace OddMath.QuiverHecke.SerreComplex
open CategoryTheory StringDiagrams OddMath.QuiverHecke
open SKM (zsign)
open SignedNilHecke
open Categorification.KLR.KL2.NH (wp Wb chL chR)
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X) {k : Type w}
  [CommRing k] (Sc : SKM.Scalars D k)

/-! ## The words -/

section Words

variable (i j : I) (M : ℕ)

/-- The word `i^a j i^{M-a}`. -/
def word (a : ℕ) : List I := List.replicate a i ++ [j] ++ List.replicate (M - a) i

variable {i j M}

theorem length_word {a : ℕ} (ha : a ≤ M) : (word i j M a).length = M + 1 := by
  simp [word]; omega

theorem word_lt {a p : ℕ} (hp : p < a) : (word i j M a)[p]? = some i := by
  simp [word, List.getElem?_append_left, hp]

theorem word_self (a : ℕ) : (word i j M a)[a]? = some j := by
  simp [word]

theorem word_gt {a p : ℕ} (hp : a < p) (hpM : p ≤ M) : (word i j M a)[p]? = some i := by
  simp only [word, List.append_assoc, List.singleton_append]
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_replicate]
  rw [show p - a = (p - a - 1) + 1 by omega, List.getElem?_cons_succ, List.getElem?_replicate]
  simp; omega

theorem word_up {a : ℕ} (ha : a < M) :
    word i j M a = List.replicate a i ++ [j, i] ++ List.replicate (M - a - 1) i := by
  simp only [word, List.append_assoc, List.cons_append, List.nil_append]
  congr 2
  rw [show M - a = (M - a - 1) + 1 by omega, List.replicate_succ, Nat.add_sub_cancel]

theorem word_down (a : ℕ) :
    word i j M (a + 1) = List.replicate a i ++ [i, j] ++ List.replicate (M - a - 1) i := by
  simp only [word, List.replicate_succ', List.append_assoc, List.cons_append, List.nil_append]
  congr 3

theorem sChain_up {a : ℕ} (ha : a < M) :
    SChain (word i j M a) (pl (word i j M a) [.cross a]) (word i j M (a + 1)) :=
  sChain_ofShape' (List.replicate a i) (List.replicate (M - a - 1) i) (.cross j i) (word_up ha)
    (word_down a) (by simp)

theorem sChain_down {a : ℕ} (ha : a < M) :
    SChain (word i j M (a + 1)) (pl (word i j M (a + 1)) [.cross a]) (word i j M a) :=
  sChain_ofShape' (List.replicate a i) (List.replicate (M - a - 1) i) (.cross i j)
    (word_down a) (word_up ha) (by simp)

end Words

/-! ## Blocks, idempotents and maps -/

section Maps

variable (i j : I) (M : ℕ)

/-- The object of `H` of the word `i^a j i^{M-a}`. -/
abbrev wobj (a : ℕ) : H D Sc := (pres D Sc).obj (ob D (word i j M a))

/-- Dots on `i^a j i^{M-a}`. -/
abbrev xw (a : ℕ) : ℕ → End (wobj D Sc i j M a) := dotE D Sc (word i j M a)

/-- Crossings on `i^a j i^{M-a}`. -/
abbrev tw (a : ℕ) : ℕ → End (wobj D Sc i j M a) := crossE D Sc (word i j M a)

/-- The sign of the colour `i`. -/
abbrev eps : ℤˣ := zunit (D.parity i)

/-- `1_{i^{(a)}} ⊗ 1_{j i^{M-a}}`. -/
def lIdem (a : ℕ) : End (wobj D Sc i j M a) :=
  idem (eps D i) 0 a (xw D Sc i j M a) (tw D Sc i j M a) 0 a

/-- `1_{i^a j} ⊗ 1_{i^{(M-a)}}`. -/
def rIdem (a : ℕ) : End (wobj D Sc i j M a) :=
  idem (eps D i) (a + 1) (M - a) (xw D Sc i j M a) (tw D Sc i j M a) (a + 1) (M - a)

/-- `e_a = 1_{i^{(a)}} ⊗ 1_j ⊗ 1_{i^{(M-a)}}`. -/
def eIdem (a : ℕ) : End (wobj D Sc i j M a) := lIdem D Sc i j M a * rIdem D Sc i j M a

/-- The crossing of `j` with the `i` to its right. -/
def up {a : ℕ} (ha : a < M) : wobj D Sc i j M a ⟶ wobj D Sc i j M (a + 1) :=
  cl D Sc _ _ [.cross a] (sChain_up ha)

/-- The crossing of the `i` left of `j` with `j`. -/
def down {a : ℕ} (ha : a < M) : wobj D Sc i j M (a + 1) ⟶ wobj D Sc i j M a :=
  cl D Sc _ _ [.cross a] (sChain_down ha)

variable {D Sc i j M}

theorem family_of_eq {w : List I} (pre post : List I) (x : I) (n s : ℕ)
    (hw : w = pre ++ List.replicate n x ++ post) (hs : pre.length = s) :
    IsSignedNilHeckeFamily (zunit (D.parity x)) s n (dotE D Sc w) (crossE D Sc w) := by
  subst hw hs
  exact isSignedNilHeckeFamily_block D Sc pre post x n

theorem leftFamily (a : ℕ) :
    IsSignedNilHeckeFamily (eps D i) 0 a (xw D Sc i j M a) (tw D Sc i j M a) :=
  family_of_eq [] ([j] ++ List.replicate (M - a) i) i a 0 (by simp [word]) rfl

theorem rightFamily (a : ℕ) :
    IsSignedNilHeckeFamily (eps D i) (a + 1) (M - a) (xw D Sc i j M a) (tw D Sc i j M a) :=
  family_of_eq (List.replicate a i ++ [j]) [] i (M - a) (a + 1) (by simp [word]) (by simp)

end Maps

/-! ## Transport of the block idempotents -/

section Transport

variable {D Sc i j M}

theorem l_up {a : ℕ} (ha : a < M) :
    Slides (up D Sc i j M ha) 1 (lIdem D Sc i j M a)
      (idem (eps D i) 0 (a + 1) (xw D Sc i j M (a + 1)) (tw D Sc i j M (a + 1)) 0 a) := by
  unfold up lIdem
  exact slides_idem_gen D Sc (sChain_up ha) (x := i) le_rfl (by omega) le_rfl (by omega)
    (fun p _ hp => word_lt (by omega)) (fun p _ hp => word_lt (by omega))
    (Or.inl (by rw [PG.pos_cross]; omega))
    (by rw [PG.pos_cross, PG.width_cross, length_word ha.le]; omega)

theorem r_up {a : ℕ} (ha : a < M) :
    Slides (up D Sc i j M ha) 1
      (idem (eps D i) (a + 1) (M - a) (xw D Sc i j M a) (tw D Sc i j M a) (a + 1 + 1)
        (M - (a + 1)))
      (rIdem D Sc i j M (a + 1)) := by
  unfold up rIdem
  exact slides_idem_gen D Sc (sChain_up ha) (x := i) (by omega) (by omega) le_rfl le_rfl
    (fun p hp hp' => word_gt (by omega) (by omega)) (fun p hp hp' => word_gt (by omega) (by omega))
    (Or.inr (by rw [PG.pos_cross, PG.width_cross]))
    (by rw [PG.pos_cross, PG.width_cross, length_word ha.le]; omega)

theorem l_down {a : ℕ} (ha : a < M) :
    Slides (down D Sc i j M ha) 1
      (idem (eps D i) 0 (a + 1) (xw D Sc i j M (a + 1)) (tw D Sc i j M (a + 1)) 0 a)
      (lIdem D Sc i j M a) := by
  unfold down lIdem
  exact slides_idem_gen D Sc (sChain_down ha) (x := i) le_rfl (by omega) le_rfl (by omega)
    (fun p _ hp => word_lt (by omega)) (fun p _ hp => word_lt (by omega))
    (Or.inl (by rw [PG.pos_cross]; omega))
    (by rw [PG.pos_cross, PG.width_cross, length_word (by omega : a + 1 ≤ M)]; omega)

theorem r_down {a : ℕ} (ha : a < M) :
    Slides (down D Sc i j M ha) 1 (rIdem D Sc i j M (a + 1))
      (idem (eps D i) (a + 1) (M - a) (xw D Sc i j M a) (tw D Sc i j M a) (a + 1 + 1)
        (M - (a + 1))) := by
  unfold down rIdem
  exact slides_idem_gen D Sc (sChain_down ha) (x := i) le_rfl le_rfl (by omega) (by omega)
    (fun p hp hp' => word_gt (by omega) (by omega)) (fun p hp hp' => word_gt (by omega) (by omega))
    (Or.inr (by rw [PG.pos_cross, PG.width_cross]))
    (by rw [PG.pos_cross, PG.width_cross, length_word (by omega : a + 1 ≤ M)]; omega)

end Transport

/-! ## Commutation inside a word -/

section Inside

variable {D Sc i j M}

/-- The right block idempotent commutes with the left one. -/
theorem r_slides_l (a : ℕ) (ha : a ≤ M) :
    Slides (rIdem D Sc i j M a) 1 (lIdem D Sc i j M a) (lIdem D Sc i j M a) := by
  unfold rIdem lIdem
  exact slides_idem_idem D Sc (x := i) (y := i) le_rfl le_rfl (fun p _ hp => word_lt (by omega))
    (fun p hp hp' => word_gt (by omega) (by omega)) (Or.inl (by omega))

/-- A sub-block idempotent of the right block commutes with the left one. -/
theorem rs_slides_l (a : ℕ) (ha : a < M) :
    Slides (idem (B := End (wobj D Sc i j M a)) (eps D i) (a + 1) (M - a) (xw D Sc i j M a)
      (tw D Sc i j M a) (a + 1 + 1) (M - (a + 1))) 1 (lIdem D Sc i j M a)
      (lIdem D Sc i j M a) := by
  unfold lIdem
  exact slides_idem_idem D Sc (x := i) (y := i) le_rfl le_rfl (fun p _ hp => word_lt (by omega))
    (fun p hp hp' => word_gt (by omega) (by omega)) (Or.inl (by omega))

theorem lIdem_mul_rIdem_comm (a : ℕ) (ha : a ≤ M) :
    rIdem D Sc i j M a * lIdem D Sc i j M a = lIdem D Sc i j M a * rIdem D Sc i j M a := by
  have h := (r_slides_l (D := D) (Sc := Sc) (i := i) (j := j) a ha).eq_of_one
  rwa [← End.mul_def, ← End.mul_def] at h

theorem eIdem_eq_comp (a : ℕ) :
    eIdem D Sc i j M a = rIdem D Sc i j M a ≫ lIdem D Sc i j M a := rfl

theorem lIdem_idem (a : ℕ) : lIdem D Sc i j M a * lIdem D Sc i j M a = lIdem D Sc i j M a :=
  (leftFamily a).idem_mul_idem 0 a

theorem rIdem_idem (a : ℕ) : rIdem D Sc i j M a * rIdem D Sc i j M a = rIdem D Sc i j M a :=
  (rightFamily a).idem_mul_idem (a + 1) (M - a)

theorem eIdem_eq_comp' (a : ℕ) (ha : a ≤ M) :
    eIdem D Sc i j M a = lIdem D Sc i j M a ≫ rIdem D Sc i j M a := by
  rw [eIdem, ← lIdem_mul_rIdem_comm a ha, End.mul_def]

theorem eIdem_idem (a : ℕ) (ha : a ≤ M) :
    eIdem D Sc i j M a * eIdem D Sc i j M a = eIdem D Sc i j M a := by
  unfold eIdem
  rw [mul_assoc, ← mul_assoc (rIdem D Sc i j M a), lIdem_mul_rIdem_comm a ha, mul_assoc,
    rIdem_idem, ← mul_assoc, lIdem_idem]

end Inside

/-! ## The maps of the complex -/

section Complex

variable (i j : I) (M : ℕ)

/-- `upMap a : i^a j i^{M-a} → i^{a+1} j i^{M-a-1}`: `e_a`, the crossing of `j` with the `i` to
its right, and that `i` carried to the left end. -/
def upMap {a : ℕ} (ha : a < M) : wobj D Sc i j M a ⟶ wobj D Sc i j M (a + 1) :=
  eIdem D Sc i j M a ≫ up D Sc i j M ha ≫
    chL (B := End (wobj D Sc i j M (a + 1))) (tw D Sc i j M (a + 1)) 0 a

/-- `downMap a : i^{a+1} j i^{M-a-1} → i^a j i^{M-a}`: `e_{a+1}`, the crossing of the `i` left
of `j` with `j`, and that `i` carried to the right end. -/
def downMap {a : ℕ} (ha : a < M) : wobj D Sc i j M (a + 1) ⟶ wobj D Sc i j M a :=
  eIdem D Sc i j M (a + 1) ≫ down D Sc i j M ha ≫
    chR (B := End (wobj D Sc i j M a)) (tw D Sc i j M a) (a + 1) (M - (a + 1))

variable {D Sc i j M}

theorem chL_slides_r {a : ℕ} (ha : a < M) :
    Slides (chL (B := End (wobj D Sc i j M (a + 1))) (tw D Sc i j M (a + 1)) 0 a) 1 (rIdem D Sc i j M (a + 1))
      (rIdem D Sc i j M (a + 1)) := by
  unfold rIdem chL
  exact slides_idem_wp D Sc (x := i) (y := i) _ le_rfl le_rfl
    (fun p hp hp' => word_gt (by omega) (by omega)) fun q hq => by
      rw [List.mem_range'_1] at hq
      exact ⟨word_lt (by omega), word_lt (by omega), Or.inr (by omega)⟩

theorem chR_slides_l {a : ℕ} (ha : a < M) :
    Slides (chR (B := End (wobj D Sc i j M a)) (tw D Sc i j M a) (a + 1) (M - (a + 1))) 1 (lIdem D Sc i j M a)
      (lIdem D Sc i j M a) := by
  unfold lIdem chR
  exact slides_idem_wp D Sc (x := i) (y := i) _ le_rfl le_rfl
    (fun p _ hp => word_lt (by omega)) fun q hq => by
      rw [List.mem_reverse, List.mem_range'_1] at hq
      exact ⟨word_gt (by omega) (by omega), word_gt (by omega) (by omega), Or.inl (by omega)⟩

/-- `e_a` absorbs the sub-block idempotent `1_{i^a j i} ⊗ 1_{i^{(M-a-1)}}`. -/
theorem eIdem_comp_rs {a : ℕ} (ha : a < M) :
    eIdem D Sc i j M a ≫
        idem (B := End (wobj D Sc i j M a)) (eps D i) (a + 1) (M - a) (xw D Sc i j M a)
          (tw D Sc i j M a) (a + 1 + 1) (M - (a + 1)) = eIdem D Sc i j M a := by
  have h₁ := (rs_slides_l (D := D) (Sc := Sc) (i := i) (j := j) a ha).eq_of_one
  have h₂ := (rightFamily (D := D) (Sc := Sc) (i := i) (j := j) (M := M) a).idem_succ_mul_idem_succ
    (a + 1) (M - (a + 1))
  rw [show M - (a + 1) + 1 = M - a by omega] at h₂
  rw [← End.mul_def, ← End.mul_def] at h₁
  rw [← End.mul_def, eIdem, ← mul_assoc, h₁, mul_assoc]
  unfold rIdem
  rw [h₂]

/-- `e_{a+1}` absorbs the sub-block idempotent `1_{i^{(a)}} ⊗ 1_{i j i^{M-a-1}}`. -/
theorem eIdem_comp_ls (a : ℕ) :
    eIdem D Sc i j M (a + 1) ≫
        idem (B := End (wobj D Sc i j M (a + 1))) (eps D i) 0 (a + 1) (xw D Sc i j M (a + 1))
          (tw D Sc i j M (a + 1)) 0 a = eIdem D Sc i j M (a + 1) := by
  have h₂ := (leftFamily (D := D) (Sc := Sc) (i := i) (j := j) (M := M) (a + 1)).idem_mul_idem_succ
    0 a
  rw [← End.mul_def, eIdem, ← mul_assoc]
  unfold lIdem
  rw [h₂]

/-- `upMap a` ends in `e_{a+1}` (HW (5.25)–(5.26)). -/
theorem upMap_comp_eIdem {a : ℕ} (ha : a < M) :
    upMap D Sc i j M ha ≫ eIdem D Sc i j M (a + 1) = upMap D Sc i j M ha := by
  have hc := (chL_slides_r (D := D) (Sc := Sc) (i := i) (j := j) ha).eq_of_one
  have hc' := (leftFamily (D := D) (Sc := Sc) (i := i) (j := j) (M := M) (a + 1)).idem_mul_chL_mul_idem
    (s' := 0) (l := a) le_rfl (by omega)
  simp only [End.mul_def, Category.assoc] at hc'
  unfold upMap
  rw [eIdem_eq_comp (a + 1)]
  simp only [Category.assoc]
  rw [← reassoc_of% hc, ← (r_up ha).comp_eq, ← Category.assoc (eIdem D Sc i j M a),
    eIdem_comp_rs ha, eIdem_eq_comp a]
  simp only [Category.assoc]
  rw [(l_up ha).comp_eq, (l_up ha).comp_eq]
  unfold lIdem
  rw [hc']

/-- `downMap a` ends in `e_a` (HW (5.25), (5.27)). -/
theorem downMap_comp_eIdem {a : ℕ} (ha : a < M) :
    downMap D Sc i j M ha ≫ eIdem D Sc i j M a = downMap D Sc i j M ha := by
  have hc := (chR_slides_l (D := D) (Sc := Sc) (i := i) (j := j) ha).eq_of_one
  have hc' := (rightFamily (D := D) (Sc := Sc) (i := i) (j := j) (M := M) a).idem_mul_chR_mul_idem
    (s' := a + 1) (l := M - (a + 1)) le_rfl (by omega)
  rw [show M - (a + 1) + 1 = M - a by omega] at hc'
  simp only [End.mul_def, Category.assoc] at hc'
  unfold downMap
  rw [eIdem_eq_comp' a ha.le]
  simp only [Category.assoc]
  rw [← reassoc_of% hc, ← (l_down ha).comp_eq, ← Category.assoc (eIdem D Sc i j M (a + 1)),
    eIdem_comp_ls, eIdem_eq_comp' (a + 1) ha]
  simp only [Category.assoc]
  rw [(r_down ha).comp_eq, (r_down ha).comp_eq]
  unfold rIdem
  rw [hc']

/-- The left chain of `upMap a` passes through the next crossing `up`, up to a sign. -/
theorem chL_slides_up {a : ℕ} (ha : a + 1 < M) :
    ∃ u : ℤˣ, Slides (up D Sc i j M ha) u
      (chL (B := End (wobj D Sc i j M (a + 1))) (tw D Sc i j M (a + 1)) 0 a)
      (chL (B := End (wobj D Sc i j M (a + 1 + 1))) (tw D Sc i j M (a + 1 + 1)) 0 a) := by
  unfold up chL
  exact ⟨_, slides_wp_gen D Sc (sChain_up ha) (x := i) _ (fun q hq => by
    rw [List.mem_range'_1] at hq
    exact ⟨word_lt (by omega), word_lt (by omega), word_lt (by omega), word_lt (by omega),
      Or.inl (by rw [PG.pos_cross]; omega)⟩)
    (by rw [PG.pos_cross, PG.width_cross, length_word ha.le]; omega)⟩

/-- `braid_ne` on words given up to equality. -/
theorem cl_braid_of {w w' : List I} (l r : List I) (x y z : I) (hb : ¬(x = z ∧ x ≠ y))
    (hw : w = l ++ [x, y, z] ++ r) (hw' : w' = l ++ [z, y, x] ++ r) {p : ℕ}
    (hp : l.length = p) {gs hs : List PG} (hgs : gs = [.cross p, .cross (p + 1), .cross p])
    (hhs : hs = [.cross (p + 1), .cross p, .cross (p + 1)]) (h₁ : SChain w (pl w gs) w')
    (h₂ : SChain w (pl w hs) w') : cl D Sc w w' gs h₁ = cl D Sc w w' hs h₂ := by
  subst hw hw' hp hgs hhs
  exact braid_ne D Sc l r x y z hb h₁ h₂

/-- The braid relation on `i^a j i i`: two crossings of `j` with the `i`s to its right, preceded
by the crossing of those `i`s, are followed by the crossing of the `i`s. -/
theorem braid_up {a : ℕ} (ha : a + 1 < M) :
    tw D Sc i j M a (a + 1) ≫ up D Sc i j M (Nat.lt_of_succ_lt ha) ≫ up D Sc i j M ha =
      up D Sc i j M (Nat.lt_of_succ_lt ha) ≫ up D Sc i j M ha ≫
        tw D Sc i j M (a + 1 + 1) a := by
  have hT := sChain_cross_of (word_gt (i := i) (j := j) (M := M) (a := a) (p := a + 1)
    (by omega) (by omega)) (word_gt (by omega) (by omega))
  have hT' := sChain_cross_of (word_lt (i := i) (j := j) (M := M) (a := a + 1 + 1) (p := a)
    (by omega)) (word_lt (by omega))
  have e₁ : word i j M a = List.replicate a i ++ [j, i, i] ++ List.replicate (M - a - 2) i := by
    rw [word_up (by omega)]
    rw [show M - a - 1 = (M - a - 2) + 1 by omega, List.replicate_succ]
    simp
  have e₂ : word i j M (a + 1 + 1) =
      List.replicate a i ++ [i, i, j] ++ List.replicate (M - a - 2) i := by
    simp only [word, List.replicate_succ', List.append_assoc, List.cons_append,
      List.nil_append]
    congr 4
  unfold tw crossE up
  rw [genE_eq D Sc hT, genE_eq D Sc hT', cl_comp, cl_comp, cl_comp, cl_comp]
  symm
  exact cl_braid_of _ _ j i i (fun h => h.2 h.1) e₁ e₂ (by simp) rfl rfl _ _

/-- `e_a` is fixed by the Demazure element on the first two strands of its right block. -/
theorem eIdem_comp_dem {a : ℕ} (ha : a + 1 < M) :
    eIdem D Sc i j M a ≫
        dem (B := End (wobj D Sc i j M a)) (eps D i) (a + 1) (M - a) (xw D Sc i j M a)
          (tw D Sc i j M a) (a + 1) = eIdem D Sc i j M a := by
  have h := (rightFamily (D := D) (Sc := Sc) (i := i) (j := j) (M := M) a).dem_mul_idem
    (j := a + 1) (s' := a + 1) (n' := M - a) le_rfl (by omega)
  rw [eIdem_eq_comp' a (by omega), Category.assoc]
  congr 1

/-- `upMap (a + 1) ∘ upMap a = 0`. -/
theorem upMap_comp_upMap {a : ℕ} (ha : a + 1 < M) :
    upMap D Sc i j M (Nat.lt_of_succ_lt ha) ≫ upMap D Sc i j M ha = 0 := by
  obtain ⟨u, hu⟩ := chL_slides_up (D := D) (Sc := Sc) (i := i) (j := j) ha
  have hb := braid_up (D := D) (Sc := Sc) (i := i) (j := j) ha
  have hsq : tw D Sc i j M (a + 1 + 1) a ≫
      chL (B := End (wobj D Sc i j M (a + 1 + 1))) (tw D Sc i j M (a + 1 + 1)) 0 a ≫
        chL (B := End (wobj D Sc i j M (a + 1 + 1))) (tw D Sc i j M (a + 1 + 1)) 0 (a + 1) =
      0 := by
    have h := (leftFamily (D := D) (Sc := Sc) (i := i) (j := j) (M := M) (a + 1 + 1)).chL_mul_chL
      (p := 0) (l := a + 1) le_rfl (by omega) (by omega)
    nth_rw 2 [Categorification.KLR.KL2.NH.chL_succ'] at h
    simpa only [zero_add, End.mul_def, Category.assoc] using h
  have hD := eIdem_comp_dem (D := D) (Sc := Sc) (i := i) (j := j) ha
  rw [dem_of le_rfl (by omega)] at hD
  change eIdem D Sc i j M a ≫ (-((eps D i : ℤ) • (xw D Sc i j M a (a + 1 + 1) ≫
    tw D Sc i j M a (a + 1)))) = eIdem D Sc i j M a at hD
  simp only [Preadditive.comp_neg, Preadditive.comp_zsmul] at hD
  rw [show upMap D Sc i j M ha = eIdem D Sc i j M (a + 1) ≫ up D Sc i j M ha ≫
    chL (B := End (wobj D Sc i j M (a + 1 + 1))) (tw D Sc i j M (a + 1 + 1)) 0 (a + 1) from rfl,
    ← Category.assoc, upMap_comp_eIdem]
  unfold upMap
  simp only [Category.assoc]
  rw [reassoc_of% hu]
  simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc]
  rw [← hD]
  simp only [Preadditive.neg_comp, Preadditive.zsmul_comp, Category.assoc]
  rw [reassoc_of% hb, hsq]
  simp

/-- The right chain of `downMap (a + 1)` passes through the next crossing `down`, up to a
sign. -/
theorem chR_slides_down {a : ℕ} (ha : a < M) :
    ∃ u : ℤˣ, Slides (down D Sc i j M ha) u
      (chR (B := End (wobj D Sc i j M (a + 1))) (tw D Sc i j M (a + 1)) (a + 1 + 1)
        (M - (a + 1 + 1)))
      (chR (B := End (wobj D Sc i j M a)) (tw D Sc i j M a) (a + 1 + 1) (M - (a + 1 + 1))) := by
  unfold down chR
  exact ⟨_, slides_wp_gen D Sc (sChain_down ha) (x := i) _ (fun q hq => by
    rw [List.mem_reverse, List.mem_range'_1] at hq
    exact ⟨word_gt (by omega) (by omega), word_gt (by omega) (by omega),
      word_gt (by omega) (by omega), word_gt (by omega) (by omega),
      Or.inr (by rw [PG.pos_cross, PG.width_cross]; omega)⟩)
    (by rw [PG.pos_cross, PG.width_cross, length_word (by omega : a + 1 ≤ M)]; omega)⟩

/-- The braid relation on `i^a i i j`. -/
theorem braid_down {a : ℕ} (ha : a + 1 < M) :
    tw D Sc i j M (a + 1 + 1) a ≫ down D Sc i j M ha ≫ down D Sc i j M (Nat.lt_of_succ_lt ha) =
      down D Sc i j M ha ≫ down D Sc i j M (Nat.lt_of_succ_lt ha) ≫
        tw D Sc i j M a (a + 1) := by
  have hT := sChain_cross_of (word_lt (i := i) (j := j) (M := M) (a := a + 1 + 1) (p := a)
    (by omega)) (word_lt (by omega))
  have hT' := sChain_cross_of (word_gt (i := i) (j := j) (M := M) (a := a) (p := a + 1)
    (by omega) (by omega)) (word_gt (by omega) (by omega))
  have e₁ : word i j M (a + 1 + 1) =
      List.replicate a i ++ [i, i, j] ++ List.replicate (M - a - 2) i := by
    simp only [word, List.replicate_succ', List.append_assoc, List.cons_append,
      List.nil_append]
    congr 4
  have e₂ : word i j M a = List.replicate a i ++ [j, i, i] ++ List.replicate (M - a - 2) i := by
    rw [word_up (by omega)]
    rw [show M - a - 1 = (M - a - 2) + 1 by omega, List.replicate_succ]
    simp
  unfold tw crossE down
  rw [genE_eq D Sc hT, genE_eq D Sc hT', cl_comp, cl_comp, cl_comp, cl_comp]
  exact cl_braid_of _ _ i i j (fun h => h.2 rfl) e₁ e₂ (by simp) rfl rfl _ _

/-- `e_{a+2}` is fixed by the Demazure element on the last two strands of its left block. -/
theorem eIdem_comp_demL (a : ℕ) :
    eIdem D Sc i j M (a + 1 + 1) ≫
        dem (B := End (wobj D Sc i j M (a + 1 + 1))) (eps D i) 0 (a + 1 + 1)
          (xw D Sc i j M (a + 1 + 1)) (tw D Sc i j M (a + 1 + 1)) a =
      eIdem D Sc i j M (a + 1 + 1) := by
  have h := (leftFamily (D := D) (Sc := Sc) (i := i) (j := j) (M := M) (a + 1 + 1)).dem_mul_idem
    (j := a) (s' := 0) (n' := a + 1 + 1) (Nat.zero_le _) (by omega)
  rw [eIdem_eq_comp, Category.assoc]
  congr 1

/-- `downMap a ∘ downMap (a + 1) = 0`. -/
theorem downMap_comp_downMap {a : ℕ} (ha : a + 1 < M) :
    downMap D Sc i j M ha ≫ downMap D Sc i j M (Nat.lt_of_succ_lt ha) = 0 := by
  obtain ⟨u, hu⟩ := chR_slides_down (D := D) (Sc := Sc) (i := i) (j := j) (Nat.lt_of_succ_lt ha)
  have hb := braid_down (D := D) (Sc := Sc) (i := i) (j := j) ha
  have hsq : tw D Sc i j M a (a + 1) ≫
      chR (B := End (wobj D Sc i j M a)) (tw D Sc i j M a) (a + 1 + 1) (M - (a + 1 + 1)) ≫
        chR (B := End (wobj D Sc i j M a)) (tw D Sc i j M a) (a + 1) (M - (a + 1)) = 0 := by
    have h := (rightFamily (D := D) (Sc := Sc) (i := i) (j := j) (M := M) a).chR_mul_chR
      (p := a + 1) (l := M - (a + 1)) le_rfl (by omega) (by omega)
    rw [show M - (a + 1) = M - (a + 1 + 1) + 1 by omega] at h
    nth_rw 2 [Categorification.KLR.KL2.NH.chR_succ] at h
    rw [show M - (a + 1 + 1) + 1 = M - (a + 1) by omega] at h
    simpa only [End.mul_def, Category.assoc] using h
  have hD := eIdem_comp_demL (D := D) (Sc := Sc) (i := i) (j := j) (M := M) a
  rw [dem_of (Nat.zero_le _) (by omega)] at hD
  change eIdem D Sc i j M (a + 1 + 1) ≫ (-((eps D i : ℤ) • (xw D Sc i j M (a + 1 + 1) (a + 1) ≫
    tw D Sc i j M (a + 1 + 1) a))) = eIdem D Sc i j M (a + 1 + 1) at hD
  simp only [Preadditive.comp_neg, Preadditive.comp_zsmul] at hD
  rw [show downMap D Sc i j M (Nat.lt_of_succ_lt ha) = eIdem D Sc i j M (a + 1) ≫
    down D Sc i j M (Nat.lt_of_succ_lt ha) ≫
      chR (B := End (wobj D Sc i j M a)) (tw D Sc i j M a) (a + 1) (M - (a + 1)) from rfl,
    ← Category.assoc, downMap_comp_eIdem]
  unfold downMap
  simp only [Category.assoc]
  rw [reassoc_of% hu]
  simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc]
  rw [← hD]
  simp only [Preadditive.neg_comp, Preadditive.zsmul_comp, Category.assoc]
  rw [reassoc_of% hb, hsq]
  simp

end Complex

end OddMath.QuiverHecke.SerreComplex
