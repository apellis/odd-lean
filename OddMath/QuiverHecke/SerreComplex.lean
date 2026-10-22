/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SerreWords
import OddMath.QuiverHecke.SplitComplex
import OddMath.QuiverHecke.DividedPowerModules

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


/-! ## The splitting -/

section Annihilation

open SignedNilHecke

/-- The annihilator computation of HW Lemma 5.8 on two blocks: `A`, `Bm` are the chains of the
left and right blocks with idempotents `L`, `R`, and `x`, `z` the dots that HW Lemma 5.8 pairs
with them. A monomial `x^p y^q z^r` with an exponent below its bound is killed. -/
theorem ann_mono_zero {B : Type*} [Ring B] {A Bm L R x y z : B} {cL cR : ℤ} {m n : ℕ}
    (hA : ∀ p ≤ m, A * (x ^ p * L) = if p = m then cL • L else 0)
    (hB : ∀ r ≤ n, Bm * (z ^ r * R) = if r = n then cR • R else 0)
    (zL : ∀ r, z ^ r * L = L * z ^ r) (yL : ∀ q, y ^ q * L = L * y ^ q)
    (BA : SignComm Bm A) (Bx : ∀ p, SignComm Bm (x ^ p)) (BL : Bm * L = L * Bm)
    (By : ∀ q, SignComm Bm (y ^ q)) {p q r : ℕ} (h : p < m ∨ r < n) :
    Bm * A * (x ^ p * y ^ q * z ^ r) * (L * R) = 0 := by
  simp only [mul_assoc]
  rw [← mul_assoc (z ^ r) L, zL, mul_assoc L, ← mul_assoc (y ^ q) L, yL, mul_assoc L]
  rcases h with h | h
  · rw [← mul_assoc (x ^ p) L, ← mul_assoc A, hA p h.le, ite_eq_right (by omega), zero_mul,
      mul_zero]
  · have hc : SignComm Bm (A * (x ^ p * (L * y ^ q))) :=
      BA.mul_right ((Bx p).mul_right (SignComm.mul_right (⟨1, by rw [BL]; simp⟩ : SignComm Bm L)
        (By q)))
    obtain ⟨u, hu⟩ := hc
    have e : A * (x ^ p * (L * (y ^ q * (z ^ r * R)))) =
        A * (x ^ p * (L * y ^ q)) * (z ^ r * R) := by simp only [mul_assoc]
    rw [e, ← mul_assoc Bm, hu, smul_mul_assoc, mul_assoc, hB r h.le, ite_eq_right (by omega),
      mul_zero, smul_zero]

/-- The surviving monomial of HW Lemma 5.8 on two blocks. -/
theorem ann_mono_top {B : Type*} [Ring B] {A Bm L R x z : B} {cL cR : ℤ} {m n : ℕ}
    (hA : ∀ p ≤ m, A * (x ^ p * L) = if p = m then cL • L else 0)
    (hB : ∀ r ≤ n, Bm * (z ^ r * R) = if r = n then cR • R else 0)
    (zL : ∀ r, z ^ r * L = L * z ^ r) (BL : Bm * L = L * Bm) :
    Bm * A * (x ^ m * z ^ n) * (L * R) = (cL * cR) • (L * R) := by
  simp only [mul_assoc]
  rw [← mul_assoc (z ^ n) L, zL, mul_assoc L, ← mul_assoc (x ^ m) L, ← mul_assoc A,
    hA m le_rfl, ite_eq_left rfl, smul_mul_assoc, mul_smul_comm, ← mul_assoc Bm, BL, mul_assoc,
    hB n le_rfl, ite_eq_left rfl, mul_smul_comm, smul_smul]

end Annihilation


section Commuting

open SignedNilHecke

variable {w : List I}

theorem length_of_getElem? {p : ℕ} {x : I} (h : w[p]? = some x) : p < w.length := by
  by_contra hc
  rw [List.getElem?_eq_none (by omega)] at h
  simp at h

theorem signComm_cross_cross {q q' : ℕ} {x y : I} (hq : q + 2 ≤ q') (h₀ : w[q]? = some x)
    (h₁ : w[q + 1]? = some x) (h₀' : w[q']? = some y) (h₁' : w[q' + 1]? = some y) :
    SignComm (crossE D Sc w q) (crossE D Sc w q') :=
  signComm_genE D Sc (by rw [PG.pos_cross, PG.width_cross, PG.pos_cross]; omega)
    (by have := length_of_getElem? h₁'; rw [PG.pos_cross, PG.width_cross]; omega)
    (sChain_cross_of h₀ h₁) (sChain_cross_of h₀' h₁')

theorem signComm_dot_cross {p q' : ℕ} {y : I} (hq : p + 1 ≤ q') (h₀' : w[q']? = some y)
    (h₁' : w[q' + 1]? = some y) : SignComm (dotE D Sc w p) (crossE D Sc w q') :=
  signComm_genE D Sc (by rw [PG.pos_dot, PG.width_dot, PG.pos_cross]; omega)
    (by have := length_of_getElem? h₁'; rw [PG.pos_cross, PG.width_cross]; omega)
    (sChain_pl w _) (sChain_cross_of h₀' h₁')

theorem signComm_cross_dot {q p : ℕ} {x y : I} (hq : q + 2 ≤ p) (h₀ : w[q]? = some x)
    (h₁ : w[q + 1]? = some x) (hp : w[p]? = some y) :
    SignComm (crossE D Sc w q) (dotE D Sc w p) :=
  signComm_genE D Sc (by rw [PG.pos_dot, PG.width_cross, PG.pos_cross]; omega)
    (by have := length_of_getElem? hp; rw [PG.pos_dot, PG.width_dot]; omega)
    (sChain_cross_of h₀ h₁) (sChain_pl w _)

end Commuting

section Interior

open SignedNilHecke

variable {D Sc i j M}

/-- HW Lemma 5.8 on the left block of `i^{b+1} j i^{M-b-1}`. -/
theorem ann_left {b : ℕ} (p : ℕ) (hp : p ≤ b) :
    chL (tw D Sc i j M (b + 1)) 0 b * (xw D Sc i j M (b + 1) b ^ p * lIdem D Sc i j M (b + 1)) =
      if p = b then ((-1 : ℤ) ^ b * (eps D i : ℤ) ^ (b + 1).choose 2) • lIdem D Sc i j M (b + 1)
      else 0 := by
  have h := (leftFamily (D := D) (Sc := Sc) (i := i) (j := j) (M := M) (b + 1)).chL_mul_x_pow_mul_idem
    (s' := 0) (l := b) (a := p) le_rfl (by omega) hp
  rw [zero_add] at h
  exact h

/-- HW Lemma 5.8 on the right block of `i^{b+1} j i^{M-b-1}`. -/
theorem ann_right {b : ℕ} (hb : b + 1 < M) (r : ℕ) (hr : r ≤ M - (b + 1 + 1)) :
    chR (tw D Sc i j M (b + 1)) (b + 1 + 1) (M - (b + 1 + 1)) *
        (xw D Sc i j M (b + 1) (b + 1 + 1) ^ r * rIdem D Sc i j M (b + 1)) =
      if r = M - (b + 1 + 1) then
        ((eps D i : ℤ) ^ (M - (b + 1 + 1)).choose 2) • rIdem D Sc i j M (b + 1)
      else 0 := by
  have h := (rightFamily (D := D) (Sc := Sc) (i := i) (j := j) (M := M) (b + 1)).chR_mul_x_pow_mul_idem
    (s' := b + 1 + 1) (l := M - (b + 1 + 1)) (a := r) le_rfl (by omega) hr
  rw [show M - (b + 1 + 1) + 1 = M - (b + 1) by omega] at h
  exact h

theorem pow_comm_lIdem {b : ℕ} (hb : b + 1 ≤ M) {p : ℕ} (hp : b + 1 ≤ p) (hpM : p ≤ M)
    (r : ℕ) :
    xw D Sc i j M (b + 1) p ^ r * lIdem D Sc i j M (b + 1) =
      lIdem D Sc i j M (b + 1) * xw D Sc i j M (b + 1) p ^ r := by
  have h := slides_idem_genE D Sc (sChain_pl (word i j M (b + 1)) [.dot p]) (x := i)
    (ε := eps D i) (s := 0) (n := b + 1) (t := 0) (m := b + 1) le_rfl le_rfl
    (fun q _ hq => word_lt (by omega)) (Or.inl (by rw [PG.pos_dot]; omega))
    (by rw [PG.pos_dot, PG.width_dot, length_word (by omega)]; omega)
  have h₂ := h.powσ r
  rw [one_pow] at h₂
  exact h₂.eq_of_one

theorem chR_comm_lIdem {b : ℕ} (hb : b + 1 < M) :
    chR (tw D Sc i j M (b + 1)) (b + 1 + 1) (M - (b + 1 + 1)) * lIdem D Sc i j M (b + 1) =
      lIdem D Sc i j M (b + 1) * chR (tw D Sc i j M (b + 1)) (b + 1 + 1) (M - (b + 1 + 1)) := by
  have h := slides_idem_wp D Sc (w := word i j M (b + 1)) (x := i) (y := i) (ε := eps D i)
    (s := 0) (n := b + 1) (t := 0) (m := b + 1) (List.range' (b + 1 + 1) (M - (b + 1 + 1))).reverse
    le_rfl le_rfl (fun q _ hq => word_lt (by omega)) fun q hq => by
      rw [List.mem_reverse, List.mem_range'_1] at hq
      exact ⟨word_gt (by omega) (by omega), word_gt (by omega) (by omega), Or.inl (by omega)⟩
  exact h.eq_of_one

theorem signComm_chR_dot {b : ℕ} (hb : b + 1 < M) {p : ℕ} (hp : p ≤ b + 1) (e : ℕ) :
    SignComm (chR (tw D Sc i j M (b + 1)) (b + 1 + 1) (M - (b + 1 + 1)))
      (xw D Sc i j M (b + 1) p ^ e) := by
  unfold chR
  refine ((SignComm.wp fun q hq => ?_).pow_left e).symm
  rw [List.mem_reverse, List.mem_range'_1] at hq
  exact signComm_dot_cross D Sc (by omega) (word_gt (by omega) (by omega))
    (word_gt (by omega) (by omega))

theorem signComm_chR_chL {b : ℕ} (hb : b + 1 < M) :
    SignComm (chR (tw D Sc i j M (b + 1)) (b + 1 + 1) (M - (b + 1 + 1)))
      (chL (tw D Sc i j M (b + 1)) 0 b) := by
  unfold chR chL
  refine SignComm.wp fun q hq => (SignComm.wp fun q' hq' => ?_).symm
  rw [List.mem_range'_1] at hq
  rw [List.mem_reverse, List.mem_range'_1] at hq'
  exact signComm_cross_cross D Sc (by omega) (word_lt (by omega)) (word_lt (by omega))
    (word_gt (by omega) (by omega)) (word_gt (by omega) (by omega))

/-- In the interior, a monomial `x^p y^q z^r` (dots on the strands left of, on, and right of `j`)
with `p` or `r` below its bound is killed by the two chains and `e`. -/
theorem interior_ann_zero {b : ℕ} (hb : b + 1 < M) {p q r : ℕ}
    (h : p < b ∨ r < M - (b + 1 + 1)) :
    chR (tw D Sc i j M (b + 1)) (b + 1 + 1) (M - (b + 1 + 1)) * chL (tw D Sc i j M (b + 1)) 0 b *
        (xw D Sc i j M (b + 1) b ^ p * xw D Sc i j M (b + 1) (b + 1) ^ q *
          xw D Sc i j M (b + 1) (b + 1 + 1) ^ r) * eIdem D Sc i j M (b + 1) = 0 :=
  ann_mono_zero ann_left (ann_right hb) (pow_comm_lIdem hb.le (by omega) (by omega))
    (pow_comm_lIdem hb.le le_rfl (by omega)) (signComm_chR_chL hb)
    (signComm_chR_dot hb (by omega)) (chR_comm_lIdem hb) (signComm_chR_dot hb le_rfl) h

/-- The surviving monomial `x^b z^{M-b-2}` gives a sign times `e`. -/
theorem interior_ann_top {b : ℕ} (hb : b + 1 < M) :
    ∃ c : ℤˣ, chR (tw D Sc i j M (b + 1)) (b + 1 + 1) (M - (b + 1 + 1)) *
        chL (tw D Sc i j M (b + 1)) 0 b *
        (xw D Sc i j M (b + 1) b ^ b * xw D Sc i j M (b + 1) (b + 1 + 1) ^ (M - (b + 1 + 1))) *
          eIdem D Sc i j M (b + 1) = (c : ℤ) • eIdem D Sc i j M (b + 1) := by
  refine ⟨(-1) ^ b * eps D i ^ (b + 1).choose 2 * eps D i ^ (M - (b + 1 + 1)).choose 2, ?_⟩
  rw [eIdem, ann_mono_top ann_left (ann_right hb) (pow_comm_lIdem hb.le (by omega) (by omega))
    (chR_comm_lIdem hb)]
  push_cast
  ring_nf

/-- The left part of the left chain passes through `down`, up to a sign. -/
theorem chL_slides_down {a b : ℕ} (ha : a < M) (hb : b + 1 ≤ a) :
    ∃ u : ℤˣ, Slides (down D Sc i j M ha) u
      (chL (B := End (wobj D Sc i j M (a + 1))) (tw D Sc i j M (a + 1)) 0 b)
      (chL (B := End (wobj D Sc i j M a)) (tw D Sc i j M a) 0 b) := by
  unfold down chL
  exact ⟨_, slides_wp_gen D Sc (sChain_down ha) (x := i) _ (fun q hq => by
    rw [List.mem_range'_1] at hq
    exact ⟨word_lt (by omega), word_lt (by omega), word_lt (by omega), word_lt (by omega),
      Or.inl (by rw [PG.pos_cross]; omega)⟩)
    (by rw [PG.pos_cross, PG.width_cross, length_word (by omega : a + 1 ≤ M)]; omega)⟩

/-- The right part of the right chain passes through `up`, up to a sign. -/
theorem chR_slides_up {a : ℕ} (ha : a < M) :
    ∃ u : ℤˣ, Slides (up D Sc i j M ha) u
      (chR (B := End (wobj D Sc i j M a)) (tw D Sc i j M a) (a + 1 + 1) (M - (a + 1 + 1)))
      (chR (B := End (wobj D Sc i j M (a + 1))) (tw D Sc i j M (a + 1)) (a + 1 + 1)
        (M - (a + 1 + 1))) := by
  unfold up chR
  exact ⟨_, slides_wp_gen D Sc (sChain_up ha) (x := i) _ (fun q hq => by
    rw [List.mem_reverse, List.mem_range'_1] at hq
    exact ⟨word_gt (by omega) (by omega), word_gt (by omega) (by omega),
      word_gt (by omega) (by omega), word_gt (by omega) (by omega),
      Or.inr (by rw [PG.pos_cross, PG.width_cross]; omega)⟩)
    (by rw [PG.pos_cross, PG.width_cross, length_word ha.le]; omega)⟩

/-- `braid_iji` on words given up to equality. -/
theorem cl_braid_iji_of {w : List I} (l r : List I) (hij : i ≠ j)
    (hw : w = l ++ [i, j, i] ++ r) {p : ℕ} (hp : l.length = p) {gs hs : List PG}
    (hgs : gs = [.cross p, .cross (p + 1), .cross p])
    (hhs : hs = [.cross (p + 1), .cross p, .cross (p + 1)]) (h₁ : SChain w (pl w gs) w)
    (h₂ : SChain w (pl w hs) w) :
    cl D Sc w w gs h₁ - cl D Sc w w hs h₂ =
      ∑ s ∈ Finset.range (D.dn i j),
          (zsign k (D.parity i * (D.parity j + s)) * (Sc.t i j : k)) •
            (dotE D Sc w p ^ (D.dn i j - 1 - s) * dotE D Sc w (p + 2) ^ s) +
        ∑ p' ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
          ∑ s ∈ Finset.range p', (zsign k (D.parity i * (D.parity j + s)) * Sc.s i j p' q) •
            (dotE D Sc w p ^ (p' - 1 - s) * dotE D Sc w (p + 1) ^ q *
              dotE D Sc w (p + 2) ^ s) := by
  subst hw hp hgs hhs
  exact braid_iji D Sc l r hij h₁ h₂

/-- (1.9) on the strands `b, b+1, b+2` (colours `i j i`) of `i^{b+1} j i^{M-b-1}`, through the
neighbouring words. -/
theorem braid_iji_word (hij : i ≠ j) {b : ℕ} (hb : b + 1 < M) :
    down D Sc i j M (Nat.lt_of_succ_lt hb) ≫ tw D Sc i j M b (b + 1) ≫
          up D Sc i j M (Nat.lt_of_succ_lt hb) -
        up D Sc i j M hb ≫ tw D Sc i j M (b + 1 + 1) b ≫ down D Sc i j M hb =
      ∑ s ∈ Finset.range (D.dn i j),
          (zsign k (D.parity i * (D.parity j + s)) * (Sc.t i j : k)) •
            (xw D Sc i j M (b + 1) b ^ (D.dn i j - 1 - s) *
              xw D Sc i j M (b + 1) (b + 1 + 1) ^ s) +
        ∑ p' ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
          ∑ s ∈ Finset.range p', (zsign k (D.parity i * (D.parity j + s)) * Sc.s i j p' q) •
            (xw D Sc i j M (b + 1) b ^ (p' - 1 - s) * xw D Sc i j M (b + 1) (b + 1) ^ q *
              xw D Sc i j M (b + 1) (b + 1 + 1) ^ s) := by
  have hT := sChain_cross_of (word_gt (i := i) (j := j) (M := M) (a := b) (p := b + 1)
    (by omega) (by omega)) (word_gt (by omega) (by omega))
  have hT' := sChain_cross_of (word_lt (i := i) (j := j) (M := M) (a := b + 1 + 1) (p := b)
    (by omega)) (word_lt (by omega))
  have e : word i j M (b + 1) = List.replicate b i ++ [i, j, i] ++ List.replicate (M - b - 2) i := by
    rw [word_down b, show M - b - 1 = (M - b - 2) + 1 by omega, List.replicate_succ]
    simp
  unfold tw crossE up down
  rw [genE_eq D Sc hT, genE_eq D Sc hT', cl_comp, cl_comp, cl_comp, cl_comp]
  exact cl_braid_iji_of _ _ hij e (by simp) rfl rfl _ _

/-- The correction term of (1.9), between the two chains, is a unit times `e`. -/
theorem interior_corr (hij : i ≠ j) (hM : M = D.dn i j + 1) {b : ℕ} (hb : b + 1 < M) :
    ∃ γ : k, IsUnit γ ∧
      eIdem D Sc i j M (b + 1) ≫
          (down D Sc i j M (Nat.lt_of_succ_lt hb) ≫ tw D Sc i j M b (b + 1) ≫
              up D Sc i j M (Nat.lt_of_succ_lt hb) -
            up D Sc i j M hb ≫ tw D Sc i j M (b + 1 + 1) b ≫ down D Sc i j M hb) ≫
          chL (B := End (wobj D Sc i j M (b + 1))) (tw D Sc i j M (b + 1)) 0 b ≫
          chR (B := End (wobj D Sc i j M (b + 1))) (tw D Sc i j M (b + 1)) (b + 1 + 1)
            (M - (b + 1 + 1)) = γ • eIdem D Sc i j M (b + 1) := by
  obtain ⟨c, hc⟩ := interior_ann_top (D := D) (Sc := Sc) (i := i) (j := j) hb
  refine ⟨zsign k (D.parity i * (D.parity j + ((M - (b + 1 + 1) : ℕ) : ZMod 2))) *
    (Sc.t i j : k) * ((c : ℤ) : k), ?_, ?_⟩
  · refine ((IsUnit.of_mul_eq_one _ (zsign_mul_self _)).mul (Sc.t i j).isUnit).mul ?_
    exact c.isUnit.map (Int.castRingHom k)
  rw [braid_iji_word hij hb]
  change chR (tw D Sc i j M (b + 1)) (b + 1 + 1) (M - (b + 1 + 1)) *
    chL (tw D Sc i j M (b + 1)) 0 b * (_ + _) * eIdem D Sc i j M (b + 1) = _
  simp only [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm, smul_mul_assoc]
  rw [Finset.sum_eq_zero (s := Finset.Ioo 0 (D.dn i j)) fun p' hp' =>
    Finset.sum_eq_zero fun q _ => Finset.sum_eq_zero fun s hs => by
      rw [Finset.mem_Ioo] at hp'
      rw [Finset.mem_range] at hs
      have h0 := interior_ann_zero (D := D) (Sc := Sc) (i := i) (j := j) hb (p := p' - 1 - s)
        (q := q) (r := s) (by omega)
      rw [h0, smul_zero], add_zero,
    Finset.sum_eq_single (M - (b + 1 + 1))]
  · rw [show D.dn i j - 1 - (M - (b + 1 + 1)) = b by omega, hc, ← Int.cast_smul_eq_zsmul k,
      smul_smul]
  · intro s hs hne
    rw [Finset.mem_range] at hs
    have h0 := interior_ann_zero (D := D) (Sc := Sc) (i := i) (j := j) hb (p := D.dn i j - 1 - s)
      (q := 0) (r := s) (by omega)
    simp only [pow_zero, mul_one] at h0
    rw [h0, smul_zero]
  · intro h
    rw [Finset.mem_range] at h
    omega

theorem intCast_units_mul_self (u : ℤˣ) : ((u : ℤ) : k) * ((u : ℤ) : k) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]

/-- HW Theorem 5.9 in the interior: `e_{b+1}` is a combination of the two composites through
the neighbouring words. -/
theorem split_interior (hij : i ≠ j) (hM : M = D.dn i j + 1) {b : ℕ} (hb : b + 1 < M) :
    ∃ cp cm : k, eIdem D Sc i j M (b + 1) =
      cp • (upMap D Sc i j M hb ≫ downMap D Sc i j M hb) +
        cm • (downMap D Sc i j M (Nat.lt_of_succ_lt hb) ≫
          upMap D Sc i j M (Nat.lt_of_succ_lt hb)) := by
  obtain ⟨γ, hγ, hcorr⟩ := interior_corr (D := D) (Sc := Sc) hij hM hb
  obtain ⟨u, hu⟩ := chL_slides_down (D := D) (Sc := Sc) (i := i) (j := j) (a := b + 1) (b := b)
    hb le_rfl
  obtain ⟨u', hu'⟩ := chR_slides_up (D := D) (Sc := Sc) (i := i) (j := j) (a := b)
    (Nat.lt_of_succ_lt hb)
  obtain ⟨v, hv⟩ := (signComm_chR_chL (D := D) (Sc := Sc) (i := i) (j := j) hb).symm
  have hv' : chR (B := End (wobj D Sc i j M (b + 1))) (tw D Sc i j M (b + 1)) (b + 1 + 1)
      (M - (b + 1 + 1)) ≫ chL (B := End (wobj D Sc i j M (b + 1))) (tw D Sc i j M (b + 1)) 0 b =
      (v : ℤ) • (chL (B := End (wobj D Sc i j M (b + 1))) (tw D Sc i j M (b + 1)) 0 b ≫
        chR (B := End (wobj D Sc i j M (b + 1))) (tw D Sc i j M (b + 1)) (b + 1 + 1)
          (M - (b + 1 + 1))) := hv
  have hI : upMap D Sc i j M hb ≫ downMap D Sc i j M hb = (u : ℤ) •
      (eIdem D Sc i j M (b + 1) ≫ up D Sc i j M hb ≫ tw D Sc i j M (b + 1 + 1) b ≫
        down D Sc i j M hb ≫
        chL (B := End (wobj D Sc i j M (b + 1))) (tw D Sc i j M (b + 1)) 0 b ≫
        chR (B := End (wobj D Sc i j M (b + 1))) (tw D Sc i j M (b + 1)) (b + 1 + 1)
          (M - (b + 1 + 1))) := by
    rw [show downMap D Sc i j M hb = eIdem D Sc i j M (b + 1 + 1) ≫ down D Sc i j M hb ≫
      chR (B := End (wobj D Sc i j M (b + 1))) (tw D Sc i j M (b + 1)) (b + 1 + 1)
        (M - (b + 1 + 1)) from rfl, ← Category.assoc, upMap_comp_eIdem]
    unfold upMap
    rw [show chL (B := End (wobj D Sc i j M (b + 1 + 1))) (tw D Sc i j M (b + 1 + 1)) 0 (b + 1) =
      tw D Sc i j M (b + 1 + 1) b ≫
        chL (B := End (wobj D Sc i j M (b + 1 + 1))) (tw D Sc i j M (b + 1 + 1)) 0 b by
      rw [Categorification.KLR.KL2.NH.chL_succ', zero_add]; rfl]
    simp only [Category.assoc]
    rw [reassoc_of% hu]
    simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc]
  have hII : downMap D Sc i j M (Nat.lt_of_succ_lt hb) ≫ upMap D Sc i j M (Nat.lt_of_succ_lt hb) =
      ((u' * v : ℤˣ) : ℤ) •
      (eIdem D Sc i j M (b + 1) ≫ down D Sc i j M (Nat.lt_of_succ_lt hb) ≫
        tw D Sc i j M b (b + 1) ≫ up D Sc i j M (Nat.lt_of_succ_lt hb) ≫
        chL (B := End (wobj D Sc i j M (b + 1))) (tw D Sc i j M (b + 1)) 0 b ≫
        chR (B := End (wobj D Sc i j M (b + 1))) (tw D Sc i j M (b + 1)) (b + 1 + 1)
          (M - (b + 1 + 1))) := by
    rw [show upMap D Sc i j M (Nat.lt_of_succ_lt hb) = eIdem D Sc i j M b ≫
      up D Sc i j M (Nat.lt_of_succ_lt hb) ≫
      chL (B := End (wobj D Sc i j M (b + 1))) (tw D Sc i j M (b + 1)) 0 b from rfl,
      ← Category.assoc, downMap_comp_eIdem]
    unfold downMap
    rw [show chR (B := End (wobj D Sc i j M b)) (tw D Sc i j M b) (b + 1) (M - (b + 1)) =
      tw D Sc i j M b (b + 1) ≫
        chR (B := End (wobj D Sc i j M b)) (tw D Sc i j M b) (b + 1 + 1) (M - (b + 1 + 1)) by
      rw [show M - (b + 1) = M - (b + 1 + 1) + 1 by omega,
        Categorification.KLR.KL2.NH.chR_succ]; rfl]
    simp only [Category.assoc]
    rw [reassoc_of% hu']
    simp only [Preadditive.zsmul_comp, Preadditive.comp_zsmul, Category.assoc]
    rw [hv']
    simp only [Preadditive.comp_zsmul, smul_smul, Units.val_mul]
  simp only [Preadditive.comp_sub, Preadditive.sub_comp, Category.assoc] at hcorr
  rw [sub_eq_iff_eq_add] at hcorr
  set γ' : k := ↑hγ.unit⁻¹
  have hγγ : γ' * γ = 1 := hγ.val_inv_mul
  have hUU := intCast_units_mul_self (k := k) u
  have hVV := intCast_units_mul_self (k := k) (u' * v)
  refine ⟨-(γ' * ((u : ℤ) : k)), γ' * (((u' * v : ℤˣ) : ℤ) : k), ?_⟩
  rw [hI, hII, hcorr, ← Int.cast_smul_eq_zsmul k, ← Int.cast_smul_eq_zsmul k]
  simp only [smul_add, smul_smul]
  rw [show γ' * (((u' * v : ℤˣ) : ℤ) : k) * ((((u' * v : ℤˣ) : ℤ) : k) * γ) = 1 by
      linear_combination (γ' * γ) * hVV + hγγ,
    show -(γ' * ((u : ℤ) : k)) * ((u : ℤ) : k) =
      -(γ' * (((u' * v : ℤˣ) : ℤ) : k) * (((u' * v : ℤˣ) : ℤ) : k)) by
      linear_combination (-γ') * hUU + γ' * hVV,
    neg_smul, one_smul]
  abel

end Interior

/-! ### The ends of the complex -/

section Ends

open SignedNilHecke

variable {D Sc i j M}

/-- (1.7) on words given up to equality. -/
theorem cl_cross_cross_of {w : List I} (l r : List I) {x y : I} (hxy : x ≠ y) (hd : D.d x y ≠ 0)
    (hw : w = l ++ [x, y] ++ r) {p : ℕ} (hp : l.length = p) {gs : List PG}
    (hgs : gs = [.cross p, .cross p]) (h : SChain w (pl w gs) w) :
    cl D Sc w w gs h =
      ∑ p' ∈ Finset.Ioo 0 (D.dn x y), ∑ q ∈ Finset.Ioo 0 (D.dn y x),
        Sc.s x y p' q • (dotE D Sc w p ^ p' * dotE D Sc w (p + 1) ^ q) +
      ((Sc.t x y : k) • dotE D Sc w p ^ D.dn x y +
        (Sc.t y x : k) • dotE D Sc w (p + 1) ^ D.dn y x) := by
  subst hw hp hgs
  exact cross_cross_ne D Sc l r hxy hd h

/-- (1.7) with `d_xy = 0` on words given up to equality. -/
theorem cl_cross_cross_zero_of {w : List I} (l r : List I) {x y : I} (hxy : x ≠ y)
    (hd : D.d x y = 0) (hw : w = l ++ [x, y] ++ r) {p : ℕ} (hp : l.length = p) {gs : List PG}
    (hgs : gs = [.cross p, .cross p]) (h : SChain w (pl w gs) w) :
    cl D Sc w w gs h = (Sc.t x y : k) • 𝟙 _ := by
  subst hw hp hgs
  exact cross_cross_ne_zero D Sc l r hxy hd h

theorem lIdem_zero : lIdem D Sc i j M 0 = 1 := by
  simp [lIdem, idem, Wb, Categorification.NilHecke.w0Word]

theorem rIdem_top {b : ℕ} (hbM : M = b + 1) : rIdem D Sc i j M (b + 1) = 1 := by
  unfold rIdem
  rw [show M - (b + 1) = 0 by omega]
  simp [idem, Wb, Categorification.NilHecke.w0Word]

/-- HW Theorem 5.9 at `a = 0`: `e_0` is a multiple of `upMap 0 ≫ downMap 0`. -/
theorem split_zero (hij : i ≠ j) (hM : M = D.dn i j + 1) :
    ∃ cp : k, eIdem D Sc i j M 0 =
      cp • (upMap D Sc i j M (by omega : 0 < M) ≫ downMap D Sc i j M (by omega : 0 < M)) := by
  have h0 : 0 < M := by omega
  have hc : upMap D Sc i j M h0 ≫ downMap D Sc i j M h0 = eIdem D Sc i j M 0 ≫
      (up D Sc i j M h0 ≫ down D Sc i j M h0) ≫
        chR (B := End (wobj D Sc i j M 0)) (tw D Sc i j M 0) 1 (M - 1) := by
    rw [show downMap D Sc i j M h0 = eIdem D Sc i j M 1 ≫ down D Sc i j M h0 ≫
      chR (B := End (wobj D Sc i j M 0)) (tw D Sc i j M 0) 1 (M - 1) from rfl,
      ← Category.assoc, upMap_comp_eIdem]
    unfold upMap
    rw [Categorification.KLR.KL2.NH.chL_zero, End.one_def, Category.comp_id]
    simp only [Category.assoc]
  have e : word i j M 0 = [] ++ [j, i] ++ List.replicate (M - 1) i := by
    rw [word_up h0]; simp
  have hcc : up D Sc i j M h0 ≫ down D Sc i j M h0 =
      cl D Sc (word i j M 0) (word i j M 0) [.cross 0, .cross 0]
        (sChain_comp (sChain_up h0) (sChain_down h0)) := by
    unfold up down; rw [cl_comp]; rfl
  rcases eq_or_ne (D.d i j) 0 with hd | hd
  · have hd' := (D.d_eq_zero_iff i j).1 hd
    have hM1 : M = 1 := by have := D.dn_cast hij; omega
    refine ⟨((Sc.t j i)⁻¹ : kˣ), ?_⟩
    rw [hc, hcc, cl_cross_cross_zero_of _ _ hij.symm hd' e (p := 0) rfl rfl, Linear.smul_comp,
      Category.id_comp, Linear.comp_smul, show M - 1 = 0 by omega,
      Categorification.KLR.KL2.NH.chR_zero, End.one_def, Category.comp_id, smul_smul,
      Units.inv_mul, one_smul]
  · have hd' : D.d j i ≠ 0 := fun h => hd ((D.d_eq_zero_iff i j).2 h)
    have hn : D.dn i j = M - 1 := by omega
    have hn0 : 0 < D.dn i j := by have := D.dn_cast hij; omega
    -- the right block of `j i^M`
    have hR : ∀ q ≤ M - 1, chR (tw D Sc i j M 0) 1 (M - 1) *
        (xw D Sc i j M 0 1 ^ q * rIdem D Sc i j M 0) =
        if q = M - 1 then ((eps D i : ℤ) ^ (M - 1).choose 2) • rIdem D Sc i j M 0 else 0 := by
      intro q hq
      have h := (rightFamily (D := D) (Sc := Sc) (i := i) (j := j) (M := M) 0).chR_mul_x_pow_mul_idem
        (s' := 1) (l := M - 1) (a := q) le_rfl (by omega) hq
      rw [show M - 1 + 1 = M by omega] at h
      exact h
    have hX : ∀ p, SignComm (chR (tw D Sc i j M 0) 1 (M - 1)) (xw D Sc i j M 0 0 ^ p) := by
      intro p
      unfold chR
      refine ((SignComm.wp fun q hq => ?_).pow_left p).symm
      rw [List.mem_reverse, List.mem_range'_1] at hq
      exact signComm_dot_cross D Sc (by omega) (word_gt (by omega) (by omega))
        (word_gt (by omega) (by omega))
    have hzero : ∀ p q, q < M - 1 → chR (tw D Sc i j M 0) 1 (M - 1) *
        (xw D Sc i j M 0 0 ^ p * xw D Sc i j M 0 1 ^ q) * eIdem D Sc i j M 0 = 0 := by
      intro p q hq
      obtain ⟨u, hu⟩ := hX p
      rw [eIdem, lIdem_zero, one_mul, ← mul_assoc, hu, smul_mul_assoc, smul_mul_assoc,
        mul_assoc, mul_assoc, hR q hq.le, ite_eq_right (by omega), mul_zero, smul_zero]
    obtain ⟨c, hc'⟩ : ∃ c : ℤ, IsUnit c ∧ chR (tw D Sc i j M 0) 1 (M - 1) *
        xw D Sc i j M 0 1 ^ (M - 1) * eIdem D Sc i j M 0 = c • eIdem D Sc i j M 0 :=
      ⟨_, (Units.isUnit (eps D i)).pow _, by
        rw [eIdem, lIdem_zero, one_mul, mul_assoc, hR _ le_rfl, ite_eq_left rfl]⟩
    have hval : eIdem D Sc i j M 0 ≫ cl D Sc (word i j M 0) (word i j M 0) [.cross 0, .cross 0]
        (sChain_comp (sChain_up h0) (sChain_down h0)) ≫
          chR (B := End (wobj D Sc i j M 0)) (tw D Sc i j M 0) 1 (M - 1) =
        ((Sc.t i j : k) * ((c : ℤ) : k)) • eIdem D Sc i j M 0 := by
      rw [cl_cross_cross_of _ _ hij.symm hd' e (p := 0) rfl rfl]
      change chR (tw D Sc i j M 0) 1 (M - 1) * (_ + _) * eIdem D Sc i j M 0 = _
      simp only [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm,
        smul_mul_assoc, zero_add]
      rw [Finset.sum_eq_zero fun p' _ => Finset.sum_eq_zero fun q hq => by
        rw [Finset.mem_Ioo] at hq
        rw [hzero p' q (by omega), smul_zero]]
      have h₁ := hzero (D.dn j i) 0 (by omega)
      rw [pow_zero, mul_one] at h₁
      rw [h₁, smul_zero, hn, hc'.2, ← Int.cast_smul_eq_zsmul k, smul_smul]
      simp only [zero_add]
    have hγ : IsUnit ((Sc.t i j : k) * ((c : ℤ) : k)) :=
      (Sc.t i j).isUnit.mul (hc'.1.map (Int.castRingHom k))
    refine ⟨↑hγ.unit⁻¹, ?_⟩
    rw [hc, hcc, hval, smul_smul, hγ.val_inv_mul, one_smul]

/-- HW Theorem 5.9 at `a = M`: `e_M` is a multiple of `downMap (M-1) ≫ upMap (M-1)`. -/
theorem split_top (hij : i ≠ j) {b : ℕ} (hM : M = D.dn i j + 1) (hbM : M = b + 1) :
    ∃ cm : k, eIdem D Sc i j M (b + 1) =
      cm • (downMap D Sc i j M (by omega : b < M) ≫ upMap D Sc i j M (by omega : b < M)) := by
  have hb : b < M := by omega
  have hc : downMap D Sc i j M hb ≫ upMap D Sc i j M hb = eIdem D Sc i j M (b + 1) ≫
      (down D Sc i j M hb ≫ up D Sc i j M hb) ≫
        chL (B := End (wobj D Sc i j M (b + 1))) (tw D Sc i j M (b + 1)) 0 b := by
    rw [show upMap D Sc i j M hb = eIdem D Sc i j M b ≫ up D Sc i j M hb ≫
      chL (B := End (wobj D Sc i j M (b + 1))) (tw D Sc i j M (b + 1)) 0 b from rfl,
      ← Category.assoc, downMap_comp_eIdem]
    unfold downMap
    rw [show M - (b + 1) = 0 by omega, Categorification.KLR.KL2.NH.chR_zero, End.one_def,
      Category.comp_id]
    simp only [Category.assoc]
  have e : word i j M (b + 1) = List.replicate b i ++ [i, j] ++ [] := by
    rw [word_down b, show M - b - 1 = 0 by omega]; rfl
  have hcc : down D Sc i j M hb ≫ up D Sc i j M hb =
      cl D Sc (word i j M (b + 1)) (word i j M (b + 1)) [.cross b, .cross b]
        (sChain_comp (sChain_down hb) (sChain_up hb)) := by
    unfold up down; rw [cl_comp]; rfl
  rcases eq_or_ne (D.d i j) 0 with hd | hd
  · have hb0 : b = 0 := by have := D.dn_cast hij; omega
    subst hb0
    refine ⟨((Sc.t i j)⁻¹ : kˣ), ?_⟩
    rw [hc, hcc, cl_cross_cross_zero_of _ _ hij hd e (p := 0) rfl rfl, Linear.smul_comp,
      Category.id_comp, Linear.comp_smul, Categorification.KLR.KL2.NH.chL_zero, End.one_def,
      Category.comp_id, smul_smul, Units.inv_mul, one_smul]
  · have hn : D.dn i j = b := by omega
    have hn0 : 0 < b := by have := D.dn_cast hij; omega
    have hzero : ∀ p q, p < b → chL (tw D Sc i j M (b + 1)) 0 b *
        (xw D Sc i j M (b + 1) b ^ p * xw D Sc i j M (b + 1) (b + 1) ^ q) *
          eIdem D Sc i j M (b + 1) = 0 := by
      intro p q hp
      rw [eIdem, rIdem_top hbM, mul_one, mul_assoc, mul_assoc,
        pow_comm_lIdem (by omega) le_rfl (by omega), ← mul_assoc (xw D Sc i j M (b + 1) b ^ p),
        ← mul_assoc (chL (tw D Sc i j M (b + 1)) 0 b), ann_left p hp.le, ite_eq_right (by omega),
        zero_mul]
    have htop : chL (tw D Sc i j M (b + 1)) 0 b * xw D Sc i j M (b + 1) b ^ b *
        eIdem D Sc i j M (b + 1) = ((-1 : ℤ) ^ b * (eps D i : ℤ) ^ (b + 1).choose 2) •
          eIdem D Sc i j M (b + 1) := by
      rw [eIdem, rIdem_top hbM, mul_one, mul_assoc, ann_left b le_rfl, ite_eq_left rfl]
    have hval : eIdem D Sc i j M (b + 1) ≫ cl D Sc (word i j M (b + 1)) (word i j M (b + 1))
        [.cross b, .cross b] (sChain_comp (sChain_down hb) (sChain_up hb)) ≫
          chL (B := End (wobj D Sc i j M (b + 1))) (tw D Sc i j M (b + 1)) 0 b =
        ((Sc.t i j : k) * ((((-1 : ℤ) ^ b * (eps D i : ℤ) ^ (b + 1).choose 2 : ℤ)) : k)) •
          eIdem D Sc i j M (b + 1) := by
      rw [cl_cross_cross_of _ _ hij hd e (p := b) (by simp) rfl]
      change chL (tw D Sc i j M (b + 1)) 0 b * (_ + _) * eIdem D Sc i j M (b + 1) = _
      simp only [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul, mul_smul_comm,
        smul_mul_assoc]
      rw [Finset.sum_eq_zero fun p' hp' => Finset.sum_eq_zero fun q _ => by
        rw [Finset.mem_Ioo] at hp'
        rw [hzero p' q (by omega), smul_zero]]
      have h₁ := hzero 0 (D.dn j i) (by omega)
      rw [pow_zero, one_mul] at h₁
      rw [h₁, smul_zero, hn, htop, ← Int.cast_smul_eq_zsmul k, smul_smul]
      simp only [zero_add, add_zero]
    have hγ : IsUnit ((Sc.t i j : k) *
        ((((-1 : ℤ) ^ b * (eps D i : ℤ) ^ (b + 1).choose 2 : ℤ)) : k)) :=
      (Sc.t i j).isUnit.mul (((isUnit_one.neg.pow b).mul ((Units.isUnit _).pow _)).map
        (Int.castRingHom k))
    refine ⟨↑hγ.unit⁻¹, ?_⟩
    rw [hc, hcc, hval, smul_smul, hγ.val_inv_mul, one_smul]

end Ends


/-! ## The split complex in `H_{M+1}` -/

section Assembly

variable (i j : I) (M : ℕ)

/-- The word `i^a j i^{M-a}` as a word of length `M + 1`. -/
def wd {a : ℕ} (ha : a ≤ M) : Word I (M + 1) := ⟨word i j M a, length_word ha⟩

/-- `e_a = 1_{i^{(a)} j i^{(M-a)}}` in `H_{M+1}` (zero for `a > M`). -/
def eH (a : ℕ) : Hn D Sc (M + 1) :=
  if h : a ≤ M then Hn.single (wd i j M h) (wd i j M h) (eIdem D Sc i j M a) else 0

/-- The map `upMap a` as an element of `e_{a+1} H_{M+1} e_a` (zero for `a ≥ M`). -/
def fH (a : ℕ) : Hn D Sc (M + 1) :=
  if h : a < M then Hn.single (wd i j M (a := a + 1) h) (wd i j M h.le) (upMap D Sc i j M h)
  else 0

/-- The map `downMap a` as an element of `e_a H_{M+1} e_{a+1}` (zero for `a ≥ M`). -/
def gH (a : ℕ) : Hn D Sc (M + 1) :=
  if h : a < M then Hn.single (wd i j M h.le) (wd i j M (a := a + 1) h) (downMap D Sc i j M h)
  else 0

variable {D Sc i j M}

theorem eIdem_comp_upMap {a : ℕ} (ha : a < M) :
    eIdem D Sc i j M a ≫ upMap D Sc i j M ha = upMap D Sc i j M ha := by
  unfold upMap
  rw [← Category.assoc, show eIdem D Sc i j M a ≫ eIdem D Sc i j M a = eIdem D Sc i j M a from
    eIdem_idem a ha.le]

theorem eIdem_comp_downMap {a : ℕ} (ha : a < M) :
    eIdem D Sc i j M (a + 1) ≫ downMap D Sc i j M ha = downMap D Sc i j M ha := by
  unfold downMap
  rw [← Category.assoc, show eIdem D Sc i j M (a + 1) ≫ eIdem D Sc i j M (a + 1) =
    eIdem D Sc i j M (a + 1) from eIdem_idem (a + 1) ha]

theorem fH_mul (a : ℕ) : fH D Sc i j M a * eH D Sc i j M a = fH D Sc i j M a := by
  by_cases h : a < M
  · rw [fH, eH, dite_eq_left h, dite_eq_left h.le, Hn.single_mul_single, eIdem_comp_upMap]
  · rw [fH, dite_eq_right h, FiniteHomMatrix.matrix_zero_mul]

theorem mul_fH (a : ℕ) : eH D Sc i j M (a + 1) * fH D Sc i j M a = fH D Sc i j M a := by
  by_cases h : a < M
  · rw [fH, eH, dite_eq_left h, dite_eq_left (show a + 1 ≤ M from h), Hn.single_mul_single,
      upMap_comp_eIdem]
  · rw [fH, dite_eq_right h, FiniteHomMatrix.matrix_mul_zero]

theorem gH_mul (a : ℕ) : gH D Sc i j M a * eH D Sc i j M (a + 1) = gH D Sc i j M a := by
  by_cases h : a < M
  · rw [gH, eH, dite_eq_left h, dite_eq_left (show a + 1 ≤ M from h), Hn.single_mul_single,
      eIdem_comp_downMap]
  · rw [gH, dite_eq_right h, FiniteHomMatrix.matrix_zero_mul]

theorem mul_gH (a : ℕ) : eH D Sc i j M a * gH D Sc i j M a = gH D Sc i j M a := by
  by_cases h : a < M
  · rw [gH, eH, dite_eq_left h, dite_eq_left h.le, Hn.single_mul_single, downMap_comp_eIdem]
  · rw [gH, dite_eq_right h, FiniteHomMatrix.matrix_mul_zero]

theorem fH_mul_fH (a : ℕ) : fH D Sc i j M (a + 1) * fH D Sc i j M a = 0 := by
  by_cases h : a + 1 < M
  · rw [fH, fH, dite_eq_left h, dite_eq_left (Nat.lt_of_succ_lt h), Hn.single_mul_single,
      upMap_comp_upMap h]
    exact FiniteHomMatrix.single_zero _ _
  · rw [show fH D Sc i j M (a + 1) = 0 from dite_eq_right h, FiniteHomMatrix.matrix_zero_mul]

theorem gH_mul_gH (a : ℕ) : gH D Sc i j M a * gH D Sc i j M (a + 1) = 0 := by
  by_cases h : a + 1 < M
  · rw [gH, gH, dite_eq_left h, dite_eq_left (Nat.lt_of_succ_lt h), Hn.single_mul_single,
      downMap_comp_downMap h]
    exact FiniteHomMatrix.single_zero _ _
  · rw [show gH D Sc i j M (a + 1) = 0 from dite_eq_right h, FiniteHomMatrix.matrix_mul_zero]

theorem gH_mul_fH {a : ℕ} (h : a < M) :
    gH D Sc i j M a * fH D Sc i j M a =
      Hn.single (wd i j M h.le) (wd i j M h.le) (upMap D Sc i j M h ≫ downMap D Sc i j M h) := by
  rw [gH, fH, dite_eq_left h, dite_eq_left h, Hn.single_mul_single]

theorem fH_mul_gH {a : ℕ} (h : a < M) :
    fH D Sc i j M a * gH D Sc i j M a =
      Hn.single (wd i j M (a := a + 1) h) (wd i j M (a := a + 1) h)
        (downMap D Sc i j M h ≫ upMap D Sc i j M h) := by
  rw [gH, fH, dite_eq_left h, dite_eq_left h, Hn.single_mul_single]

theorem single_comb {a b : Word I (M + 1)} (c₁ c₂ : k)
    (f g : wordObj D Sc b ⟶ wordObj D Sc a) :
    Hn.single a b (c₁ • f + c₂ • g) = c₁ • Hn.single a b f + c₂ • Hn.single a b g := by
  unfold Hn.single
  rw [FiniteHomMatrix.single_add, FiniteHomMatrix.single_smul, FiniteHomMatrix.single_smul]

/-- The splitting identities of HW Theorem 5.9 in `H_{M+1}`. -/
theorem eH_split (hij : i ≠ j) (hM : M = D.dn i j + 1) (a : ℕ) (ha : a ≤ M) :
    ∃ cp cm : k, eH D Sc i j M a = cp • (gH D Sc i j M a * fH D Sc i j M a) +
      if 0 < a then cm • (fH D Sc i j M (a - 1) * gH D Sc i j M (a - 1)) else 0 := by
  rcases a with _ | b
  · obtain ⟨cp, hcp⟩ := split_zero (D := D) (Sc := Sc) hij hM
    refine ⟨cp, 0, ?_⟩
    rw [ite_eq_right (lt_irrefl 0), add_zero, gH_mul_fH (by omega), eH, dite_eq_left ha, hcp]
    exact FiniteHomMatrix.single_smul _ _ _ _
  · by_cases hb : b + 1 < M
    · obtain ⟨cp, cm, hc⟩ := split_interior (D := D) (Sc := Sc) hij hM hb
      refine ⟨cp, cm, ?_⟩
      rw [ite_eq_left (Nat.succ_pos b), Nat.add_sub_cancel, fH_mul_gH (by omega), gH_mul_fH hb,
        eH, dite_eq_left ha, hc]
      exact single_comb _ _ _ _
    · obtain ⟨cm, hc⟩ := split_top (D := D) (Sc := Sc) hij hM (b := b) (by omega)
      refine ⟨0, cm, ?_⟩
      rw [ite_eq_left (Nat.succ_pos b), Nat.add_sub_cancel, fH_mul_gH (by omega), eH,
        dite_eq_left ha, zero_smul, zero_add, hc]
      exact FiniteHomMatrix.single_smul _ _ _ _

open DividedPowerModules in
/-- **BE2 Proposition 11.2** (HW Theorem 5.9), on underlying modules: for `i ≠ j` and
`M = d_ij + 1`, the principal modules `H_{M+1} e_a` of the words `i^a j i^{M-a}`
(`0 ≤ a ≤ M`) with the maps `upMap`, `downMap` form a split complex: consecutive maps compose to
zero and `e_a = c⁺_a g_a f_a + c⁻_a f_{a-1} g_{a-1}`. -/
theorem isSplit (hij : i ≠ j) (hM : M = D.dn i j + 1) :
    ∃ cp cm : ℕ → k, SplitComplex.IsSplit M
      (fun a => (eH D Sc i j M a : ModuleRing D Sc (M + 1)))
      (fun a => (fH D Sc i j M a : ModuleRing D Sc (M + 1)))
      (fun a => (gH D Sc i j M a : ModuleRing D Sc (M + 1))) cp cm := by
  have hs := fun a ha => eH_split (D := D) (Sc := Sc) hij hM a ha
  choose! cp cm hc using hs
  refine ⟨cp, cm, ⟨fun a => ?_, fun a => ?_, fun a => ?_, fun a => ?_, fun a => ?_,
    fun a => ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_⟩⟩
  · rw [← Unitization.inr_mul, fH_mul]
  · rw [← Unitization.inr_mul, mul_fH]
  · rw [← Unitization.inr_mul, gH_mul]
  · rw [← Unitization.inr_mul, mul_gH]
  · rw [← Unitization.inr_mul, fH_mul_fH, Unitization.inr_zero]
  · rw [← Unitization.inr_mul, gH_mul_gH, Unitization.inr_zero]
  · rw [fH, dite_eq_right (by omega), Unitization.inr_zero]
  · rw [gH, dite_eq_right (by omega), Unitization.inr_zero]
  · rw [hc a ha]
    split_ifs <;> simp only [Unitization.inr_add, Unitization.inr_smul, Unitization.inr_mul,
      Unitization.inr_zero]

open DividedPowerModules SplitComplex in
/-- **BE2 Proposition 11.2**, "in particular" (on underlying modules): the sum of the principal
modules `H_{M+1} e_a` over even `a` is isomorphic to the sum over odd `a`. -/
def serreEquiv (hij : i ≠ j) (hM : M = D.dn i j + 1) :
    (∀ a : terms M true, principal D Sc (eH D Sc i j M a)) ≃ₗ[ModuleRing D Sc (M + 1)]
      (∀ b : terms M false, principal D Sc (eH D Sc i j M b)) :=
  (Classical.choose_spec (Classical.choose_spec (isSplit (D := D) (Sc := Sc) hij hM))).evenOddEquiv

end Assembly

end OddMath.QuiverHecke.SerreComplex
