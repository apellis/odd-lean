/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.PrefixQPDistinct

/-!
# The repeated-colour step of the all-prefix QP induction

`docs/Nondegeneracy/DeformedGlobalQP.md`, §§2–3, case `ν_n = i` (the deformed form of
Kang–Kashiwara–Oh, arXiv:1206.5933v2, proof of Theorem 8.5, (8.14)–(8.17)). Write
`Vₙ = moveHom i [] ν`, `Tₙ = lastToFirstHom i ν` and `W = ν ++ [i] ++ [i]`. On `W` let `u, v`
be the dots at positions `|ν|, |ν| + 1` (the moving strand and the new spectator), and on
`i :: (ν ++ [i])` let `u₀, v₀` be the dots at positions `0, |ν| + 1`. Put
`h = p(ν₁) + ⋯ + p(νₙ)` and `s = (-1)^(p(i) h)`.

* `moveHom_append_self`, `lastToFirstHom_append_self`: `V_(n+1) = (Vₙ ⊗ 1) g` and
  `T_(n+1) = (Tₙ ⊗ 1) τ` with `g` the same-colour intertwiner of `W` at `|ν|`
  (`sameIntertwiner`) and `τ` the crossing there.
* `moveHom_whiskerRight_comp_sameIntertwiner_odd`, `_even`: the expansion of
  `(Vₙ ⊗ 1) g` with its polynomial part moved in front of `Vₙ ⊗ 1`:
  `D V = V D₀` and `E V = s V E₀` for `E = v - u`, `D = v² - u²`. In the odd case
  `g = D E - D D τ` (in execution order); in the even case `g = E + E E τ`.
  These are the two terms of the relation (K) used in the induction.
* `moveHom_lastToFirstHom_append_self_odd`, `_even`: the recursion
  `V_(n+1) T_(n+1) = s D₀ E₀ (Vₙ ⊗ 1) T_(n+1)` for odd `i` and
  `V_(n+1) T_(n+1) = E₀ (Vₙ ⊗ 1) T_(n+1)` for even `i` (KKO (8.15): `τ g = τ E D`,
  resp. `τ E`).

Arbitrary words and parities.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams MonoidalCategory SignedNilHecke
universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X) [CommRing k]
  (Sc : SKM.Scalars D k)

/-! ### Two-strand algebra -/

section TwoStrand

variable {B : Type*} [Ring B]

/-- The odd same-colour intertwiner with its polynomial factors on the right. -/
theorem OddTwo.element_eq_sub {x y T : B} (h : OddTwo x y T) :
    OddNilHecke.Intertwiner.element x y T =
      (y - x) * OddNilHecke.Intertwiner.squareDiff x y -
        T * OddNilHecke.Intertwiner.squareDiff x y * OddNilHecke.Intertwiner.squareDiff x y := by
  rw [h.element_identities.2.2.2.1]
  noncomm_ring

/-- The even same-colour intertwiner with its polynomial factors on the right. -/
theorem EvenTwo.gEven_eq_add {x y T : B} (h : EvenTwo x y T) :
    gEven x y T = (y - x) + T * (y - x) * (y - x) := by
  simp only [phiEven, gEven, mul_add, add_mul, mul_sub, sub_mul, mul_assoc,
    h.tu', h.tv', h.vu, mul_one]
  noncomm_ring

end TwoStrand

/-! ### Signed transport of differences -/

section Transport

variable {C : Type*} [Category C] [Preadditive C] [Linear k C]

theorem comp_end_sub {A B : C} (g : A ⟶ B) (a b : End B) :
    g ≫ (b - a) = g ≫ b - g ≫ a :=
  Preadditive.comp_sub _ _ _

theorem end_sub_comp {A B : C} (g : A ⟶ B) (a b : End A) :
    (b - a) ≫ g = b ≫ g - a ≫ g :=
  Preadditive.sub_comp _ _ _

theorem comp_sub_of_signed {A B : C} (g : A ⟶ B) (a' b' : End A) (a b : End B) (s : k)
    (ha : g ≫ a = s • (a' ≫ g)) (hb : g ≫ b = s • (b' ≫ g)) :
    g ≫ (b - a) = s • ((b' - a') ≫ g) := by
  rw [comp_end_sub, ha, hb, end_sub_comp, smul_sub]

theorem comp_squareDiff_of_signed {A B : C} (g : A ⟶ B) (a' b' : End A) (a b : End B)
    (s : k) (hs : s ^ 2 = 1) (ha : g ≫ a = s • (a' ≫ g)) (hb : g ≫ b = s • (b' ≫ g)) :
    g ≫ OddNilHecke.Intertwiner.squareDiff (A := End B) a b =
      OddNilHecke.Intertwiner.squareDiff (A := End A) a' b' ≫ g := by
  unfold OddNilHecke.Intertwiner.squareDiff
  rw [comp_end_sub, comp_pow_of_signed g a' a s ha, comp_pow_of_signed g b' b s hb, hs,
    one_smul, one_smul, end_sub_comp]

end Transport

theorem zmod_two_mul_self (p : ZMod 2) : p * p = p := by
  have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hz p with rfl | rfl <;> rfl

/-! ### The last-letter recursions on `ν ++ [i]` -/

theorem eqToHom_sameIntertwiner_eqToHom {w w' w'' : List I} (e : w = w') (e' : w' = w'')
    (a : ℕ) (i : I) :
    eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) e) ≫
        sameIntertwiner D Sc w' a i ≫
          eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) e') =
      sameIntertwiner D Sc w a i ≫
        eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) (e.trans e')) := by
  subst e e'
  simp

/-- `Vₙ ⊗ 1_i`, typed between the words `i :: (ν ++ [i])` and `ν ++ [i] ++ [i]`. -/
def moveWhisker (i : I) (ν : List I) :
    (pres D Sc).obj (ob D (i :: (ν ++ [i]))) ⟶ (pres D Sc).obj (ob D (ν ++ [i] ++ [i])) :=
  moveHom D Sc i [] ν ▷ (pres D Sc).obj (ob D [i])

/-- `V_(n+1) = (Vₙ ⊗ 1_i) g` on `ν ++ [i]`, with `g` the same-colour intertwiner. -/
theorem moveHom_append_self (i : I) (ν : List I) :
    moveHom D Sc i [] (ν ++ [i]) =
      moveWhisker D Sc i ν ≫ sameIntertwiner D Sc (ν ++ [i] ++ [i]) ν.length i := by
  rw [moveHom_append_singleton, intertwinerHom_self, eqToHom_sameIntertwiner_eqToHom]
  · erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  all_goals simp [ob]

/-- `T_(n+1) = (Tₙ ⊗ 1_i) τ` on `ν ++ [i]`, with `τ` the crossing at `|ν|`. -/
theorem lastToFirstHom_append_self (i : I) (ν : List I) :
    lastToFirstHom D Sc i (ν ++ [i]) =
      crossE D Sc (ν ++ [i] ++ [i]) ν.length ≫
        (lastToFirstHom D Sc i ν ▷ (pres D Sc).obj (ob D [i])) := by
  rw [lastToFirstHom_append_singleton, crossE_eq_cl]

/-- The moving-strand dot through `Vₙ ⊗ 1_i`. -/
theorem moveWhisker_comp_dot (i : I) (ν : List I) :
    moveWhisker D Sc i ν ≫ dotE D Sc (ν ++ [i] ++ [i]) ν.length =
      SKM.zsign k (D.parity i * wordSumParity D ν) •
        (dotE D Sc (i :: (ν ++ [i])) 0 ≫ moveWhisker D Sc i ν) :=
  moveHom_whiskerRight_comp_dot D Sc i i ν

/-- The spectator dot through `Vₙ ⊗ 1_i`, with the same sign `s = (-1)^(p(i) h)`. -/
theorem moveWhisker_comp_last_dot (i : I) (ν : List I) :
    moveWhisker D Sc i ν ≫ dotE D Sc (ν ++ [i] ++ [i]) (ν.length + 1) =
      SKM.zsign k (D.parity i * wordSumParity D ν) •
        (dotE D Sc (i :: (ν ++ [i])) (ν.length + 1) ≫ moveWhisker D Sc i ν) := by
  have h := moveHom_whiskerRight_comp_last_dot D Sc i i ν
  rw [mul_right_comm, zmod_two_mul_self] at h
  exact h

theorem zsign_sq (p : ZMod 2) : SKM.zsign k p ^ 2 = 1 := by
  rw [sq, zsign_mul_self]

/-- `D V = V D₀` for `D = v² - u²`. -/
theorem moveWhisker_comp_squareDiff (i : I) (ν : List I) :
    moveWhisker D Sc i ν ≫
        OddNilHecke.Intertwiner.squareDiff (A := End _) (dotE D Sc (ν ++ [i] ++ [i]) ν.length)
          (dotE D Sc (ν ++ [i] ++ [i]) (ν.length + 1)) =
      OddNilHecke.Intertwiner.squareDiff (A := End _) (dotE D Sc (i :: (ν ++ [i])) 0)
          (dotE D Sc (i :: (ν ++ [i])) (ν.length + 1)) ≫ moveWhisker D Sc i ν :=
  comp_squareDiff_of_signed _ _ _ _ _ _ (zsign_sq _) (moveWhisker_comp_dot D Sc i ν)
    (moveWhisker_comp_last_dot D Sc i ν)

/-- `E V = s V E₀` for `E = v - u`. -/
theorem moveWhisker_comp_sub (i : I) (ν : List I) :
    moveWhisker D Sc i ν ≫
        (dotE D Sc (ν ++ [i] ++ [i]) (ν.length + 1) - dotE D Sc (ν ++ [i] ++ [i]) ν.length) =
      SKM.zsign k (D.parity i * wordSumParity D ν) •
        ((dotE D Sc (i :: (ν ++ [i])) (ν.length + 1) - dotE D Sc (i :: (ν ++ [i])) 0) ≫
          moveWhisker D Sc i ν) :=
  comp_sub_of_signed _ _ _ _ _ _ (moveWhisker_comp_dot D Sc i ν)
    (moveWhisker_comp_last_dot D Sc i ν)

theorem moveWhisker_comp_squareDiff_assoc (i : I) (ν : List I) {Z : (pres D Sc).Presented}
    (h : (pres D Sc).obj (ob D (ν ++ [i] ++ [i])) ⟶ Z) :
    moveWhisker D Sc i ν ≫
        OddNilHecke.Intertwiner.squareDiff (A := End _) (dotE D Sc (ν ++ [i] ++ [i]) ν.length)
          (dotE D Sc (ν ++ [i] ++ [i]) (ν.length + 1)) ≫ h =
      OddNilHecke.Intertwiner.squareDiff (A := End _) (dotE D Sc (i :: (ν ++ [i])) 0)
          (dotE D Sc (i :: (ν ++ [i])) (ν.length + 1)) ≫ moveWhisker D Sc i ν ≫ h := by
  rw [← Category.assoc, moveWhisker_comp_squareDiff, Category.assoc]

theorem moveWhisker_comp_sub_assoc (i : I) (ν : List I) {Z : (pres D Sc).Presented}
    (h : (pres D Sc).obj (ob D (ν ++ [i] ++ [i])) ⟶ Z) :
    moveWhisker D Sc i ν ≫
        (dotE D Sc (ν ++ [i] ++ [i]) (ν.length + 1) - dotE D Sc (ν ++ [i] ++ [i]) ν.length) ≫ h =
      SKM.zsign k (D.parity i * wordSumParity D ν) •
        ((dotE D Sc (i :: (ν ++ [i])) (ν.length + 1) - dotE D Sc (i :: (ν ++ [i])) 0) ≫
          moveWhisker D Sc i ν ≫ h) := by
  rw [← Category.assoc, moveWhisker_comp_sub, Linear.smul_comp, Category.assoc]

theorem oddTwo_append_self (i : I) (hp : D.parity i = 1) (ν : List I) :
    OddTwo (dotE D Sc (ν ++ [i] ++ [i]) ν.length)
      (dotE D Sc (ν ++ [i] ++ [i]) (ν.length + 1))
      (crossE D Sc (ν ++ [i] ++ [i]) ν.length) := by
  have e : ν ++ [i] ++ [i] = ν ++ [i, i] ++ [] := by simp
  rw [e]
  exact oddTwo_block D Sc ν [] i hp

theorem evenTwo_append_self (i : I) (hp : D.parity i = 0) (ν : List I) :
    EvenTwo (dotE D Sc (ν ++ [i] ++ [i]) ν.length)
      (dotE D Sc (ν ++ [i] ++ [i]) (ν.length + 1))
      (crossE D Sc (ν ++ [i] ++ [i]) ν.length) := by
  have e : ν ++ [i] ++ [i] = ν ++ [i, i] ++ [] := by simp
  rw [e]
  exact evenTwo_block D Sc ν [] i hp

theorem zsign_parity_even (i : I) (hp : D.parity i = 0) (ν : List I) :
    SKM.zsign k (D.parity i * wordSumParity D ν) = 1 := by
  rw [hp, zero_mul]
  simp [SKM.zsign]

/-- Odd colour: `(Vₙ ⊗ 1) g = s D₀ E₀ (Vₙ ⊗ 1) - D₀ D₀ (Vₙ ⊗ 1) τ` (execution order). -/
theorem moveWhisker_comp_sameIntertwiner_odd (i : I) (hp : D.parity i = 1) (ν : List I) :
    moveWhisker D Sc i ν ≫ sameIntertwiner D Sc (ν ++ [i] ++ [i]) ν.length i =
      SKM.zsign k (D.parity i * wordSumParity D ν) •
          (OddNilHecke.Intertwiner.squareDiff (A := End _) (dotE D Sc (i :: (ν ++ [i])) 0)
              (dotE D Sc (i :: (ν ++ [i])) (ν.length + 1)) ≫
            (dotE D Sc (i :: (ν ++ [i])) (ν.length + 1) - dotE D Sc (i :: (ν ++ [i])) 0) ≫
              moveWhisker D Sc i ν) -
        OddNilHecke.Intertwiner.squareDiff (A := End _) (dotE D Sc (i :: (ν ++ [i])) 0)
            (dotE D Sc (i :: (ν ++ [i])) (ν.length + 1)) ≫
          OddNilHecke.Intertwiner.squareDiff (A := End _) (dotE D Sc (i :: (ν ++ [i])) 0)
              (dotE D Sc (i :: (ν ++ [i])) (ν.length + 1)) ≫
            moveWhisker D Sc i ν ≫ crossE D Sc (ν ++ [i] ++ [i]) ν.length := by
  simp only [sameIntertwiner, hp, ↓reduceIte]
  rw [OddTwo.element_eq_sub (oddTwo_append_self D Sc i hp ν), comp_end_sub]
  simp only [End.mul_def]
  rw [moveWhisker_comp_squareDiff_assoc, moveWhisker_comp_sub, Linear.comp_smul,
    moveWhisker_comp_squareDiff_assoc, moveWhisker_comp_squareDiff_assoc, hp]

/-- Even colour: `(Vₙ ⊗ 1) g = E₀ (Vₙ ⊗ 1) + E₀ E₀ (Vₙ ⊗ 1) τ` (execution order). -/
theorem moveWhisker_comp_sameIntertwiner_even (i : I) (hp : D.parity i = 0) (ν : List I) :
    moveWhisker D Sc i ν ≫ sameIntertwiner D Sc (ν ++ [i] ++ [i]) ν.length i =
      (dotE D Sc (i :: (ν ++ [i])) (ν.length + 1) - dotE D Sc (i :: (ν ++ [i])) 0) ≫
          moveWhisker D Sc i ν +
        (dotE D Sc (i :: (ν ++ [i])) (ν.length + 1) - dotE D Sc (i :: (ν ++ [i])) 0) ≫
          (dotE D Sc (i :: (ν ++ [i])) (ν.length + 1) - dotE D Sc (i :: (ν ++ [i])) 0) ≫
            moveWhisker D Sc i ν ≫ crossE D Sc (ν ++ [i] ++ [i]) ν.length := by
  have hp' : ¬D.parity i = 1 := by rw [hp]; decide
  simp only [sameIntertwiner, hp', ↓reduceIte]
  rw [EvenTwo.gEven_eq_add (evenTwo_append_self D Sc i hp ν)]
  simp only [End.mul_def, comp_end_add]
  rw [moveWhisker_comp_sub, moveWhisker_comp_sub_assoc, moveWhisker_comp_sub_assoc,
    zsign_parity_even D i hp ν]
  simp only [one_smul]

/-- KKO (8.15), odd colour: `V_(n+1) T_(n+1) = s D₀ E₀ (Vₙ ⊗ 1_i) T_(n+1)`. -/
theorem moveHom_lastToFirstHom_append_self_odd (i : I) (hp : D.parity i = 1) (ν : List I) :
    moveHom D Sc i [] (ν ++ [i]) ≫ lastToFirstHom D Sc i (ν ++ [i]) =
      SKM.zsign k (D.parity i * wordSumParity D ν) •
        (OddNilHecke.Intertwiner.squareDiff (A := End _) (dotE D Sc (i :: (ν ++ [i])) 0)
            (dotE D Sc (i :: (ν ++ [i])) (ν.length + 1)) ≫
          (dotE D Sc (i :: (ν ++ [i])) (ν.length + 1) - dotE D Sc (i :: (ν ++ [i])) 0) ≫
            moveWhisker D Sc i ν ≫ lastToFirstHom D Sc i (ν ++ [i])) := by
  have hg : sameIntertwiner D Sc (ν ++ [i] ++ [i]) ν.length i ≫
        crossE D Sc (ν ++ [i] ++ [i]) ν.length =
      OddNilHecke.Intertwiner.squareDiff (A := End _) (dotE D Sc (ν ++ [i] ++ [i]) ν.length)
          (dotE D Sc (ν ++ [i] ++ [i]) (ν.length + 1)) ≫
        (dotE D Sc (ν ++ [i] ++ [i]) (ν.length + 1) - dotE D Sc (ν ++ [i] ++ [i]) ν.length) ≫
          crossE D Sc (ν ++ [i] ++ [i]) ν.length := by
    simp only [sameIntertwiner, hp, ↓reduceIte]
    rw [← End.mul_def, (oddTwo_append_self D Sc i hp ν).element_identities.2.2.2.2]
    simp only [End.mul_def]
  rw [moveHom_append_self, lastToFirstHom_append_self, Category.assoc,
    ← Category.assoc (sameIntertwiner _ _ _ _ _), hg]
  simp only [Category.assoc]
  rw [moveWhisker_comp_squareDiff_assoc, moveWhisker_comp_sub_assoc, Linear.comp_smul]

/-- KKO (8.15), even colour: `V_(n+1) T_(n+1) = E₀ (Vₙ ⊗ 1_i) T_(n+1)`. -/
theorem moveHom_lastToFirstHom_append_self_even (i : I) (hp : D.parity i = 0) (ν : List I) :
    moveHom D Sc i [] (ν ++ [i]) ≫ lastToFirstHom D Sc i (ν ++ [i]) =
      (dotE D Sc (i :: (ν ++ [i])) (ν.length + 1) - dotE D Sc (i :: (ν ++ [i])) 0) ≫
        moveWhisker D Sc i ν ≫ lastToFirstHom D Sc i (ν ++ [i]) := by
  have hp' : ¬D.parity i = 1 := by rw [hp]; decide
  have hg : sameIntertwiner D Sc (ν ++ [i] ++ [i]) ν.length i ≫
        crossE D Sc (ν ++ [i] ++ [i]) ν.length =
      (dotE D Sc (ν ++ [i] ++ [i]) (ν.length + 1) - dotE D Sc (ν ++ [i] ++ [i]) ν.length) ≫
        crossE D Sc (ν ++ [i] ++ [i]) ν.length := by
    simp only [sameIntertwiner, hp', ↓reduceIte]
    rw [← End.mul_def, (evenTwo_append_self D Sc i hp ν).t_mul_gEven]
    rfl
  rw [moveHom_append_self, lastToFirstHom_append_self, Category.assoc,
    ← Category.assoc (sameIntertwiner _ _ _ _ _), hg]
  simp only [Category.assoc]
  rw [moveWhisker_comp_sub_assoc, zsign_parity_even D i hp ν, one_smul]

end OddMath.QuiverHecke
