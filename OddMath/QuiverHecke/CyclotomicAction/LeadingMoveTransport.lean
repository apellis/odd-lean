/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.LeadingMovePolynomial

/-!
# Source transport for a leading moving-strand expansion

`collectedSourceSign_leadingMoveBlocks` eliminates the transport coefficient.
`collectedSourceDots_leadingMoveBlocks` evaluates the original collection recursion
at explicit moving and old-strand source positions. Together they identify the
source dot word needed for the ordered moving-strand polynomial product.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification.TypeA
open scoped Classical
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k]

theorem sourceDotPosition_append (σ τ : List ℕ) (p : ℕ) :
    sourceDotPosition (σ ++ τ) p = sourceDotPosition τ (sourceDotPosition σ p) := by
  induction σ generalizing p with
  | nil => rfl
  | cons a σ ih => exact ih (swapNat a p)

theorem sourceDotSign_append (t : List I) (σ τ : List ℕ) (p : ℕ) :
    sourceDotSign D (k := k) t (σ ++ τ) p =
      sourceDotSign D (tgt t (cw τ)) σ p *
        sourceDotSign D t τ (sourceDotPosition σ p) := by
  induction σ generalizing p with
  | nil => simp [sourceDotSign, sourceDotPosition]
  | cons a σ ih =>
    simp [sourceDotSign, sourceDotPosition, cw_append, tgt_append, ih, mul_assoc]

theorem sourceDotSign_sq (t : List I) (σ : List ℕ) (p : ℕ) :
    sourceDotSign D (k := k) t σ p * sourceDotSign D t σ p = 1 := by
  induction σ generalizing p with
  | nil => simp [sourceDotSign]
  | cons a σ ih =>
    have hs (q : ZMod 2) : SKM.zsign k q * SKM.zsign k q = 1 := by
      unfold SKM.zsign; split_ifs <;> simp
    rw [sourceDotSign, mul_mul_mul_comm, hs, ih, one_mul]

theorem collectedSourceDots_snoc (bs : List (ℕ × List ℕ)) (a : ℕ) (ps : List ℕ) :
    collectedSourceDots (bs ++ [(a, ps)]) =
      ps.map (swapNat a) ++ (collectedSourceDots bs).map (swapNat a) := by
  induction bs with
  | nil => simp [collectedSourceDots, sourceDotPosition]
  | cons b bs ih =>
    simp [collectedSourceDots, ih, sourceDotPosition_append, sourceDotPosition,
      List.map_append, List.map_map, List.append_assoc, Function.comp_def]

private theorem collectedSourceSign_snoc_even (t : List I)
    (bs : List (ℕ × List ℕ)) (a : ℕ) (ps : List ℕ)
    (ha : ∀ p, sourceDotSign D (k := k) t [a] p = 1) :
    collectedSourceSign D (k := k) t (bs ++ [(a, ps)]) =
      collectedSourceSign D (tgt t (cw [a])) bs := by
  have hs (σ qs : List ℕ) : sourceDotsSign D (k := k) t (σ ++ [a]) qs =
      sourceDotsSign D (tgt t (cw [a])) σ qs := by
    have hf : sourceDotSign D (k := k) t (σ ++ [a]) =
        sourceDotSign D (tgt t (cw [a])) σ := by
      funext p
      rw [sourceDotSign_append, ha, mul_one]
    simp only [sourceDotsSign, hf]
  have hf : sourceDotSign D (k := k) t [a] = fun _ => 1 := funext ha
  induction bs with
  | nil => simp [collectedSourceSign, sourceDotsSign, hf]
  | cons b bs ih =>
    simp only [List.cons_append, collectedSourceSign, ih, List.map_append,
      List.map_cons, List.map_nil]
    rw [show b.1 :: (bs.map Prod.fst ++ [a]) = (b.1 :: bs.map Prod.fst) ++ [a] from rfl, hs]

private theorem sourceDotsSign_leadingBlock_odd (i j : I) (hi : D.parity i = 1)
    (t : List I) (σ : List ℕ) (a : ℕ) (c : Fin 4) :
    sourceDotsSign D (k := k) t σ (leadingBlockDots D i j a c) = 1 := by
  by_cases hij : i = j
  · subst j
    fin_cases c <;>
      simp [leadingBlockDots, hi, sourceDotsSign, sourceDotSign_sq]
  · simp [leadingBlockDots, hij, sourceDotsSign]

private theorem collectedSourceSign_of_blocks (t : List I) (bs : List (ℕ × List ℕ))
    (h : ∀ b ∈ bs, ∀ σ, sourceDotsSign D (k := k) t σ b.2 = 1) :
    collectedSourceSign D (k := k) t bs = 1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    rw [collectedSourceSign, h b (by simp), mul_one]
    exact ih (fun d hd => h d (by simp [hd]))

/-- Every computed transport coefficient is one, including all distant odd slides. -/
theorem collectedSourceSign_leadingMoveBlocks (i : I) (l ν : List I)
    (c : MoveChoices ν) :
    collectedSourceSign D (k := k) (l ++ i :: ν) (leadingMoveBlocks D i l ν c) = 1 := by
  rcases Supercategory.parity_eq_zero_or_one (D.parity i) with hi | hi
  · induction ν generalizing l with
    | nil => rfl
    | cons j ν ih =>
      have ha : ∀ p, sourceDotSign D (k := k) (l ++ i :: j :: ν) [l.length] p = 1 := by
        intro p
        have he : (PG.cross l.length).par D (l ++ i :: j :: ν) = 0 := by
          simp [PG.par, hi]
        simp [sourceDotSign, crossDotExponent, he, SKM.zsign]
      rw [leadingMoveBlocks, collectedSourceSign_snoc_even D _ _ _ _ ha]
      have ht : tgt (l ++ i :: j :: ν) (cw [l.length]) = (l ++ [j]) ++ i :: ν := by
        simpa [cw] using tgt_eq (sChain_crossAt l ν i j)
      rw [ht]
      exact ih (l ++ [j]) c.2
  · apply collectedSourceSign_of_blocks
    intro b hb σ
    have h : ∀ l ν (c : MoveChoices ν), ∀ b ∈ leadingMoveBlocks D i l ν c,
        ∀ t, sourceDotsSign D (k := k) t σ b.2 = 1 := by
      intro l ν
      induction ν generalizing l with
      | nil => simp [leadingMoveBlocks]
      | cons j ν ih =>
        intro c b hb t
        simp only [leadingMoveBlocks, List.mem_append, List.mem_singleton] at hb
        rcases hb with hb | rfl
        · exact ih _ c.2 _ hb t
        · exact sourceDotsSign_leadingBlock_odd D i j hi t σ _ c.1
    exact h l ν c b hb _

/-- A local block at its source endpoints: `m` is the moving strand and `p` the old strand. -/
def leadingSourceBlockDots (i j : I) (m p : ℕ) (c : Fin 4) : List ℕ :=
  if i = j then
    if D.parity i = 1 then
      match c.val with
      | 0 => [m, m, m, m]
      | 1 => [p, p, m, m]
      | 2 => [m, m, p, p]
      | _ => [p, p, p, p]
    else
      match c.val with
      | 0 => [m, m]
      | 1 => [p, m]
      | 2 => [m, p]
      | _ => [p, p]
  else []

/-- Explicit source positions, in collection order. At old index `b`, the old
strand has position `a + b + 1`, while the moving strand stays at `m`. -/
def leadingSourceDots (i : I) (m a : ℕ) :
    (ν : List I) → MoveChoices ν → List ℕ
  | [], _ => []
  | j :: ν, c => leadingSourceBlockDots D i j m (a + 1) c.1 ++
      leadingSourceDots i m (a + 1) ν c.2

private theorem leadingSourceBlockDots_map (i j : I) (m p : ℕ) (c : Fin 4)
    (f : ℕ → ℕ) :
    (leadingSourceBlockDots D i j m p c).map f =
      leadingSourceBlockDots D i j (f m) (f p) c := by
  unfold leadingSourceBlockDots
  split_ifs <;> fin_cases c <;> rfl

private theorem leadingSourceDots_map (i : I) (m m' a : ℕ) (ν : List I)
    (c : MoveChoices ν) (f : ℕ → ℕ) (hm : f m = m')
    (hp : ∀ b, a ≤ b → f (b + 1) = b + 1) :
    (leadingSourceDots D i m a ν c).map f = leadingSourceDots D i m' a ν c := by
  induction ν generalizing a with
  | nil => rfl
  | cons j ν ih =>
    simp only [leadingSourceDots, List.map_append, leadingSourceBlockDots_map, hm,
      hp a le_rfl]
    rw [ih (a + 1) c.2 (fun b hb => hp b (by omega))]

private theorem leadingBlockDots_swap (i j : I) (a : ℕ) (c : Fin 4) :
    (leadingBlockDots D i j a c).map (swapNat a) =
      leadingSourceBlockDots D i j a (a + 1) c := by
  unfold leadingBlockDots leadingSourceBlockDots
  split_ifs <;> fin_cases c <;> simp [swapNat]

/-- Evaluation of the original collected dot list at explicit source positions,
for arbitrary prefixes, words, choices and parity of the moving colour. -/
theorem collectedSourceDots_leadingMoveBlocks (i : I) (l ν : List I)
    (c : MoveChoices ν) :
    collectedSourceDots (leadingMoveBlocks D i l ν c) =
      leadingSourceDots D i l.length l.length ν c := by
  induction ν generalizing l with
  | nil => rfl
  | cons j ν ih =>
    rw [leadingMoveBlocks, collectedSourceDots_snoc, ih, leadingBlockDots_swap]
    simp only [List.length_append, List.length_singleton]
    rw [leadingSourceDots_map D i (l.length + 1) l.length (l.length + 1) ν c.2
      (swapNat l.length) (by simp [swapNat])
      (by intro b hb; simp [swapNat, show b + 1 ≠ l.length by omega,
        show b ≠ l.length by omega])]
    rfl

end OddMath.QuiverHecke
