/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerRelation
import OddMath.QuiverHecke.CyclotomicAction.MoveHomSnoc
import OddMath.QuiverHecke.MixedRelations

/-!
# The last-to-first crossing map as a positioned word

The map `lastToFirstHom i ν : ν ++ [i] → i :: ν` of the all-prefix identity (K) is the
crossing `Tₙ` of the global QP induction in `docs/Nondegeneracy/DeformedGlobalQP.md`, §3
(the deformed form of Kang–Kashiwara–Oh, arXiv:1206.5933v2, proof of Theorem 8.5). It is
defined by peeling the first letter of `ν`. This file writes it as the positioned word
`crossingDescent ν.length = [cross (n-1), …, cross 0]` and derives the recursion that peels
the last letter: `T_(n+1) = τ_n (T_n ⊗ 1)`.

* `lastToFirstHom_eq_cl`: `lastToFirstHom i ν` is the class of `crossingDescent ν.length`;
* `lastToFirstHom_append_singleton`: `lastToFirstHom i (ν ++ [x])` is the crossing at
  position `|ν|` followed by `lastToFirstHom i ν ⊗ 1_x`.

Arbitrary colours, parities and words.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams MonoidalCategory

universe u v
variable {I k : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X) [CommRing k]
  (Sc : SKM.Scalars D k)

/-- The crossings `cross (n-1), …, cross 0`, in this order. -/
def crossingDescent : ℕ → List PG
  | 0 => []
  | n + 1 => .cross n :: crossingDescent n

theorem crossingDescent_succ_shift : ∀ n : ℕ,
    crossingDescent (n + 1) = (crossingDescent n).map (PG.shift 1) ++ [.cross 0]
  | 0 => rfl
  | n + 1 => by
    show PG.cross (n + 1) :: crossingDescent (n + 1) =
      (PG.cross n :: crossingDescent n).map (PG.shift 1) ++ [.cross 0]
    rw [crossingDescent_succ_shift n, List.map_cons, PG.shift_cross, Nat.add_comm 1 n,
      List.cons_append]

theorem fits_crossingDescent (n : ℕ) : Fits (n + 1) (crossingDescent n) := by
  induction n with
  | zero => intro g hg; simp [crossingDescent] at hg
  | succ n ih =>
    intro g hg
    rw [crossingDescent, List.mem_cons] at hg
    rcases hg with rfl | hg
    · simp [PG.pos, PG.width]
    · have := ih g hg
      omega

/-- `lastToFirstHom i ν` is the class of the positioned word `crossingDescent |ν|`. -/
theorem lastToFirstHom_eq_cl (i : I) : ∀ ν : List I,
    ∃ h : SChain (ν ++ [i]) (pl (ν ++ [i]) (crossingDescent ν.length)) (i :: ν),
      lastToFirstHom D Sc i ν = cl D Sc _ _ (crossingDescent ν.length) h
  | [] => ⟨sChain_pl [i] [], by simp [lastToFirstHom, crossingDescent, cl_nil]⟩
  | j :: ν => by
    obtain ⟨h, hν⟩ := lastToFirstHom_eq_cl i ν
    have h₂ : SChain (j :: i :: ν) (pl (j :: i :: ν) [.cross 0]) (i :: j :: ν) := by
      simpa using sChain_crossAt [] ν j i
    have h₁ := (by rw [pl_shift]; simpa using sChain_wh h [j] [] :
      SChain ([j] ++ (ν ++ [i])) (pl ([j] ++ (ν ++ [i]))
        ((crossingDescent ν.length).map (PG.shift [j].length))) ([j] ++ (i :: ν)))
    refine ⟨?_, ?_⟩
    · rw [List.length_cons, crossingDescent_succ_shift]
      exact sChain_append_of h₁ h₂
    · rw [lastToFirstHom, hν, cl_whiskerLeft]
      refine (cl_comp D Sc (t := j :: (ν ++ [i])) (t₁ := j :: i :: ν) (t' := i :: j :: ν)
        _ _ h₁ h₂).trans ?_
      exact cl_congr_gs D Sc
        (by rw [show (j :: ν).length = ν.length + 1 from rfl, crossingDescent_succ_shift]; rfl) _ _

/-- KKO's `T_(n+1) = τ_n (T_n ⊗ 1)`: moving the last strand to the front first crosses it
past `x`, then past `ν`. -/
theorem lastToFirstHom_append_singleton (i x : I) (ν : List I) :
    lastToFirstHom D Sc i (ν ++ [x]) =
      cl D Sc (ν ++ [x] ++ [i]) (ν ++ [i] ++ [x]) [.cross ν.length]
          (by simpa using sChain_crossAt ν [] x i) ≫
        (lastToFirstHom D Sc i ν ▷ (pres D Sc).obj (ob D [x])) := by
  obtain ⟨h, hν⟩ := lastToFirstHom_eq_cl D Sc i ν
  obtain ⟨h', hν'⟩ := lastToFirstHom_eq_cl D Sc i (ν ++ [x])
  have hf : Fits (ν ++ [i]).length (crossingDescent ν.length) := by
    simpa using fits_crossingDescent ν.length
  rw [hν', hν, cl_whiskerRight D Sc _ h [x] hf, cl_comp]
  exact cl_congr_gs D Sc (by simp [crossingDescent]) _ _

end OddMath.QuiverHecke
