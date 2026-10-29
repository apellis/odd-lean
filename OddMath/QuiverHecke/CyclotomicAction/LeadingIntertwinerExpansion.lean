/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.SignedDotNormalOrder

/-!
# Four-term expansion of a leading intertwiner

The local polynomial factors of `MoveHomLeading` are expanded without commuting
any dots. Lists record chronological output decorations after the crossing.
This supplies the local finite expansion for the moving-chain normal ordering.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
open scoped Classical
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- Chronological output dots of the four local monomials. -/
def leadingBlockDots (i j : I) (a : ℕ) (c : Fin 4) : List ℕ :=
  if i = j then
    if D.parity i = 1 then
      ![[a+1,a+1,a+1,a+1], [a,a,a+1,a+1], [a+1,a+1,a,a], [a,a,a,a]] c
    else ![[a+1,a+1], [a,a+1], [a+1,a], [a,a]] c
  else []

/-- Explicit local signs; unequal colours retain only the zeroth term. -/
def leadingBlockCoeff (i j : I) (c : Fin 4) : k :=
  if i = j then
    if D.parity i = 1 then ![-1,1,1,-1] c else ![1,-1,-1,1] c
  else if c = 0 then 1 else 0

/-- Every decoration stays within the two strands of the crossing. -/
theorem leadingBlockDots_lt (i j : I) {a n : ℕ} (ha : a + 1 < n)
    (c : Fin 4) : ∀ p ∈ leadingBlockDots D i j a c, p < n := by
  intro p hp
  unfold leadingBlockDots at hp
  split_ifs at hp <;> fin_cases c <;> simp at hp <;> omega

/-- Canonical chain from the input word to the swapped output word. -/
theorem leadingBlock_sChain (l r : List I) (i j : I) (c : Fin 4) :
    SChain (l ++ [i,j] ++ r)
      (pl (l ++ [i,j] ++ r)
        ([.cross l.length] ++ (leadingBlockDots D i j l.length c).map PG.dot))
      (l ++ [j,i] ++ r) := by
  have h := sChain_pl (l ++ [i,j] ++ r)
    ([.cross l.length] ++ (leadingBlockDots D i j l.length c).map PG.dot)
  simpa only [tgt_append, tgt_map_dot, tgt_eq (sChain_crossAt l r i j)] using h

/-- Exact four-term expansion, crossing first and output dots afterwards. -/
theorem leadingIntertwinerHom_expansion (l r : List I) (i j : I) :
    leadingIntertwinerHom D Sc l r i j =
      ∑ c : Fin 4, leadingBlockCoeff D (k := k) i j c •
        cl D Sc _ _
          ([.cross l.length] ++ (leadingBlockDots D i j l.length c).map PG.dot)
          (leadingBlock_sChain D l r i j c) := by
  by_cases hij : i = j
  · subst j
    by_cases hp : D.parity i = 1
    all_goals
      simp only [leadingIntertwinerHom, dite_true, Category.comp_id,
        eqToHom_refl, leadingSameIntertwiner, hp, ite_true, ite_false,
        Fin.sum_univ_succ, leadingBlockCoeff, leadingBlockDots,
        Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.isValue,
        List.map_cons, List.map_nil, List.cons_append, List.nil_append,
        neg_smul, one_smul, Fin.sum_univ_zero, add_zero]
      simp only [pow_two, sub_mul, mul_sub, neg_sub]
      rw [show crossE D Sc (l ++ [i,i] ++ r) l.length =
        cl D Sc _ _ [.cross l.length] (sChain_crossAt l r i i) from
          genE_eq D Sc (sChain_crossAt l r i i)]
      simp only [dotE_eq_cl D Sc (sChain_dotAny _ _), cl_mul,
        List.cons_append, List.nil_append]
      abel
  · simp [leadingIntertwinerHom, hij, leadingBlockCoeff, leadingBlockDots]

end OddMath.QuiverHecke
