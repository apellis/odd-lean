/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.LeadingIntertwinerExpansion
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerBalance

/-!
# Finite expansion of the leading moving chain

Expand the recursive leading move into products of the four local terms of
`leadingIntertwinerHom_expansion`. Blocks are recorded from top to bottom,
with canonical chains and position bounds for signed dot normal ordering.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification.TypeA
open scoped Classical
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

def MoveChoices : List I → Type
  | [] => Unit
  | _ :: ν => Fin 4 × MoveChoices ν

instance moveChoicesFintype : (ν : List I) → Fintype (MoveChoices ν)
  | [] => inferInstanceAs (Fintype Unit)
  | _ :: ν => @instFintypeProd _ _ inferInstance (moveChoicesFintype ν)

def leadingMoveBlocks (i : I) : (l ν : List I) → MoveChoices ν → List (ℕ × List ℕ)
  | _, [], _ => []
  | l, j :: ν, c => leadingMoveBlocks i (l ++ [j]) ν c.2 ++
      [(l.length, leadingBlockDots D i j l.length c.1)]

def leadingMoveCoeff (i : I) : (ν : List I) → MoveChoices ν → k
  | [], _ => 1
  | j :: ν, c => leadingBlockCoeff D i j c.1 * leadingMoveCoeff i ν c.2

def leadingMoveWord : (l ν : List I) → List ℕ
  | _, [] => []
  | l, j :: ν => leadingMoveWord (l ++ [j]) ν ++ [l.length]

theorem leadingMoveBlocks_map_fst (i : I) (l ν : List I) (c : MoveChoices ν) :
    (leadingMoveBlocks D i l ν c).map Prod.fst = leadingMoveWord l ν := by
  induction ν generalizing l with
  | nil => rfl
  | cons j ν ih => simp [leadingMoveBlocks, leadingMoveWord, ih]

theorem leadingMoveBlocks_length (i : I) (l ν : List I) (c : MoveChoices ν) :
    (leadingMoveBlocks D i l ν c).length = ν.length := by
  induction ν generalizing l with
  | nil => rfl
  | cons j ν ih => simp [leadingMoveBlocks, ih]

theorem leadingMoveWord_valid (l ν : List I) :
    ValidWord (l.length + ν.length + 1) (leadingMoveWord l ν) := by
  induction ν generalizing l with
  | nil => intro a ha; simp [leadingMoveWord] at ha
  | cons j ν ih =>
    intro a ha
    simp only [leadingMoveWord, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · have h := ih (l ++ [j]) a ha
      simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    · simp only [List.length_cons]; omega

theorem leadingMoveBlocks_valid (i : I) (l ν : List I) (c : MoveChoices ν) :
    ValidWord (l.length + ν.length + 1) ((leadingMoveBlocks D i l ν c).map Prod.fst) := by
  rw [leadingMoveBlocks_map_fst]
  exact leadingMoveWord_valid l ν

theorem leadingMoveBlocks_dots_lt (i : I) (l ν : List I) (c : MoveChoices ν) :
    ∀ b ∈ leadingMoveBlocks D i l ν c, ∀ p ∈ b.2, p < l.length + ν.length + 1 := by
  induction ν generalizing l with
  | nil => simp [leadingMoveBlocks]
  | cons j ν ih =>
    intro b hb p hp
    simp only [leadingMoveBlocks, List.mem_append, List.mem_singleton] at hb
    rcases hb with hb | rfl
    · have h := ih (l ++ [j]) c.2 b hb p hp
      simpa [List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
    · exact leadingBlockDots_lt D i j (by simp only [List.length_cons]; omega) c.1 p hp

theorem decoratedCrossingGens_append (bs cs : List (ℕ × List ℕ)) :
    decoratedCrossingGens (bs ++ cs) = decoratedCrossingGens cs ++ decoratedCrossingGens bs := by
  induction bs with
  | nil => simp [decoratedCrossingGens]
  | cons b bs ih => simp [decoratedCrossingGens, ih, List.append_assoc]

theorem leadingMoveBlocks_sChain (i : I) (l ν : List I) (c : MoveChoices ν) :
    SChain (l ++ i :: ν)
      (pl (l ++ i :: ν) (decoratedCrossingGens (leadingMoveBlocks D i l ν c)))
      (l ++ ν ++ [i]) := by
  induction ν generalizing l with
  | nil => simp [leadingMoveBlocks, decoratedCrossingGens]
  | cons j ν ih =>
    have h₁ := leadingBlock_sChain D l ν i j c.1
    have h₂ := ih (l ++ [j]) c.2
    have h₁' : SChain (l ++ i :: j :: ν)
        (pl (l ++ i :: j :: ν)
          ([.cross l.length] ++ (leadingBlockDots D i j l.length c.1).map PG.dot))
        ((l ++ [j]) ++ i :: ν) := by simpa using h₁
    simpa [leadingMoveBlocks, decoratedCrossingGens_append, decoratedCrossingGens,
      List.append_assoc] using sChain_append_of h₁' h₂

private theorem cl_nil_eqToHom {t t' : List I} (e : t = t')
    (h : SChain t (pl t []) t') :
    cl D Sc t t' [] h = eqToHom (congrArg (fun s => (pres D Sc).obj (ob D s)) e) := by
  subst t'
  simp [cl_nil]

theorem leadingMoveHom_expansion (i : I) (l ν : List I) :
    leadingMoveHom D Sc i l ν =
      ∑ c : MoveChoices ν, leadingMoveCoeff D (k := k) i ν c •
        cl D Sc _ _ (decoratedCrossingGens (leadingMoveBlocks D i l ν c))
          (leadingMoveBlocks_sChain D i l ν c) := by
  induction ν generalizing l with
  | nil =>
    simp only [leadingMoveHom, leadingMoveCoeff, leadingMoveBlocks, decoratedCrossingGens,
      MoveChoices, Fintype.sum_unique, one_smul]
    exact (cl_nil_eqToHom D Sc (by simp) _).symm
  | cons j ν ih =>
    rw [leadingMoveHom, leadingIntertwinerHom_expansion, ih]
    simp only [Preadditive.comp_sum, Preadditive.sum_comp, Linear.comp_smul,
      Linear.smul_comp, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    rw [show (∑ c : MoveChoices (j :: ν), _) = _ from Fintype.sum_prod_type _]
    apply Finset.sum_congr rfl
    intro a ha
    apply Finset.sum_congr rfl
    intro b hb
    simp only [leadingMoveCoeff, leadingMoveBlocks, decoratedCrossingGens_append,
      decoratedCrossingGens, List.nil_append]
    rw [mul_comm (leadingMoveCoeff D i ν b)]
    congr 1
    rw [cl_comp_eqToHom D Sc _
      (show (l ++ [j]) ++ ν ++ [i] = l ++ (j :: ν) ++ [i] by simp),
      eqToHom_comp_cl D Sc
        (show l ++ [j,i] ++ ν = (l ++ [j]) ++ i :: ν by simp),
      cl_comp, eqToHom_comp_cl D Sc
        (show l ++ i :: j :: ν = l ++ [i,j] ++ ν by simp)]
end OddMath.QuiverHecke
