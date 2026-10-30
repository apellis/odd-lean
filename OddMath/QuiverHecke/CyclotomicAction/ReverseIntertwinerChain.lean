/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerMeet

/-!
# Reverse moving chains and their local norms

The affine reverse of the moving chain in Kang–Kashiwara–Oh, with the
local squares used in `DeformedBoundaryDivision.md` §2.
The reverse chain reverses factors; it is not asserted to be an inverse.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams SignedNilHecke IntertwinerMeet
open scoped Classical

variable {I : Type*} {X : Type*} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type*} [CommRing k] (Sc : SKM.Scalars D k)

/-- The moving chain with its factors reversed, from the append word to the prepend word. -/
def reverseMoveHom (i : I) : (l ν : List I) →
    (pres D Sc).obj (ob D (l ++ ν ++ [i])) ⟶ (pres D Sc).obj (ob D (l ++ i :: ν))
  | l, [] => eqToHom (by simp)
  | l, j :: ν =>
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) (by simp)) ≫
        reverseMoveHom i (l ++ [j]) ν ≫
          eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t))
            (show (l ++ [j]) ++ i :: ν = l ++ [j, i] ++ ν by simp)) ≫
            intertwinerHom D Sc l ν j i ≫
              eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t)) (by simp))

/-- The even repeated-colour square, with categorical composition in its affine block. -/
theorem intertwinerHom_square_even (l r : List I) (i : I) (hp : D.parity i = 0) :
    intertwinerHom D Sc l r i i ≫ intertwinerHom D Sc l r i i =
      -((dotE D Sc (l ++ [i, i] ++ r) (l.length + 1) -
        dotE D Sc (l ++ [i, i] ++ r) l.length) ^ 2) := by
  rw [intertwinerHom_self, ← End.mul_def]
  simp only [sameIntertwiner, hp, zero_ne_one, ite_false]
  simpa only [pow_two] using (evenTwo_block D Sc l r i hp).gEven_mul_gEven

/-- The odd repeated-colour square; no commutativity of the two odd dots is assumed. -/
theorem intertwinerHom_square_odd (l r : List I) (i : I) (hp : D.parity i = 1) :
    intertwinerHom D Sc l r i i ≫ intertwinerHom D Sc l r i i =
      -((dotE D Sc (l ++ [i, i] ++ r) (l.length + 1) ^ 2 -
        dotE D Sc (l ++ [i, i] ++ r) l.length ^ 2) ^ 2 *
        (dotE D Sc (l ++ [i, i] ++ r) l.length ^ 2 +
          dotE D Sc (l ++ [i, i] ++ r) (l.length + 1) ^ 2)) := by
  rw [intertwinerHom_self, ← End.mul_def]
  simp only [sameIntertwiner, hp, ite_true]
  simpa only [pow_two, OddNilHecke.Intertwiner.squareDiff] using
    (oddTwo_block D Sc l r i hp).element_identities.1

/-- The unequal-colour square for a nonzero Cartan entry. -/
theorem intertwinerHom_square_ne (l r : List I) {i j : I}
    (hij : i ≠ j) (hd : D.d i j ≠ 0) :
    intertwinerHom D Sc l r i j ≫ intertwinerHom D Sc l r j i =
      qLeft (dotE D Sc (l ++ [i, j] ++ r) l.length)
        (dotE D Sc (l ++ [i, j] ++ r) (l.length + 1))
        (D.dn i j) (D.dn j i) (Sc.t i j : k) (Sc.t j i : k) (Sc.s i j) := by
  rw [intertwinerHom_of_ne D Sc l r hij,
    intertwinerHom_of_ne D Sc l r (Ne.symm hij), cl_comp]
  exact crossSq_gen D Sc l r hij hd rfl rfl _

/-- The unequal-colour square for disconnected colours. -/
theorem intertwinerHom_square_ne_zero (l r : List I) {i j : I}
    (hij : i ≠ j) (hd : D.d i j = 0) :
    intertwinerHom D Sc l r i j ≫ intertwinerHom D Sc l r j i =
      (Sc.t i j : k) • 𝟙 _ := by
  rw [intertwinerHom_of_ne D Sc l r hij,
    intertwinerHom_of_ne D Sc l r (Ne.symm hij), cl_comp]
  exact crossSq_zero_gen D Sc l r hij hd rfl rfl _

/-- Polynomial local norm at the source word of an adjacent intertwiner. -/
def intertwinerSquare (l r : List I) (i j : I) :
    End ((pres D Sc).obj (ob D (l ++ [i, j] ++ r))) :=
  let u := dotE D Sc (l ++ [i, j] ++ r) l.length
  let v := dotE D Sc (l ++ [i, j] ++ r) (l.length + 1)
  if i = j then
    if D.parity i = 1 then -((v ^ 2 - u ^ 2) ^ 2 * (u ^ 2 + v ^ 2))
    else -((v - u) ^ 2)
  else if D.d i j = 0 then (Sc.t i j : k) • 𝟙 _
  else qLeft u v (D.dn i j) (D.dn j i) (Sc.t i j : k) (Sc.t j i : k) (Sc.s i j)

/-- The local square in all parity and Cartan cases. -/
theorem intertwinerHom_comp_reverse (l r : List I) (i j : I) :
    intertwinerHom D Sc l r i j ≫ intertwinerHom D Sc l r j i =
      intertwinerSquare D Sc l r i j := by
  by_cases hij : i = j
  · subst j
    by_cases hp : D.parity i = 1
    · simpa only [intertwinerSquare, ite_true, hp] using
        intertwinerHom_square_odd D Sc l r i hp
    · simpa only [intertwinerSquare, ite_true, hp, ite_false] using
        intertwinerHom_square_even D Sc l r i (parity_eq_zero_of_ne_one hp)
  · by_cases hd : D.d i j = 0
    · simpa only [intertwinerSquare, hij, hd, ite_false, ite_true] using
        intertwinerHom_square_ne_zero D Sc l r hij hd
    · simpa only [intertwinerSquare, hij, hd, ite_false] using
        intertwinerHom_square_ne D Sc l r hij hd

/-- The norm of the empty chain is the identity on the append word. -/
theorem reverseMoveHom_comp_moveHom_nil (i : I) (l : List I) :
    reverseMoveHom D Sc i l [] ≫ moveHom D Sc i l [] = 𝟙 _ := by
  simp [reverseMoveHom, moveHom]

/-- Remove the adjacent pair in the append-end norm. The local factor is at the
swapped word `(l,j,i,ν)`, as required by the order of categorical composition. -/
theorem reverseMoveHom_comp_moveHom_cons (i j : I) (l ν : List I) :
    reverseMoveHom D Sc i l (j :: ν) ≫ moveHom D Sc i l (j :: ν) =
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t))
        (show l ++ (j :: ν) ++ [i] = (l ++ [j]) ++ ν ++ [i] by simp)) ≫
      reverseMoveHom D Sc i (l ++ [j]) ν ≫
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t))
        (show (l ++ [j]) ++ i :: ν = l ++ [j, i] ++ ν by simp)) ≫
      intertwinerSquare D Sc l ν j i ≫
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t))
        (show l ++ [j, i] ++ ν = (l ++ [j]) ++ i :: ν by simp)) ≫
      moveHom D Sc i (l ++ [j]) ν ≫
      eqToHom (congrArg (fun t => (pres D Sc).obj (ob D t))
        (show (l ++ [j]) ++ ν ++ [i] = l ++ (j :: ν) ++ [i] by simp)) := by
  simp only [reverseMoveHom, moveHom, Category.assoc]
  simp only [eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  rw [← Category.assoc (intertwinerHom D Sc l ν j i),
    intertwinerHom_comp_reverse]

/-- On a singleton, the append-end norm is exactly the local polynomial square. -/
theorem reverseMoveHom_comp_moveHom_singleton (i j : I) :
    reverseMoveHom D Sc i [] [j] ≫ moveHom D Sc i [] [j] =
      intertwinerSquare D Sc [] [] j i := by
  simpa only [reverseMoveHom, moveHom, List.nil_append, List.append_nil,
    List.cons_append, eqToHom_refl, Category.id_comp, Category.comp_id] using
    intertwinerHom_comp_reverse D Sc [] [] j i

end OddMath.QuiverHecke
