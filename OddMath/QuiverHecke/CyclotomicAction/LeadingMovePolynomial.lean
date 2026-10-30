/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.LeadingMoveExpansion

/-!
# Collected endpoint polynomial of the leading moving chain

The finite polynomial is given explicitly by its chronological dot monomials.
Each coefficient is the product of the local four-term expansion coefficient
and the computed transport sign. No reordering of odd dots, choice of a unit,
or identification of a colour count with a dot degree is made.
-/
noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams Categorification.TypeA
open scoped Classical
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
  {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

/-- The undecorated crossing chain of the prescribed move. -/
theorem leadingMoveWord_sChain (i : I) (l ν : List I) :
    SChain (l ++ i :: ν) (pl (l ++ i :: ν) (cw (leadingMoveWord l ν)))
      (l ++ ν ++ [i]) := by
  induction ν generalizing l with
  | nil => simp [leadingMoveWord]
  | cons j ν ih =>
    have h := sChain_append_of (sChain_crossAt l ν i j) (by
      simpa using ih (l ++ [j]))
    simpa [leadingMoveWord, cw_append, cw, List.append_assoc] using h

/-- An ordered dot monomial at a fixed endpoint. Multiplication order is
chronological categorical composition, not increasing strand order. -/
def endpointDotMonomial (t : List I) (ps : List ℕ) :
    (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t) :=
  cl D Sc t t (ps.map PG.dot) (by simpa only [tgt_map_dot] using sChain_pl t (ps.map PG.dot))

/-- The explicitly expanded source-endpoint polynomial of the prescribed
moving chain. Local coefficients include the negative odd square factor;
transport coefficients include every incident and distant slide. -/
def leadingMoveEndpointPolynomial (i : I) (l ν : List I) :
    (pres D Sc).obj (ob D (l ++ i :: ν)) ⟶ (pres D Sc).obj (ob D (l ++ i :: ν)) :=
  ∑ c : MoveChoices ν,
    (leadingMoveCoeff D (k := k) i ν c *
      collectedSourceSign D (k := k) (l ++ i :: ν) (leadingMoveBlocks D i l ν c)) •
        endpointDotMonomial D Sc (l ++ i :: ν)
          (collectedSourceDots (leadingMoveBlocks D i l ν c))

/-- Applying signed decorated-block normal ordering to the finite expansion
of `leadingMoveHom` gives its concrete collected endpoint polynomial for
arbitrary words and either parity. -/
theorem leadingMoveHom_sub_endpointPolynomial_mem_low (i : I) (l ν : List I) :
    leadingMoveHom D Sc i l ν -
      leadingMoveEndpointPolynomial D Sc i l ν ≫
        cl D Sc _ _ (cw (leadingMoveWord l ν)) (leadingMoveWord_sChain i l ν) ∈
      Low D Sc (l ++ i :: ν) (l ++ ν ++ [i]) ν.length := by
  rw [leadingMoveHom_expansion, leadingMoveEndpointPolynomial]
  simp only [Preadditive.sum_comp, Linear.smul_comp, ← Finset.sum_sub_distrib]
  apply Submodule.sum_mem
  intro c hc
  obtain ⟨h', hh⟩ := decorated_crossings_normal_order D Sc
    (t' := l ++ ν ++ [i]) []
    (show (l ++ i :: ν).length = l.length + ν.length + 1 by simp; omega)
    (leadingMoveBlocks D i l ν c) (leadingMoveBlocks_valid D i l ν c)
    (leadingMoveBlocks_dots_lt D i l ν c) []
    (by simpa using leadingMoveBlocks_sChain D i l ν c)
  have hm := (Low D Sc (l ++ i :: ν) (l ++ ν ++ [i]) ν.length).smul_mem
    (leadingMoveCoeff D (k := k) i ν c)
    (show _ ∈ Low D Sc (l ++ i :: ν) (l ++ ν ++ [i]) ν.length from by
      simpa only [List.nil_append, List.append_nil, crossCount_nil, Nat.zero_add,
        Nat.add_zero, leadingMoveBlocks_length, tgt_nil] using hh)
  simpa only [smul_sub, smul_smul, endpointDotMonomial, cl_comp,
    leadingMoveBlocks_map_fst, List.nil_append, List.append_nil] using hm

/-- The collected formula also computes the top-crossing part of the
prescribed (not just leading) moving homomorphism. -/
theorem moveHom_sub_endpointPolynomial_mem_low (i : I) (l ν : List I) :
    moveHom D Sc i l ν -
      leadingMoveEndpointPolynomial D Sc i l ν ≫
        cl D Sc _ _ (cw (leadingMoveWord l ν)) (leadingMoveWord_sChain i l ν) ∈
      Low D Sc (l ++ i :: ν) (l ++ ν ++ [i]) ν.length := by
  have h := (Low D Sc _ _ ν.length).add_mem
    (moveHom_sub_leading_mem_low D Sc i l ν)
    (leadingMoveHom_sub_endpointPolynomial_mem_low D Sc i l ν)
  simpa only [sub_add_sub_cancel] using h

/-- Every longest scalar prepend coordinate is computed by the collected
polynomial. This includes indices with nonidentity old permutation. -/
theorem moveHom_long_prepend_repr_endpointPolynomial (i : I) (ν : List I)
    (x : PrependIdx i ν (ν ++ [i]))
    (hx : x.1.2.2.2 = longPrependShuffle ν.length) :
    (prependBasis D Sc (i := i) (s := ν) (t := ν ++ [i])).repr (moveHom D Sc i [] ν) x =
      (prependBasis D Sc (i := i) (s := ν) (t := ν ++ [i])).repr
        (leadingMoveEndpointPolynomial D Sc i [] ν ≫
          cl D Sc _ _ (cw (leadingMoveWord [] ν)) (leadingMoveWord_sChain i [] ν)) x := by
  have h := prependBasis_long_repr_eq_zero_of_low D Sc i ν (ν ++ [i]) _
    (moveHom_sub_endpointPolynomial_mem_low D Sc i [] ν) x hx
  simpa only [map_sub, Finsupp.sub_apply, sub_eq_zero, List.nil_append] using h

end OddMath.QuiverHecke
