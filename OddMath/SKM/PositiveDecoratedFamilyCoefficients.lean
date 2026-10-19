/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.SKM.PositiveDecoratedCoefficients
import OddMath.SKM.PositiveDecoratedEnumeration

/-!
# Coefficients of the canonical positive decorated family

For [BE2, arXiv:1701.04133v2, proof of Theorem 10.3, Claim 1], sum the
single-matching coefficient formula over the existing canonical `decoratedFamily₂`.
The §8 representative coverage and uniqueness are explicit. Finiteness of every
integer-degree fiber is proved, not assumed; degrees are ordinary diagram degrees.

The placement and ordinary lifts are chosen before all degrees. The same placement
is supplied to `positive_topDotMoves_family_equiv`, so no equality between independent
choices is needed. Crossings use source colours, whereas dot counts and `dotSeries`
use target colours. The integer crossing shift is guarded before taking `Int.toNat`.
Only `CommRing` and `π ^ 2 = 1` are required of the coefficient ring.

This supports the equal-length positive, canonical-point case of Claim 1. It does
not prove arbitrary-point or selector invariance, unequal-length vanishing, or the
comparison with the algebraic form. In particular no map from the entire rational
function coefficient field, and no removal of the algebraic form's finite-colour or
`BarConsistent` restrictions, is asserted.
-/

noncomputable section
namespace OddMath.SKM
open StringDiagrams StringDiagrams.Chord
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {I X k : Type*} [AddCommGroup X] [CommRing k]
variable (Q : CoveringQuantum.RootDatum I X) (μ : X)
variable (π : k) (hπ : π ^ 2 = 1) {n : ℕ} (a b : Fin n → I)
local notation "A" => (List.ofFn fun r => (true, a r))
local notation "B" => (List.ofFn fun r => (true, b r))
private theorem sum_fibers_equiv {α β G k : Type*} [Fintype α] [AddCommMonoid k]
    (F : (α × β) ≃ G) (d : G → ℤ) (v : G → k) (z : ℤ)
    (hf : ∀ a, Set.Finite {b : β | d (F (a, b)) = z}) :
    ∃ hg : Set.Finite {g : G | d g = z},
      (∑ g ∈ hg.toFinset, v g) = ∑ a, ∑ b ∈ (hf a).toFinset, v (F (a, b)) := by
  classical
  let S : Finset (Σ _ : α, β) := Finset.univ.sigma fun a => (hf a).toFinset
  let E := (Equiv.sigmaEquivProd α β).trans F
  have hm (x : Σ _ : α, β) : x ∈ S ↔ d (E x) = z := by
    simp [S, E]
  have hg : Set.Finite {g : G | d g = z} := by
    apply (S.finite_toSet.image E).subset
    intro g hg
    exact ⟨E.symm g, (hm _).mpr (by simpa using hg), E.apply_symm_apply g⟩
  refine ⟨hg, ?_⟩
  calc
    (∑ g ∈ hg.toFinset, v g) = ∑ x ∈ S, v (E x) := by
      symm
      apply Finset.sum_bij (fun x _ => E x)
      · intro x hx
        exact hg.mem_toFinset.mpr ((hm x).mp hx)
      · intro x _ y _ h
        exact E.injective h
      · intro g hg'
        exact ⟨E.symm g, (hm _).mpr (by simpa using hg.mem_toFinset.mp hg'),
          E.apply_symm_apply g⟩
      · intro _ _
        rfl
    _ = _ := Finset.sum_sigma _ _ _

include hπ in
/-- Coefficientwise enumeration of the existing canonical decorated family supporting
[BE2, arXiv:1701.04133v2, Theorem 10.3, proof of Claim 1]. The representative hypotheses
are those of §8. One certified top placement and an ordinary realization with exactly
the given extended layers work in every integer degree. The finite permutation sum
uses bottom-to-top permutations, source-indexed crossings, and target-indexed dots.
This is not the comparison with the algebraic form or arbitrary-point invariance. -/
theorem positive_decorated_family_coeff
    (M : Set (List (TMove (Letter I))))
    (hM : ∀ R ∈ M, IsMatching₂ A B R ∧ StrictReduced₂ A R)
    (hrep : ∀ R', IsMatching₂ A B R' → StrictReduced₂ A R' →
      ∃ R ∈ M, Iso (pairing₂ A R) (pairing₂ A R'))
    (huniq : ∀ R ∈ M, ∀ S ∈ M,
      Iso (pairing₂ A R) (pairing₂ A S) → R = S) :
  let C := Q.toSuperCartanDatum
  let κ : Equiv.Perm (Fin n) → ℤ := fun w =>
    ∑ r, ∑ s with r < s ∧ w s < w r, -C.dot (a r) (a s)
  let ε : Equiv.Perm (Fin n) → ZMod 2 := fun w =>
    ∑ r, ∑ s with r < s ∧ w s < w r, Q.parity (a r) * Q.parity (a s)
  ∃ p : ∀ R : {R // R ∈ M}, MatchingStrand A R.val ≃ Fin n,
    (∀ R (j : MatchingStrand A R.val),
      OnStrand₂ A R.val j.val (R.val.length, (p R j).val)) ∧
    (let family := decoratedFamily₂ A M
       (fun R c => topDotMoves A R (topPositionExtension M p R) (fun j => c j))
     let G := {D // D ∈ family}
     ∃ (L : G → List (LayerData I)) (hL : ∀ D, SChain A (L D) B),
       (∀ D, (L D).map ofL = D.val) ∧
       ∀ z : ℤ, ∃ hf : Set.Finite {D : G |
         Diagram.degree (gdeg Q.toSKM Q.skmSymmetrizer)
           (mkD Q.toSKM μ (L D) (hL D)) = z},
         (∑ D ∈ hf.toFinset, π ^ (xpar Q.toSKM μ D.val).val) =
           ∑ w : Equiv.Perm (Fin n), if ∀ r, a r = b (w r) then
             if κ w ≤ z then π ^ (ε w).val *
               PowerSeries.coeff (z - κ w).toNat (C.dotSeries π b)
             else 0
           else 0) := by
  classical
  dsimp only
  obtain ⟨E, hE⟩ := positive_representatives_equiv a b M hM hrep huniq
  let : Fintype {R // R ∈ M} := Fintype.ofEquiv _ E.symm
  have hc (R : {R // R ∈ M}) := positive_decorated_coeff Q μ π hπ a b
    (hM R R.property).1 (hM R R.property).2 (E R).val (hE R)
  choose p hp L hL hmap hcoeff using hc
  obtain ⟨F, hF⟩ := positive_topDotMoves_family_equiv a b M hM p
  refine ⟨p, hp, (fun D => L (F.symm D).1 (F.symm D).2),
    (fun D => hL (F.symm D).1 (F.symm D).2), ?_, ?_⟩
  · intro D
    rw [hmap, ← hF (F.symm D), F.apply_symm_apply]
  · intro z
    choose hf hs using fun R => hcoeff R z
    have hfinite (R : {R // R ∈ M}) :
        Set.Finite {c : Fin n → ℕ |
          Diagram.degree (gdeg Q.toSKM Q.skmSymmetrizer)
            (mkD Q.toSKM μ (L (F.symm (F (R, c))).1 (F.symm (F (R, c))).2)
              (hL (F.symm (F (R, c))).1 (F.symm (F (R, c))).2)) = z} := by
      simpa only [F.symm_apply_apply] using hf R
    obtain ⟨hg, hgSum⟩ := sum_fibers_equiv F
      (fun D => Diagram.degree (gdeg Q.toSKM Q.skmSymmetrizer)
        (mkD Q.toSKM μ (L (F.symm D).1 (F.symm D).2)
          (hL (F.symm D).1 (F.symm D).2)))
      (fun D => π ^ (xpar Q.toSKM μ D.val).val) z hfinite
    refine ⟨hg, hgSum.trans ?_⟩
    have hfinset (R : {R // R ∈ M}) : (hfinite R).toFinset = (hf R).toFinset := by
      ext c
      simp only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, F.symm_apply_apply]
    simp_rw [hfinset, hF, ← hmap]
    simp_rw [hs]
    let v : Equiv.Perm (Fin n) → k := fun w =>
      if (∑ r, ∑ s with r < s ∧ w s < w r, -Q.toSuperCartanDatum.dot (a r) (a s)) ≤ z then
        π ^ (∑ r, ∑ s with r < s ∧ w s < w r, Q.parity (a r) * Q.parity (a s)).val *
          PowerSeries.coeff
            (z - ∑ r, ∑ s with r < s ∧ w s < w r, -Q.toSuperCartanDatum.dot (a r) (a s)).toNat
            (Q.toSuperCartanDatum.dotSeries π b)
      else 0
    change (∑ R, v (E R).val) = ∑ w, if ∀ r, a r = b (w r) then v w else 0
    calc
      _ = ∑ w : {w : Equiv.Perm (Fin n) // ∀ r, a r = b (w r)}, v w.val :=
        Fintype.sum_equiv E _ _ (fun _ => rfl)
      _ = _ := by
        rw [← Finset.sum_subtype (Finset.univ.filter (fun w => ∀ r, a r = b (w r)))
          (by intro w; simp) v]
        exact Finset.sum_filter _ _
end OddMath.SKM
