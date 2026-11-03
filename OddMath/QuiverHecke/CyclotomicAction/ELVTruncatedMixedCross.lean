/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVWeightedAppendCrossing
import OddMath.QuiverHecke.CyclotomicAction.ELVDistinctModuleMate

/-! # The positive two-colour crossing under coefficient truncation

Brundan–Ellis (1.12): the quotient crossing on successive singleton
appends retains the prescribed positive old crossing, including the
complete coefficient parity. Its existing two-letter append component
is identified under word associativity.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory MonoidalCategory
namespace OddMath.QuiverHecke.ELVOld
open CyclotomicCrossingTensor
universe u
private theorem mixed_mapFamily_heq {ι : Type*} {U V : ι → Type*}
    (F : ∀ a, U a → V a) {a b : ι} (h : a = b)
    {x : U a} {y : U b} (hxy : HEq x y) : HEq (F a x) (F b y) := by
  cases h
  cases hxy
  rfl

variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) (N : ℕ) (i j : I)
local notation "A" => truncatedAppend D Sc cutoff N [i]
local notation "B" => truncatedAppend D Sc cutoff N [j]
local notation "Q" => oldTruncateFunctor D Sc cutoff N

/-- The literal positive crossing j,i→i,j on successive truncated append functors. -/
def truncatedDistinctCrossComponent (s : TruncatedCategory D Sc cutoff N) :
    (B ⋙ A).obj s ⟶ (A ⋙ B).obj s :=
  (truncatedIdeal D Sc cutoff N _ _).mkQ
    (affineUnit D Sc cutoff _ _ (crossLast D Sc s.word j i))

/-- The selected old crossing projects to this exact two-colour quotient crossing. -/
theorem oldTruncateFunctor_map_distinctCross (s : OldCategory D Sc cutoff) :
    (Q).map (Distinct.crossComponent D Sc cutoff i j s) =
      truncatedDistinctCrossComponent D Sc cutoff N i j ((Q).obj s) := rfl

/-- The ordinary two-letter append crossing changes only its word-associativity endpoints. -/
theorem truncatedDistinctCrossComponent_heq (s : TruncatedCategory D Sc cutoff N) :
    HEq (truncatedDistinctCrossComponent D Sc cutoff N i j s)
      (truncatedAppendComponent D Sc cutoff N (crossTwo D Sc j i) s) := by
  have hw : (s.word ++ [j] ++ [i], s.word ++ [i] ++ [j]) =
      (s.word ++ [j, i], s.word ++ [i, j]) := by
    simp only [List.append_assoc, List.cons_append, List.nil_append]
  have hc := (conj_eqToHom_iff_heq _ _
    (congrArg (fun w => (pres D Sc).obj (ob D w)) (List.append_assoc s.word [j] [i]))
    (congrArg (fun w => (pres D Sc).obj (ob D w)) (List.append_assoc s.word [i] [j]))).mp
      (crossLast_eq D Sc s.word j i)
  have ha := mixed_mapFamily_heq
    (U := fun z : List I × List I =>
      (pres D Sc).obj (ob D z.1) ⟶ (pres D Sc).obj (ob D z.2))
    (V := fun z : List I × List I => hom D Sc cutoff z.1 z.2)
    (fun z f => affineUnit D Sc cutoff z.1 z.2 f) hw hc
  exact mixed_mapFamily_heq
    (U := fun z : List I × List I => hom D Sc cutoff z.1 z.2)
    (V := fun z : List I × List I => TruncatedOld D Sc cutoff N z.1 z.2)
    (fun z f => (truncatedIdeal D Sc cutoff N z.1 z.2).mkQ f) hw ha

/-- The positive crossing remains supernatural for all coefficient parities. -/
theorem truncatedDistinctCross_supernatural :
    IsSupernatural k (D.parity i * D.parity j)
      (truncatedDistinctCrossComponent D Sc cutoff N i j) := by
  apply IsSupernatural.of_twist
  · intro s
    rw [mul_comm (D.parity i) (D.parity j)]
    exact Submodule.mem_map_of_mem
      (ELVPScalar.affineUnit_mem D Sc cutoff (crossLast_mem D Sc s.word j i))
  · intro s t f
    obtain ⟨a, rfl⟩ := (truncatedIdeal D Sc cutoff N s.word t.word).mkQ_surjective f
    let f' : (⟨s.word⟩ : OldCategory D Sc cutoff) ⟶ ⟨t.word⟩ :=
      (ideal D Sc cutoff s.word t.word).mkQ a
    have h := congrArg (fun g => (Q).map g)
      ((Distinct.cross_supernatural D Sc cutoff i j).naturality_twist f')
    simp only [Functor.map_comp, map_twist] at h
    rw [map_twist]
    exact h

end OddMath.QuiverHecke.ELVOld
