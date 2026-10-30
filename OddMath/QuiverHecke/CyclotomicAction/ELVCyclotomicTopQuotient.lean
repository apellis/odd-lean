/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.ELVCyclotomicCrossingTensor

/-! # The canonical quotient of the short crossing tensor

The map changes the affine first factor to its cyclotomic class and changes
the lower balance from the affine category to its cyclotomic quotient.
The coefficient factor already has its prescribed cyclotomic quotient.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory TensorProduct
namespace OddMath.QuiverHecke.ELVOld
universe u
variable {I X k : Type u} [AddCommGroup X] [CommRing k]
  (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ)
namespace CyclotomicCrossingTensor

/-- Words with the full affine coefficient-category Hom spaces. -/
structure AffineWord (D : SKM.Datum I X) (Sc : SKM.Scalars D k) (cutoff : I → ℕ) where
  word : List I

instance : Category (AffineWord D Sc cutoff) where
  Hom v w := hom D Sc cutoff v.word w.word
  id v := 𝟙 (obj D Sc cutoff v.word)
  comp f g := f ≫ g
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

instance : Preadditive (AffineWord D Sc cutoff) where
  homGroup v w := inferInstanceAs (AddCommGroup (hom D Sc cutoff v.word w.word))
  add_comp := by
    intro v w z f g h
    exact Preadditive.add_comp (obj D Sc cutoff v.word) (obj D Sc cutoff w.word)
      (obj D Sc cutoff z.word) f g h
  comp_add := by
    intro v w z f g h
    exact Preadditive.comp_add (obj D Sc cutoff v.word) (obj D Sc cutoff w.word)
      (obj D Sc cutoff z.word) f g h

instance : Linear k (AffineWord D Sc cutoff) where
  homModule v w := inferInstanceAs (Module k (hom D Sc cutoff v.word w.word))
  smul_comp := by
    intro v w z r f g
    exact Linear.smul_comp (obj D Sc cutoff v.word) (obj D Sc cutoff w.word)
      (obj D Sc cutoff z.word) r f g
  comp_smul := by
    intro v w z f r g
    exact Linear.comp_smul (obj D Sc cutoff v.word) (obj D Sc cutoff w.word)
      (obj D Sc cutoff z.word) f r g

/-- The identity-on-words cyclotomic quotient. -/
def quotient : AffineWord D Sc cutoff ⥤ OldCategory D Sc cutoff where
  obj v := ⟨v.word⟩
  map {v w} := (ideal D Sc cutoff v.word w.word).mkQ
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Affine right append, before imposing either old ideal. -/
def affineAppend (i : I) : AffineWord D Sc cutoff ⥤ AffineWord D Sc cutoff where
  obj v := ⟨v.word ++ [i]⟩
  map {v w} := rightContext D Sc cutoff [i] v.word w.word
  map_id _ := rightContext_id D Sc cutoff [i] _
  map_comp f g := rightContext_comp D Sc cutoff [i] f g

/-- `Re ⊗_S Πᵖ(eB)`, balanced before quotienting the first factor. -/
abbrev ShortTarget (i : I) (v t : List I) :=
  BalancedInduction.Obj (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i) i v)
    (⟨t⟩ : AffineWord D Sc cutoff)

def shortTensor (i : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    ShortTarget D Sc cutoff i v t :=
  BalancedInduction.tensor (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i) i v) ⟨s⟩ c b

/-- Quotienting the first factor on one tensor summand. -/
def qSummand (i : I) (v s t : List I) :
    hom D Sc cutoff (s ++ [i]) t ⊗[k] Old D Sc cutoff v (s ++ [i]) →ₗ[k]
      Source D Sc cutoff i v t :=
  BalancedInduction.inclusion (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩ ⟨s⟩ ∘ₗ
      TensorProduct.map (ideal D Sc cutoff (s ++ [i]) t).mkQ LinearMap.id

@[simp] theorem qSummand_tmul (i : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    qSummand D Sc cutoff i v s t (c ⊗ₜ[k] b) =
      tensor D Sc cutoff i v s t ((ideal D Sc cutoff _ _).mkQ c) b := rfl

theorem qSummand_balance (i : I) (v s s' t : List I)
    (r : hom D Sc cutoff s s') (c : hom D Sc cutoff (s' ++ [i]) t)
    (b : Old D Sc cutoff v (s ++ [i])) :
    qSummand D Sc cutoff i v s t ((rightContext D Sc cutoff [i] _ _ r ≫ c) ⊗ₜ[k] b) =
      qSummand D Sc cutoff i v s' t (c ⊗ₜ[k]
        (coefficient D Sc cutoff (D.parity i) i v).map
          ((ideal D Sc cutoff s s').mkQ r) b) := by
  rw [qSummand_tmul, qSummand_tmul]
  exact BalancedInduction.balance (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i) i v)
    ((ideal D Sc cutoff s s').mkQ r)
    ((ideal D Sc cutoff (s' ++ [i]) t).mkQ c) b

/-- The canonical quotient changes only the first tensor factor. -/
def q (i : I) (v t : List I) : ShortTarget D Sc cutoff i v t →ₗ[k]
    Source D Sc cutoff i v t :=
  BalancedInduction.lift (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩
    (fun s => qSummand D Sc cutoff i v s.word t)
    (fun s s' r c b => qSummand_balance D Sc cutoff i v s.word s'.word t r c b)

@[simp] theorem q_shortTensor (i : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : Old D Sc cutoff v (s ++ [i])) :
    q D Sc cutoff i v t (shortTensor D Sc cutoff i v s t c b) =
      tensor D Sc cutoff i v s t ((ideal D Sc cutoff _ _).mkQ c) b := by
  exact BalancedInduction.lift_tensor (affineAppend D Sc cutoff i)
    (quotient D Sc cutoff ⋙ coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩ _ _ ⟨s⟩ c b

/-- The canonical quotient is surjective without flatness or projectivity. -/
theorem q_surjective (i : I) (v t : List I) : Function.Surjective (q D Sc cutoff i v t) := by
  classical
  intro z
  obtain ⟨z, rfl⟩ := (BalancedInduction.relations (append D Sc cutoff i)
    (coefficient D Sc cutoff (D.parity i) i v) ⟨t⟩).mkQ_surjective z
  induction z using DirectSum.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | add x y hx hy =>
    obtain ⟨x', hx'⟩ := hx
    obtain ⟨y', hy'⟩ := hy
    exact ⟨x' + y', by rw [map_add, hx', hy', map_add]⟩
  | of s z =>
    induction z using TensorProduct.inductionOn with
    | add x y hx hy =>
      obtain ⟨x', hx'⟩ := hx
      obtain ⟨y', hy'⟩ := hy
      exact ⟨x' + y', by rw [map_add, hx', hy', map_add, map_add]⟩
    | tmul c b =>
      obtain ⟨c, rfl⟩ := (ideal D Sc cutoff (s.word ++ [i]) t).mkQ_surjective c
      exact ⟨shortTensor D Sc cutoff i v s.word t c b, q_shortTensor D Sc cutoff i v s.word t c b⟩

/-- The descended vertical map has the literal crossing-column formula on lifts. -/
theorem toCyclotomic_q_shortTensor (i : I) (v s t : List I)
    (c : hom D Sc cutoff (s ++ [i]) t) (b : hom D Sc cutoff v (s ++ [i])) :
    toCyclotomic D Sc cutoff i v t
      (q D Sc cutoff i v t (shortTensor D Sc cutoff i v s t c
        ((ideal D Sc cutoff _ _).mkQ b))) =
    (ideal D Sc cutoff (v ++ [i]) (t ++ [i])).mkQ
      (rightContext D Sc cutoff [i] _ _ b ≫
        affineUnit D Sc cutoff _ _ (crossLast D Sc s i i) ≫
        rightContext D Sc cutoff [i] _ _ c) := by
  rw [q_shortTensor, toCyclotomic_tensor_mk]

end CyclotomicCrossingTensor
end OddMath.QuiverHecke.ELVOld
