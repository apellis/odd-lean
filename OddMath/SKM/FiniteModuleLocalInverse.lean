/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.Algebra.FiniteSupermoduleInverseRows
import OddMath.Algebra.FiniteSupermoduleInverseColumns
import OddMath.SKM.RouquierData

/-! # Extracting the finite local inverse entries

The parity-shifted column isomorphism in Brundan–Ellis (1.14) gives the
specified homogeneous augmented inverse, including the finite window
and its zero extension outside the window. No parity shift is erased.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
open scoped BigOperators
namespace OddMath.FiniteSupermodule
universe u v
variable {k : Type u} [CommRing k]
  {C : Type v} [Category C] [Preadditive C] [Linear k C] [Supercategory k C]
  {A B Z : Superfunctor k C (SVec k)} {n : ℕ}
  {V : Option (Fin n) → Superfunctor k C (SVec k)}

def optionTargetFamily (B Z : Superfunctor k C (SVec k)) (n : ℕ) :
    Option (Fin n) → Superfunctor k C (SVec k)
  | none => B
  | some _ => Z

def optionParityProfile (p : ZMod 2) (q : ℕ → ZMod 2) (n : ℕ) : Option (Fin n) → ZMod 2
  | none => p
  | some r => q r.val

def optionRestoringIso (r₀ : V none ≅ B) (r : ∀ a : Fin n, V (some a) ≅ Z) :
    ∀ a, V a ≅ optionTargetFamily B Z n a
  | none => r₀
  | some a => r a

def optionForwardColumns (f : B ⟶ A) (g : ℕ → (Z ⟶ A)) :
    ∀ a, optionTargetFamily B Z n a ⟶ A
  | none => f
  | some a => g a.val

section Columns

variable (p : ZMod 2) (q : ℕ → ZMod 2)
  (r₀ : V none ≅ B) (r : ∀ a : Fin n, V (some a) ≅ Z)
  (hr₀ : r₀.hom ∈ parity (R := k) _ _ p)
  (hr : ∀ a, (r a).hom ∈ parity (R := k) _ _ (q a.val))
  (f : B ⟶ A) (g : ℕ → (Z ⟶ A))
  (hf : f ∈ parity (R := k) _ _ p) (hg : ∀ m, g m ∈ parity (R := k) _ _ (q m))

include hr₀ hr in
private theorem optionRestoringIso_mem (a : Option (Fin n)) :
    (optionRestoringIso r₀ r a).hom ∈ parity (R := k) _ _ (optionParityProfile p q n a) := by
  cases a with
  | none => exact hr₀
  | some a => exact hr a

include hf hg in
private theorem optionForwardColumns_mem (a : Option (Fin n)) :
    optionForwardColumns f g a ∈ parity (R := k) _ _ (optionParityProfile p q n a) := by
  cases a with
  | none => exact hf
  | some a => exact hg a.val

variable (e : product V ≅ A)
  (he : e.hom = restoredColumns (optionRestoringIso r₀ r) (optionParityProfile p q n)
    (optionRestoringIso_mem p q r₀ r hr₀ hr) (optionForwardColumns f g)
    (optionForwardColumns_mem p q f g hf hg))

/-- The inverse row for a unit slot, extended by zero beyond the prescribed finite window. -/
def inverseUnitSlot (m : ℕ) : A ⟶ Z := by
  classical
  exact if hm : m < n then inverseCoordinateRow (optionRestoringIso r₀ r) e (some ⟨m, hm⟩) else 0

/-- A given even column matrix yields all specified local inverse entries and identities. -/
def localInverseFromColumns : SKM.SuperSumInvFrom (k := k) f g p q n where
  f' := inverseCoordinateRow (optionRestoringIso r₀ r) e none
  g' := inverseUnitSlot r₀ r e
  f_mem := hf
  g_mem := hg
  f'_mem := inverseCoordinateRow_mem (optionRestoringIso r₀ r) (optionParityProfile p q n)
    (optionRestoringIso_mem p q r₀ r hr₀ hr) (optionForwardColumns f g)
    (optionForwardColumns_mem p q f g hf hg) e he none
  g'_mem m := by
    classical
    unfold inverseUnitSlot
    split_ifs with hm
    · exact inverseCoordinateRow_mem (optionRestoringIso r₀ r) (optionParityProfile p q n)
        (optionRestoringIso_mem p q r₀ r hr₀ hr) (optionForwardColumns f g)
        (optionForwardColumns_mem p q f g hf hg) e he (some ⟨m, hm⟩)
    · exact Submodule.zero_mem _
  total := by
    have ht := sum_inverseCoordinateRow_forward (optionRestoringIso r₀ r) (optionParityProfile p q n)
      (optionRestoringIso_mem p q r₀ r hr₀ hr) (optionForwardColumns f g)
      (optionForwardColumns_mem p q f g hf hg) e he
    rw [Fintype.sum_option] at ht
    have hs : (∑ m ∈ Finset.range n, inverseUnitSlot r₀ r e m ≫ g m) =
        ∑ a : Fin n, inverseCoordinateRow (optionRestoringIso r₀ r) e (some a) ≫ g a.val := by
      classical
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro m hm
      simp only [inverseUnitSlot, Finset.mem_range.mp hm, dite_eq_left]
    simpa only [hs, optionForwardColumns] using ht
  ff := forward_inverseCoordinateRow (optionRestoringIso r₀ r) (optionParityProfile p q n)
    (optionRestoringIso_mem p q r₀ r hr₀ hr) (optionForwardColumns f g)
    (optionForwardColumns_mem p q f g hf hg) e he none
  fg m hm := by
    classical
    simp only [inverseUnitSlot, hm, dite_eq_left]
    exact forward_inverseCoordinateRow_ne (optionRestoringIso r₀ r) (optionParityProfile p q n)
      (optionRestoringIso_mem p q r₀ r hr₀ hr) (optionForwardColumns f g)
      (optionForwardColumns_mem p q f g hf hg) e he none (some ⟨m, hm⟩) (by simp)
  gf m hm := by
    exact forward_inverseCoordinateRow_ne (optionRestoringIso r₀ r) (optionParityProfile p q n)
      (optionRestoringIso_mem p q r₀ r hr₀ hr) (optionForwardColumns f g)
      (optionForwardColumns_mem p q f g hf hg) e he (some ⟨m, hm⟩) none (by simp)
  gg m l hm hl := by
    classical
    simp only [inverseUnitSlot, hl, dite_eq_left]
    by_cases hml : m = l
    · subst l
      rw [ite_eq_left rfl]
      exact forward_inverseCoordinateRow (optionRestoringIso r₀ r)
        (optionParityProfile p q n) (optionRestoringIso_mem p q r₀ r hr₀ hr)
        (optionForwardColumns f g) (optionForwardColumns_mem p q f g hf hg) e he (some ⟨m, hm⟩)
    · rw [ite_eq_right hml]
      exact forward_inverseCoordinateRow_ne (optionRestoringIso r₀ r) (optionParityProfile p q n)
        (optionRestoringIso_mem p q r₀ r hr₀ hr) (optionForwardColumns f g)
        (optionForwardColumns_mem p q f g hf hg) e he (some ⟨m, hm⟩) (some ⟨l, hl⟩) (by
          intro h
          exact hml (congrArg Fin.val (Option.some.inj h)))

end Columns

section Rows

def optionForwardRows (f : A ⟶ B) (g : ℕ → (A ⟶ Z)) :
    ∀ a, A ⟶ optionTargetFamily B Z n a
  | none => f
  | some a => g a.val

variable (p : ZMod 2) (q : ℕ → ZMod 2)
  (r₀ : V none ≅ B) (r : ∀ a : Fin n, V (some a) ≅ Z)
  (hr₀ : r₀.hom ∈ parity (R := k) _ _ p)
  (hr : ∀ a, (r a).hom ∈ parity (R := k) _ _ (q a.val))
  (f : A ⟶ B) (g : ℕ → (A ⟶ Z))
  (hf : f ∈ parity (R := k) _ _ p) (hg : ∀ m, g m ∈ parity (R := k) _ _ (q m))

include hf hg in
private theorem optionForwardRows_mem (a : Option (Fin n)) :
    optionForwardRows f g a ∈ parity (R := k) _ _ (optionParityProfile p q n a) := by
  cases a with
  | none => exact hf
  | some a => exact hg a.val

variable (e : A ≅ product V)
  (he : e.hom = restoredRows (optionRestoringIso r₀ r) (optionParityProfile p q n)
    (optionRestoringIso_mem p q r₀ r hr₀ hr) (optionForwardRows f g)
    (optionForwardRows_mem p q f g hf hg))

/-- The inverse column for a cap slot, extended by zero beyond the prescribed finite window. -/
def inverseCapSlot (m : ℕ) : Z ⟶ A := by
  classical
  exact if hm : m < n then inverseCoordinateColumn (optionRestoringIso r₀ r) e (some ⟨m, hm⟩) else 0

/-- A given even row matrix yields all specified local inverse entries and identities. -/
def localInverseToRows : SKM.SuperSumInvTo (k := k) f g p q n where
  f' := inverseCoordinateColumn (optionRestoringIso r₀ r) e none
  g' := inverseCapSlot r₀ r e
  f_mem := hf
  g_mem := hg
  f'_mem := inverseCoordinateColumn_mem (optionRestoringIso r₀ r) (optionParityProfile p q n)
    (optionRestoringIso_mem p q r₀ r hr₀ hr) (optionForwardRows f g)
    (optionForwardRows_mem p q f g hf hg) e he none
  g'_mem m := by
    classical
    unfold inverseCapSlot
    split_ifs with hm
    · exact inverseCoordinateColumn_mem (optionRestoringIso r₀ r) (optionParityProfile p q n)
        (optionRestoringIso_mem p q r₀ r hr₀ hr) (optionForwardRows f g)
        (optionForwardRows_mem p q f g hf hg) e he (some ⟨m, hm⟩)
    · exact Submodule.zero_mem _
  total := by
    have ht := sum_forward_inverseCoordinateColumn (optionRestoringIso r₀ r) (optionParityProfile p q n)
      (optionRestoringIso_mem p q r₀ r hr₀ hr) (optionForwardRows f g)
      (optionForwardRows_mem p q f g hf hg) e he
    rw [Fintype.sum_option] at ht
    have hs : (∑ m ∈ Finset.range n, g m ≫ inverseCapSlot r₀ r e m) =
        ∑ a : Fin n, g a.val ≫ inverseCoordinateColumn (optionRestoringIso r₀ r) e (some a) := by
      classical
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro m hm
      simp only [inverseCapSlot, Finset.mem_range.mp hm, dite_eq_left]
    simpa only [hs, optionForwardRows] using ht
  ff := inverseCoordinateColumn_forward (optionRestoringIso r₀ r) (optionParityProfile p q n)
    (optionRestoringIso_mem p q r₀ r hr₀ hr) (optionForwardRows f g)
    (optionForwardRows_mem p q f g hf hg) e he none
  fg m hm := by
    exact inverseCoordinateColumn_forward_ne (optionRestoringIso r₀ r) (optionParityProfile p q n)
      (optionRestoringIso_mem p q r₀ r hr₀ hr) (optionForwardRows f g)
      (optionForwardRows_mem p q f g hf hg) e he none (some ⟨m, hm⟩) (by simp)
  gf m hm := by
    classical
    simp only [inverseCapSlot, hm, dite_eq_left]
    exact inverseCoordinateColumn_forward_ne (optionRestoringIso r₀ r) (optionParityProfile p q n)
      (optionRestoringIso_mem p q r₀ r hr₀ hr) (optionForwardRows f g)
      (optionForwardRows_mem p q f g hf hg) e he (some ⟨m, hm⟩) none (by simp)
  gg m l hm hl := by
    classical
    simp only [inverseCapSlot, hm, dite_eq_left]
    by_cases hml : m = l
    · subst l
      rw [ite_eq_left rfl]
      exact inverseCoordinateColumn_forward (optionRestoringIso r₀ r)
        (optionParityProfile p q n) (optionRestoringIso_mem p q r₀ r hr₀ hr)
        (optionForwardRows f g) (optionForwardRows_mem p q f g hf hg) e he (some ⟨m, hm⟩)
    · rw [ite_eq_right hml]
      exact inverseCoordinateColumn_forward_ne (optionRestoringIso r₀ r) (optionParityProfile p q n)
        (optionRestoringIso_mem p q r₀ r hr₀ hr) (optionForwardRows f g)
        (optionForwardRows_mem p q f g hf hg) e he (some ⟨m, hm⟩) (some ⟨l, hl⟩) (by
          intro h
          exact hml (congrArg Fin.val (Option.some.inj h)))

end Rows

end OddMath.FiniteSupermodule
