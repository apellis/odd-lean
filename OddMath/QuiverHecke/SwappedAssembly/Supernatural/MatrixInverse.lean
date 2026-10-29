/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.SwappedAssembly.Supernatural.Basic

/-! # Supernaturality of inverse matrices of supernatural transformations

A matrix `A = (a x y)` of transformations between finite families of functors `F x ⟶ G y`,
with a two-sided inverse `B = (b y x)`, entrywise. If every entry `a x y` is supernatural of a
parity `ρ y` depending only on its target index, then every entry `b y x` is supernatural of
parity `ρ y` (`isSupernatural_of_inverse_target`); symmetrically for a parity `ρ x` depending
only on the source index (`isSupernatural_of_inverse_source`).

These are the forms used for the inverses of the augmented maps (1.13), (1.14) of
Brundan–Ellis, *Super Kac–Moody 2-categories*, arXiv:1701.04133v2, Definition 1.5: the
leftward crossing and the `♦`-cups and caps are the entries of such inverses.

The proof: projecting the identity `A B = 1` to parity `0` shows that the homogeneous parts
`proj (ρ y) (b y x)` also form a right inverse of `A`, hence equal `B`; naturality follows from
`Ĝ(f) B = B A Ĝ(f) B = B F(f) A B = B F(f)`, where `Ĝ(f)` is the diagonal matrix of the signed
`G y (f)`.
-/

noncomputable section

namespace OddMath.QuiverHecke.SwappedAssembly

open CategoryTheory StringDiagrams Supercategory

variable {R : Type*} [CommRing R]
  {C : Type*} [Category C] [Preadditive C] [Linear R C] [Supercategory R C]
  {D : Type*} [Category D] [Preadditive D] [Linear R D] [Supercategory R D]

section Delta

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The identity matrix of a finite family of functors, at an object. -/
def famDelta (F : α → C ⥤ D) (x x' : α) (Z : C) : (F x).obj Z ⟶ (F x').obj Z :=
  if h : x = x' then eqToHom (congrArg (fun y => (F y).obj Z) h) else 0

omit [Preadditive C] [Fintype α] in
theorem famDelta_self (F : α → C ⥤ D) (x : α) (Z : C) : famDelta F x x Z = 𝟙 _ := by
  simp [famDelta]

omit [Preadditive C] [Linear R C] [Supercategory R C] [Fintype α] in
theorem famDelta_mem (F : α → C ⥤ D) (x x' : α) (Z : C) :
    famDelta F x x' Z ∈ parity (R := R) _ _ 0 := by
  unfold famDelta
  split_ifs with h
  · subst h; exact id_mem _
  · exact zero_mem _

omit [Preadditive C] in
theorem sum_famDelta_comp (F : α → C ⥤ D) (x : α) (Z : C) {W : D}
    (g : ∀ x', (F x').obj Z ⟶ W) : ∑ x', famDelta F x x' Z ≫ g x' = g x := by
  rw [Finset.sum_eq_single x (fun x' _ h => by simp [famDelta, Ne.symm h]) (by simp),
    famDelta_self, Category.id_comp]

omit [Preadditive C] in
theorem sum_comp_famDelta (F : α → C ⥤ D) (x : α) (Z : C) {W : D}
    (g : ∀ x', W ⟶ (F x').obj Z) : ∑ x', g x' ≫ famDelta F x' x Z = g x := by
  rw [Finset.sum_eq_single x (fun x' _ h => by simp [famDelta, h]) (by simp),
    famDelta_self, Category.comp_id]

end Delta

variable {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
  {F : α → C ⥤ D} {G : β → C ⥤ D}

private theorem two_mul_zmod (p : ZMod 2) : p + p = 0 := by
  fin_cases p <;> rfl

private theorem sign_smul_naturality {p : ZMod 2} {F' G' : C ⥤ D}
    {a : ∀ Z, F'.obj Z ⟶ G'.obj Z} (ha : IsSupernatural R p a) {Z Z' : C} {q : ZMod 2}
    {f : Z ⟶ Z'} (hf : f ∈ parity (R := R) Z Z' q) :
    a Z ≫ G'.map f = sign R (p * q) • (F'.map f ≫ a Z') := by
  rw [ha.naturality hf, smul_smul, Supercategory.sign_mul_self, one_smul]

private theorem sign_smul_naturality_assoc {p : ZMod 2} {F' G' : C ⥤ D}
    {a : ∀ Z, F'.obj Z ⟶ G'.obj Z} (ha : IsSupernatural R p a) {Z Z' : C} {q : ZMod 2}
    {f : Z ⟶ Z'} (hf : f ∈ parity (R := R) Z Z' q) {W : D} (h : G'.obj Z' ⟶ W) :
    a Z ≫ G'.map f ≫ h = sign R (p * q) • (F'.map f ≫ a Z' ≫ h) := by
  rw [← Category.assoc, sign_smul_naturality ha hf, Linear.smul_comp, Category.assoc]

/-- **The inverse of a matrix of supernatural transformations whose parities depend only on
the target index** is supernatural, of the parity of its source index. -/
theorem isSupernatural_of_inverse_target (ρ : β → ZMod 2)
    (a : ∀ x y Z, (F x).obj Z ⟶ (G y).obj Z) (b : ∀ y x Z, (G y).obj Z ⟶ (F x).obj Z)
    (ha : ∀ x y, IsSupernatural R (ρ y) (a x y))
    (hab : ∀ x x' Z, ∑ y, a x y Z ≫ b y x' Z = famDelta F x x' Z)
    (hba : ∀ y y' Z, ∑ x, b y x Z ≫ a x y' Z = famDelta G y y' Z) (y : β) (x : α) :
    IsSupernatural R (ρ y) (b y x) := by
  -- The homogeneous parts of `b` are a right inverse of `a`, hence equal to `b`.
  have hab' : ∀ x x' Z, ∑ y, a x y Z ≫ proj R (ρ y) (b y x' Z) = famDelta F x x' Z := by
    intro x x' Z
    have h := congrArg (proj R 0) (hab x x' Z)
    rw [proj_of_mem (famDelta_mem F x x' Z), map_sum] at h
    rw [← h]
    refine Finset.sum_congr rfl fun y _ => ?_
    have e := proj_comp_of_mem_left (R := R) (ρ y) ((ha x y).mem Z) (b y x' Z)
    rw [two_mul_zmod] at e
    exact e.symm
  have hb : ∀ y x Z, b y x Z = proj R (ρ y) (b y x Z) := by
    intro y x Z
    calc b y x Z = ∑ x', b y x' Z ≫ famDelta F x' x Z :=
        (sum_comp_famDelta F x Z (fun x' => b y x' Z)).symm
      _ = ∑ x', ∑ y', b y x' Z ≫ a x' y' Z ≫ proj R (ρ y') (b y' x Z) := by
          simp only [← hab', Preadditive.comp_sum]
      _ = ∑ y', (∑ x', b y x' Z ≫ a x' y' Z) ≫ proj R (ρ y') (b y' x Z) := by
          rw [Finset.sum_comm]; simp only [Preadditive.sum_comp, Category.assoc]
      _ = proj R (ρ y) (b y x Z) := by
          simp only [hba]; exact sum_famDelta_comp G y Z (fun y' => proj R (ρ y') (b y' x Z))
  refine ⟨fun Z => ?_, fun {Z Z' q f} hf => ?_⟩
  · rw [hb]; exact proj_mem _ _
  · have e2 : ∀ y', famDelta G y y' Z ≫ (sign R (ρ y' * q) • ((G y').map f ≫ b y' x Z')) =
        ∑ x', b y x' Z ≫ (F x').map f ≫ a x' y' Z' ≫ b y' x Z' := by
      intro y'
      rw [← hba, Preadditive.sum_comp]
      refine Finset.sum_congr rfl fun x' _ => ?_
      simp only [Category.assoc, Linear.comp_smul, sign_smul_naturality_assoc (ha x' y') hf,
        smul_smul, Supercategory.sign_mul_self, one_smul]
    have e3 : ∀ x', ∑ y', b y x' Z ≫ (F x').map f ≫ a x' y' Z' ≫ b y' x Z' =
        (b y x' Z ≫ (F x').map f) ≫ famDelta F x' x Z' := by
      intro x'
      rw [← hab, Preadditive.comp_sum]
      simp only [Category.assoc]
    have key : sign R (ρ y * q) • ((G y).map f ≫ b y x Z') = b y x Z ≫ (F x).map f := by
      rw [← sum_famDelta_comp G y Z (fun y' => sign R (ρ y' * q) • ((G y').map f ≫ b y' x Z')),
        Finset.sum_congr rfl fun y' _ => e2 y', Finset.sum_comm,
        Finset.sum_congr rfl fun x' _ => e3 x']
      exact sum_comp_famDelta F x Z' (fun x' => b y x' Z ≫ (F x').map f)
    rw [← key, smul_smul, Supercategory.sign_mul_self, one_smul]

/-- **The inverse of a matrix of supernatural transformations whose parities depend only on
the source index** is supernatural, of the parity of its target index. -/
theorem isSupernatural_of_inverse_source (ρ : α → ZMod 2)
    (a : ∀ x y Z, (F x).obj Z ⟶ (G y).obj Z) (b : ∀ y x Z, (G y).obj Z ⟶ (F x).obj Z)
    (ha : ∀ x y, IsSupernatural R (ρ x) (a x y))
    (hab : ∀ x x' Z, ∑ y, a x y Z ≫ b y x' Z = famDelta F x x' Z)
    (hba : ∀ y y' Z, ∑ x, b y x Z ≫ a x y' Z = famDelta G y y' Z) (y : β) (x : α) :
    IsSupernatural R (ρ x) (b y x) := by
  have hba' : ∀ y y' Z, ∑ x, proj R (ρ x) (b y x Z) ≫ a x y' Z = famDelta G y y' Z := by
    intro y y' Z
    have h := congrArg (proj R 0) (hba y y' Z)
    rw [proj_of_mem (famDelta_mem G y y' Z), map_sum] at h
    rw [← h]
    refine Finset.sum_congr rfl fun x _ => ?_
    have e := proj_comp_of_mem_right (R := R) (ρ x) (b y x Z) ((ha x y').mem Z)
    rw [two_mul_zmod] at e
    exact e.symm
  have hb : ∀ y x Z, b y x Z = proj R (ρ x) (b y x Z) := by
    intro y x Z
    calc b y x Z = ∑ y', famDelta G y y' Z ≫ b y' x Z :=
        (sum_famDelta_comp G y Z (fun y' => b y' x Z)).symm
      _ = ∑ y', ∑ x', proj R (ρ x') (b y x' Z) ≫ a x' y' Z ≫ b y' x Z := by
          simp only [← hba', Preadditive.sum_comp, Category.assoc]
      _ = ∑ x', proj R (ρ x') (b y x' Z) ≫ ∑ y', a x' y' Z ≫ b y' x Z := by
          rw [Finset.sum_comm]; simp only [Preadditive.comp_sum]
      _ = proj R (ρ x) (b y x Z) := by
          simp only [hab]; exact sum_comp_famDelta F x Z (fun x' => proj R (ρ x') (b y x' Z))
  refine ⟨fun Z => ?_, fun {Z Z' q f} hf => ?_⟩
  · rw [hb]; exact proj_mem _ _
  · have e2 : ∀ y', famDelta G y y' Z ≫ (G y').map f ≫ b y' x Z' =
        ∑ x', b y x' Z ≫ (sign R (ρ x' * q) • ((F x').map f ≫ a x' y' Z' ≫ b y' x Z')) := by
      intro y'
      rw [← hba, Preadditive.sum_comp]
      refine Finset.sum_congr rfl fun x' _ => ?_
      simp only [Category.assoc, sign_smul_naturality_assoc (ha x' y') hf]
    have e3 : ∀ x', ∑ y', b y x' Z ≫ (sign R (ρ x' * q) • ((F x').map f ≫ a x' y' Z' ≫
        b y' x Z')) = (sign R (ρ x' * q) • (b y x' Z ≫ (F x').map f)) ≫ famDelta F x' x Z' := by
      intro x'
      rw [← hab, Preadditive.comp_sum]
      simp only [Category.assoc, Linear.comp_smul, Linear.smul_comp]
    rw [← sum_famDelta_comp G y Z (fun y' => (G y').map f ≫ b y' x Z'),
      Finset.sum_congr rfl fun y' _ => e2 y', Finset.sum_comm,
      Finset.sum_congr rfl fun x' _ => e3 x']
    exact sum_comp_famDelta F x Z' (fun x' => sign R (ρ x' * q) • (b y x' Z ≫ (F x').map f))

end OddMath.QuiverHecke.SwappedAssembly
