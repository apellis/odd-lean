import OddMath.SKM.RouquierHomPrincipal
import OddMath.SKM.RouquierHomReservoirPowers
import OddMath.SKM.RouquierLeftWindowInverse
import OddMath.SKM.RouquierHomPostInverse

/-!
# Precomposition augmented inverses

Preliminaries for transport of the reversed left windows through the prescribed
Hom coordinates in `SwappedHomInversion.md`, §2. The raw inverses extend to
natural-number families by zero outside the finite window, including height zero.
Homogeneous coordinate transport changes the window parity by the common
coordinate parity. Its specialization to the prescribed Hom maps, including
the alpha, beta and gamma normalizations, remains to be constructed.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
private theorem preParity_cancel (σ p : ZMod 2) : σ + (p + σ) = p := by
  fin_cases σ <;> fin_cases p <;> rfl

section Transport
variable {k : Type r} [CommRing k]
  {C C' : Type*} [Category C] [Category C']
  [Preadditive C] [Linear k C] [Supercategory k C]
  [Preadditive C'] [Linear k C'] [Supercategory k C']
  (F : C ⥤ C') [F.Additive] [F.Linear k] [IsSuperfunctor k F]
  {A B Z : C} {A' B' Z' : C'}
  (a : A' ≅ F.obj A) (b : B' ≅ F.obj B) (c : Z' ≅ F.obj Z)
  (σ : ZMod 2)
  (ha : a.hom ∈ parity (R := k) _ _ σ)
  (hb : b.hom ∈ parity (R := k) _ _ σ)
  (hc : c.hom ∈ parity (R := k) _ _ 0)
  {p : ZMod 2} {q : ℕ → ZMod 2} {n : ℕ}

/-- Transport all rows and columns, preserving the finite-window equations. -/
def SuperSumInvTo.mapHomogeneousCoordinates {f : A ⟶ B} {g : ℕ → (A ⟶ Z)}
    (J : SuperSumInvTo (k := k) f g p q n) :
    SuperSumInvTo (k := k) (a.hom ≫ F.map f ≫ b.inv)
      (fun m => a.hom ≫ F.map (g m) ≫ c.inv) p (fun m => σ + q m) n where
  f' := b.hom ≫ F.map J.f' ≫ a.inv
  g' m := c.hom ≫ F.map (J.g' m) ≫ a.inv
  f_mem := by
    have hh := comp_mem ha (comp_mem (map_mem F J.f_mem) (inv_mem b hb))
    simpa only [preParity_cancel] using hh
  g_mem m := by simpa [add_assoc, add_comm, add_left_comm] using comp_mem ha (comp_mem (map_mem F (J.g_mem m)) (inv_mem c hc))
  f'_mem := by
    have hh := comp_mem hb (comp_mem (map_mem F J.f'_mem) (inv_mem a ha))
    simpa only [preParity_cancel] using hh
  g'_mem m := by simpa [add_assoc, add_comm, add_left_comm] using comp_mem hc (comp_mem (map_mem F (J.g'_mem m)) (inv_mem a ha))
  total := by
    have ht := congrArg (fun t => a.hom ≫ F.map t ≫ a.inv) J.total
    simpa [Functor.map_add, Functor.map_sum, Functor.map_comp, Preadditive.comp_add,
      Preadditive.add_comp, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc] using ht
  ff := by simp [Category.assoc, ← F.map_comp_assoc, J.ff]
  fg m hm := by simp [Category.assoc, ← F.map_comp_assoc, J.fg m hm]
  gf m hm := by simp [Category.assoc, ← F.map_comp_assoc, J.gf m hm]
  gg m l hm hl := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← F.map_comp_assoc]
    rw [J.gg m l hm hl]
    split_ifs <;> simp

/-- Transport the column presentation, including every inverse row. -/
def SuperSumInvFrom.mapHomogeneousCoordinates {f : B ⟶ A} {g : ℕ → (Z ⟶ A)}
    (J : SuperSumInvFrom (k := k) f g p q n) :
    SuperSumInvFrom (k := k) (b.hom ≫ F.map f ≫ a.inv)
      (fun m => c.hom ≫ F.map (g m) ≫ a.inv) p (fun m => σ + q m) n where
  f' := a.hom ≫ F.map J.f' ≫ b.inv
  g' m := a.hom ≫ F.map (J.g' m) ≫ c.inv
  f_mem := by simpa only [preParity_cancel] using comp_mem hb (comp_mem (map_mem F J.f_mem) (inv_mem a ha))
  g_mem m := by simpa [add_assoc, add_comm, add_left_comm] using comp_mem hc (comp_mem (map_mem F (J.g_mem m)) (inv_mem a ha))
  f'_mem := by simpa only [preParity_cancel] using comp_mem ha (comp_mem (map_mem F J.f'_mem) (inv_mem b hb))
  g'_mem m := by simpa [add_assoc, add_comm, add_left_comm] using comp_mem ha (comp_mem (map_mem F (J.g'_mem m)) (inv_mem c hc))
  total := by
    have ht := congrArg (fun t => a.hom ≫ F.map t ≫ a.inv) J.total
    simpa [Functor.map_add, Functor.map_sum, Functor.map_comp, Preadditive.comp_add,
      Preadditive.add_comp, Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc] using ht
  ff := by simp [Category.assoc, ← F.map_comp_assoc, J.ff]
  fg m hm := by simp [Category.assoc, ← F.map_comp_assoc, J.fg m hm]
  gf m hm := by simp [Category.assoc, ← F.map_comp_assoc, J.gf m hm]
  gg m l hm hl := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc, ← F.map_comp_assoc]
    rw [J.gg m l hm hl]
    split_ifs <;> simp
end Transport



variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)] [TwoSupercategory k B]
namespace SuperRouquierLoc
variable {a b c : B} {E₁ : a ⟶ b} {F₁ : b ⟶ a} {E₂ : b ⟶ c} {F₂ : c ⟶ b}
  {A₁ : SuperAdjunction (k := k) E₁ F₁} {A₂ : SuperAdjunction (k := k) E₂ F₂}
  {x₁ : E₁ ⟶ E₁} {x₂ : E₂ ⟶ E₂} {t : E₁ ≫ E₂ ⟶ E₁ ≫ E₂} {p : ZMod 2} {h : ℤ}
  (L : SuperRouquierLoc A₁ A₂ x₁ x₂ t p h)

/-- The inverse row is zero outside the finite cup window. -/
def leftWindowCupRowNat (n : ℕ) : F₁ ≫ E₁ ⟶ 𝟙 b :=
  if hn : n < h.toNat then L.leftWindowCupRow ⟨n, hn⟩ else 0

/-- The inverse column is zero outside the finite cap window. -/
def leftWindowCapColumnNat (n : ℕ) : 𝟙 b ⟶ E₂ ≫ F₂ :=
  if hn : n < (-h).toNat then L.leftWindowCapColumn ⟨n, hn⟩ else 0

/-- The raw left cup inverse, with all natural-number entries and the empty boundary. -/
def leftWindowInvFrom (hh : 0 ≤ h) :
    SuperSumInvFrom (k := k) (-L.sigL) L.leftWindowCup p
      (fun n => p * ((h : ZMod 2) + 1) + n * p) h.toNat where
  f' := L.sig
  g' := L.leftWindowCupRowNat
  f_mem := Submodule.neg_mem _ L.sigL_mem
  g_mem := L.leftWindowCup_mem
  f'_mem := L.sig_mem
  g'_mem n := by
    unfold leftWindowCupRowNat
    split_ifs with hn
    · exact L.leftWindowCupRow_mem (by omega) ⟨n, hn⟩
    · exact Submodule.zero_mem _
  total := by
    by_cases hz : h = 0
    · simpa [hz] using (L.leftWindow_zero_inverse hz).1
    · have ht := L.leftWindowCup_total (by omega)
      rw [← Fin.sum_univ_eq_sum_range]
      simpa only [leftWindowCupRowNat, dite_eq_left (Fin.isLt _)] using ht
  ff := by rw [Preadditive.neg_comp, L.sigL_sig_of_nonneg hh, neg_neg]
  fg n hn := by
    rw [leftWindowCupRowNat, dite_eq_left hn]
    exact L.sigL_leftWindowCupRow (by omega) ⟨n, hn⟩
  gf n hn := L.leftWindowCup_sig (by omega) hn
  gg n m hn hm := by
    rw [leftWindowCupRowNat, dite_eq_left hm]
    simpa only [Fin.mk.injEq] using L.leftWindowCup_row (by omega) ⟨n, hn⟩ ⟨m, hm⟩

/-- The raw left cap inverse, with all natural-number entries and the empty boundary. -/
def leftWindowInvTo (hh : h ≤ 0) :
    SuperSumInvTo (k := k) (-L.sigL) L.leftWindowCap p
      (fun n => p * ((h : ZMod 2) + 1) + n * p) (-h).toNat where
  f' := L.sig
  g' := L.leftWindowCapColumnNat
  f_mem := Submodule.neg_mem _ L.sigL_mem
  g_mem := L.leftWindowCap_mem
  f'_mem := L.sig_mem
  g'_mem n := by
    unfold leftWindowCapColumnNat
    split_ifs with hn
    · exact L.leftWindowCapColumn_mem (by omega) ⟨n, hn⟩
    · exact Submodule.zero_mem _
  total := by
    by_cases hz : h = 0
    · simpa [hz] using (L.leftWindow_zero_inverse hz).2
    · have ht := L.leftWindowCap_total (by omega)
      rw [← Fin.sum_univ_eq_sum_range]
      simpa only [leftWindowCapColumnNat, dite_eq_left (Fin.isLt _)] using ht
  ff := by rw [Preadditive.comp_neg, L.sig_sigL_of_nonpos hh, neg_neg]
  fg n hn := L.sig_leftWindowCap (by omega) hn
  gf n hn := by
    rw [leftWindowCapColumnNat, dite_eq_left hn]
    exact L.leftWindowCapColumn_sigL (by omega) ⟨n, hn⟩
  gg n m hn hm := by
    rw [leftWindowCapColumnNat, dite_eq_left hn]
    simpa only [Fin.mk.injEq] using L.leftWindowCap_column (by omega) ⟨n, hn⟩ ⟨m, hm⟩
end SuperRouquierLoc

end OddMath.SKM