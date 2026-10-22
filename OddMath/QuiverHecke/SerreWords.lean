/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.MixedRelations

/-!
# The words `i^a j i^{M-a}` of the categorical Serre relation

Input to Brundan–Ellis, arXiv:1701.04133v2, Proposition 11.2 (Hill–Wang, arXiv:1202.2769v2,
Theorem 5.9). For colours `i`, `j` and `M ≥ 0`, `serreWord i j M a = i^a j i^{M-a}` (positions
counted from the left). On it the dots and crossings of the left block `[0, a)` and of the right
block `[a + 1, M + 1)` are signed nilHecke families (`leftFamily`, `rightFamily`), and
`serreIdem a = 1_{i^{(a)}} ⊗ 1_j ⊗ 1_{i^{(M-a)}}` is the product of their longest Demazure
products. The crossing `crossHom` of the strand `j` with a neighbouring `i` moves between
consecutive words.

Generators away from that crossing pass through it by the super interchange law; `Slides`
records this for elements of the endomorphism rings, with an explicit sign, and is closed under
products, so the block idempotents pass through it unchanged.
-/

noncomputable section
open scoped Classical
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams
open SKM (zsign)
open Categorification.KLR.KL2.NH (wp Wb chL chR)
open Categorification.NilHecke (w0Word)
universe u v w

/-! ## Intertwiners -/

section Slides

variable {C : Type*} [Category C] [Preadditive C] {A B : C}

/-- `f ≫ σ = u • (σ ≫ g)`: `f` passes through `σ` as `g`, with the sign `u`. -/
def Slides (σ : A ⟶ B) (u : ℤˣ) (f : End A) (g : End B) : Prop := f ≫ σ = (u : ℤ) • (σ ≫ g)

namespace Slides

variable {σ : A ⟶ B} {u u' : ℤˣ} {f f' : End A} {g g' : End B}

theorem one : Slides σ 1 (1 : End A) (1 : End B) := by
  simp [Slides, End.one_def]

theorem mul (h : Slides σ u f g) (h' : Slides σ u' f' g') : Slides σ (u * u') (f * f') (g * g') := by
  simp only [Slides, End.mul_def, Category.assoc] at *
  rw [h, Preadditive.comp_zsmul, ← Category.assoc, h', Preadditive.zsmul_comp, Category.assoc,
    smul_smul, Units.val_mul]

theorem zsmul (h : Slides σ u f g) (c : ℤ) : Slides σ u (c • f) (c • g) := by
  simp only [Slides] at *
  rw [Preadditive.zsmul_comp, h, Preadditive.comp_zsmul, smul_comm]

theorem neg (h : Slides σ u f g) : Slides σ u (-f) (-g) := by
  simpa using h.zsmul (-1)

theorem add (h : Slides σ u f g) (h' : Slides σ u f' g') : Slides σ u (f + f') (g + g') := by
  simp only [Slides] at *
  rw [Preadditive.add_comp, h, h', Preadditive.comp_add, smul_add]

theorem wp {DA : ℕ → End A} {DB : ℕ → End B} {ρ : List ℕ}
    (h : ∀ j ∈ ρ, Slides σ 1 (DA j) (DB j)) : Slides σ 1 (wp DA ρ) (wp DB ρ) := by
  induction ρ with
  | nil => exact one
  | cons a ρ ih =>
    rw [Categorification.KLR.KL2.NH.wp_cons, Categorification.KLR.KL2.NH.wp_cons]
    simpa using (h a (by simp)).mul (ih fun j hj => h j (by simp [hj]))

theorem wp' {DA : ℕ → End A} {DB : ℕ → End B} {ρ : List ℕ}
    (h : ∀ j ∈ ρ, Slides σ u (DA j) (DB j)) :
    Slides σ (u ^ ρ.length) (Categorification.KLR.KL2.NH.wp DA ρ)
      (Categorification.KLR.KL2.NH.wp DB ρ) := by
  induction ρ with
  | nil => simpa using (one : Slides σ 1 (1 : End A) (1 : End B))
  | cons a ρ ih =>
    rw [Categorification.KLR.KL2.NH.wp_cons, Categorification.KLR.KL2.NH.wp_cons,
      List.length_cons, pow_succ']
    exact (h a (by simp)).mul (ih fun j hj => h j (by simp [hj]))

theorem pow (h : Slides σ u f g) (n : ℕ) : Slides σ (u ^ n) (f ^ n) (g ^ n) := by
  induction n with
  | zero => simpa using (one : Slides σ 1 (1 : End A) (1 : End B))
  | succ n ih => rw [pow_succ', pow_succ', pow_succ']; exact h.mul ih

theorem comp {C' : C} {σ' : B ⟶ C'} {h₀ : End C'} {g : End B} (h : Slides σ u f g)
    (h' : Slides σ' u' g h₀) : Slides (σ ≫ σ') (u * u') f h₀ := by
  simp only [Slides] at *
  rw [← Category.assoc, h, Preadditive.zsmul_comp, Category.assoc, h', Preadditive.comp_zsmul,
    smul_smul, Units.val_mul, Category.assoc]

theorem smul_left {R : Type*} [Semiring R] [Linear R C] (h : Slides σ u f g) (c : R) :
    Slides (c • σ) u f g := by
  simp only [Slides] at *
  rw [Linear.comp_smul, h, Linear.smul_comp, smul_comm]

/-- Commuting with a product of endomorphisms. -/
theorem endMul {σ σ' : End A} {f : End A} (h : Slides σ u f f) (h' : Slides σ' u' f f) :
    Slides (σ * σ') (u * u') f f := by
  rw [End.mul_def, mul_comm u u']; exact h'.comp h

theorem wpσ {D' : ℕ → End A} {f : End A} {ρ : List ℕ} (h : ∀ j ∈ ρ, Slides (D' j) u f f) :
    Slides (Categorification.KLR.KL2.NH.wp D' ρ : End A) (u ^ ρ.length) f f := by
  induction ρ with
  | nil => simp [Slides, End.one_def]
  | cons a ρ ih =>
    rw [Categorification.KLR.KL2.NH.wp_cons, List.length_cons, pow_succ']
    exact (h a (by simp)).endMul (ih fun j hj => h j (by simp [hj]))

theorem powσ {σ f : End A} (h : Slides σ u f f) (n : ℕ) : Slides (σ ^ n) (u ^ n) f f := by
  induction n with
  | zero => simp [Slides, End.one_def]
  | succ n ih => rw [pow_succ', pow_succ']; exact h.endMul ih

theorem wb {DA : ℕ → End A} {DB : ℕ → End B} {s n : ℕ}
    (h : ∀ j, s ≤ j → j + 1 < s + n → Slides σ 1 (DA j) (DB j)) :
    Slides σ 1 (Wb DA s n) (Wb DB s n) :=
  wp fun j hj => by
    obtain ⟨h₁, h₂⟩ := Categorification.KLR.KL2.NH.mem_w0Word_map hj
    exact h j h₁ h₂

end Slides

end Slides

variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X) {k : Type w}
  [CommRing k] (Sc : SKM.Scalars D k)

theorem zsign_smul_hom {a b : H D Sc} (p : ZMod 2) (f : a ⟶ b) :
    zsign k p • f = ((zunit p : ℤ)) • f := by
  have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hz p with h | h <;> simp [zsign, zunit, h]

/-- The crossing at positions `q`, `q + 1` as a morphism from `w` to `w'`, when it goes from `w`
to `w'`, and `0` otherwise. -/
def crossHom (w w' : List I) (q : ℕ) : (pres D Sc).obj (ob D w) ⟶ (pres D Sc).obj (ob D w') :=
  if h : SChain w (pl w [.cross q]) w' then cl D Sc w w' [.cross q] h else 0

theorem crossHom_eq {w w' : List I} {q : ℕ} (h : SChain w (pl w [.cross q]) w') :
    crossHom D Sc w w' q = cl D Sc w w' [.cross q] h :=
  dite_eq_left h

theorem zunit_mul_self (p : ZMod 2) : zunit p * zunit p = 1 := Int.units_mul_self _

theorem replicate_split (i : I) {n : ℕ} (a b : ℕ) (h : a + b = n) :
    List.replicate n i = List.replicate a i ++ List.replicate b i := by
  subst h; exact List.replicate_add a b i

/-! ## Transport through a crossing -/

section Transport

variable (i : I) {x y : I} {a c : ℕ}

/-- The crossing of the strands `a`, `a + 1` of `i^a x y V`. -/
abbrev crossAt (x y : I) (a : ℕ) (V : List I) :=
  crossHom D Sc (List.replicate a i ++ [x, y] ++ V) (List.replicate a i ++ [y, x] ++ V) a

theorem sChain_crossAt (x y : I) (a : ℕ) (V : List I) :
    SChain (List.replicate a i ++ [x, y] ++ V)
      (pl (List.replicate a i ++ [x, y] ++ V) [.cross a]) (List.replicate a i ++ [y, x] ++ V) :=
  sChain_ofShape' (List.replicate a i) V (.cross x y) rfl rfl (by simp)

/-- A dot left of the crossing passes through it. -/
theorem slides_dot_left {p : ℕ} (hp : p < a) :
    Slides (crossAt D Sc i x y a (List.replicate c i)) (zunit (D.parity i * (D.parity x * D.parity y)))
      (dotE D Sc _ p) (dotE D Sc _ p) := by
  have e : List.replicate a i = List.replicate p i ++ [i] ++ List.replicate (a - p - 1) i := by
    rw [replicate_split i p (a - p) (by omega), replicate_split i (n := a - p) 1 (a - p - 1)
      (by omega)]
    simp
  simp only [Slides, crossAt]
  rw [crossHom_eq D Sc (sChain_crossAt i x y a _), ← zsign_smul_hom]
  exact genE_comp_cl D Sc (List.replicate p i) (List.replicate (a - p - 1) i) (List.replicate c i) (.dot i)
    (.cross x y) rfl (by rw [e]; simp [Shape.dom]) (by rw [e]; simp [Shape.dom, Shape.cod])
    (by simp) (by simp [Shape.dom]; omega) _

/-- A crossing left of the crossing passes through it. -/
theorem slides_cross_left {p : ℕ} (hp : p + 1 < a) :
    Slides (crossAt D Sc i x y a (List.replicate c i))
      (zunit (D.parity i * (D.parity x * D.parity y))) (crossE D Sc _ p) (crossE D Sc _ p) := by
  have e : List.replicate a i = List.replicate p i ++ [i, i] ++ List.replicate (a - p - 2) i := by
    rw [replicate_split i p (a - p) (by omega), replicate_split i (n := a - p) 2 (a - p - 2)
      (by omega)]
    simp
  simp only [Slides, crossAt]
  rw [crossHom_eq D Sc (sChain_crossAt i x y a _), ← zsign_smul_hom]
  have h := genE_comp_cl D Sc (k := k) (p := p) (q := a) (List.replicate p i) (List.replicate (a - p - 2) i)
    (List.replicate c i)
    (.cross i i) (.cross x y) rfl (by rw [e]; simp [Shape.dom])
    (by rw [e]; simp [Shape.dom, Shape.cod]) (by simp) (by simp [Shape.dom]; omega)
    (sChain_crossAt i x y a (List.replicate c i))
  simpa only [Shape.parity, parity_sq, PG.ofShape] using h

/-- A dot right of the crossing passes through it. -/
theorem slides_dot_right {p : ℕ} (hp : a + 2 ≤ p) (hp' : p < a + 2 + c) :
    Slides (crossAt D Sc i x y a (List.replicate c i))
      (zunit (D.parity i * (D.parity x * D.parity y))) (dotE D Sc _ p) (dotE D Sc _ p) := by
  have e : List.replicate c i =
      List.replicate (p - a - 2) i ++ [i] ++ List.replicate (a + 1 + c - p) i := by
    rw [replicate_split i (p - a - 2) (c - (p - a - 2)) (by omega),
      replicate_split i (n := c - (p - a - 2)) 1 (a + 1 + c - p) (by omega)]
    simp
  simp only [Slides, crossAt]
  rw [crossHom_eq D Sc (sChain_crossAt i x y a _), ← zsign_smul_hom]
  have h := genE_comp_cl' D Sc (k := k) (p := p) (q := a) (List.replicate a i) (List.replicate (p - a - 2) i)
    (List.replicate (a + 1 + c - p) i) (.cross x y) (.dot i) rfl
    (by rw [e]; simp [Shape.dom]) (by rw [e]; simp [Shape.dom, Shape.cod]) (by simp)
    (by simp [Shape.dom]; omega) (by simp [Shape.cod]; omega)
    (sChain_crossAt i x y a (List.replicate c i))
  simpa only [Shape.parity, PG.ofShape, mul_comm (D.parity x * D.parity y)] using h

/-- A crossing right of the crossing passes through it. -/
theorem slides_cross_right {p : ℕ} (hp : a + 2 ≤ p) (hp' : p + 1 < a + 2 + c) :
    Slides (crossAt D Sc i x y a (List.replicate c i))
      (zunit (D.parity i * (D.parity x * D.parity y))) (crossE D Sc _ p) (crossE D Sc _ p) := by
  have e : List.replicate c i =
      List.replicate (p - a - 2) i ++ [i, i] ++ List.replicate (a + c - p) i := by
    rw [replicate_split i (p - a - 2) (c - (p - a - 2)) (by omega),
      replicate_split i (n := c - (p - a - 2)) 2 (a + c - p) (by omega)]
    simp
  simp only [Slides, crossAt]
  rw [crossHom_eq D Sc (sChain_crossAt i x y a _), ← zsign_smul_hom]
  have h := genE_comp_cl' D Sc (k := k) (p := p) (q := a) (List.replicate a i) (List.replicate (p - a - 2) i)
    (List.replicate (a + c - p) i) (.cross x y) (.cross i i) rfl
    (by rw [e]; simp [Shape.dom]) (by rw [e]; simp [Shape.dom, Shape.cod]) (by simp)
    (by simp [Shape.dom]; omega) (by simp [Shape.cod]; omega)
    (sChain_crossAt i x y a (List.replicate c i))
  simpa only [Shape.parity, parity_sq, PG.ofShape, mul_comm (D.parity x * D.parity y)] using h

open SignedNilHecke in
/-- A Demazure element of a block, at positions away from the crossing, passes through it. -/
theorem slides_dem {ε : ℤˣ} {s n s' n' q : ℕ} (hA₁ : s ≤ q) (hA₂ : q + 1 < s + n) (hB₁ : s' ≤ q)
    (hB₂ : q + 1 < s' + n') (hq : q + 2 ≤ a ∨ (a + 2 ≤ q ∧ q + 2 ≤ a + 2 + c)) :
    Slides (crossAt D Sc i x y a (List.replicate c i)) 1
      (dem ε s n (dotE D Sc _) (crossE D Sc _) q) (dem ε s' n' (dotE D Sc _) (crossE D Sc _) q) := by
  rw [dem_of hA₁ hA₂, dem_of hB₁ hB₂]
  refine Slides.neg (Slides.zsmul ?_ _)
  rw [← zunit_mul_self (D.parity i * (D.parity x * D.parity y))]
  rcases hq with hq | ⟨hq₁, hq₂⟩
  · exact (slides_cross_left D Sc i (by omega)).mul (slides_dot_left D Sc i (by omega))
  · exact (slides_cross_right D Sc i hq₁ (by omega)).mul
      (slides_dot_right D Sc i (by omega) (by omega))

open SignedNilHecke in
/-- A block idempotent left of the crossing passes through it. -/
theorem slides_idem_left {ε : ℤˣ} {s n s' n' t m : ℕ} (hA₁ : s ≤ t) (hA₂ : t + m ≤ s + n)
    (hB₁ : s' ≤ t) (hB₂ : t + m ≤ s' + n') (h : t + m ≤ a) :
    Slides (crossAt D Sc i x y a (List.replicate c i)) 1
      (idem ε s n (dotE D Sc _) (crossE D Sc _) t m)
      (idem ε s' n' (dotE D Sc _) (crossE D Sc _) t m) :=
  Slides.wb fun q h₁ h₂ => slides_dem D Sc i (by omega) (by omega) (by omega) (by omega) (by omega)

open SignedNilHecke in
/-- A block idempotent right of the crossing passes through it. -/
theorem slides_idem_right {ε : ℤˣ} {s n s' n' t m : ℕ} (hA₁ : s ≤ t) (hA₂ : t + m ≤ s + n)
    (hB₁ : s' ≤ t) (hB₂ : t + m ≤ s' + n') (h₁ : a + 2 ≤ t) (h₂ : t + m ≤ a + 2 + c) :
    Slides (crossAt D Sc i x y a (List.replicate c i)) 1
      (idem ε s n (dotE D Sc _) (crossE D Sc _) t m)
      (idem ε s' n' (dotE D Sc _) (crossE D Sc _) t m) :=
  Slides.wb fun q h₁' h₂' => slides_dem D Sc i (by omega) (by omega) (by omega) (by omega)
    (Or.inr ⟨by omega, by omega⟩)

end Transport

end OddMath.QuiverHecke
