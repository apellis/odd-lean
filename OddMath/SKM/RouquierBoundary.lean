import OddMath.SKM.RouquierData

/-!
# Homogeneous boundary coefficients

Ports `RouqBoundary.Coefficients` from
`Categorification/TwoRep/RouqBoundaryAdjunction.lean`. A finite dotted-unit
boundary has no lower edge and no artificial lower zero category. The
coefficients retain their parities, so coefficient `n-1` is an odd cap when
`(n-1)|i|` is odd. No unshifted opposite adjunction is asserted.

`ofVacuumInverse` extracts these coefficients from a factor Rouquier inverse
when its common summand vanishes. This is a consumer of factor inversion,
not a proof of separated-sector inversion or of normalized bubble formulas.
-/
noncomputable section
namespace OddMath.SKM
open CategoryTheory StringDiagrams BicategoryStruct Supercategory
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)]

namespace RouquierBoundary
variable {a b : B} {E : a ⟶ b} {F : b ⟶ a}

/-- Ordered dotted unit, before any inverse cap is chosen. -/
def cup (A : SuperAdjunction (k := k) E F) (x : E ⟶ E) (j : ℕ) :
    𝟙 a ⟶ E ≫ F := A.unit ≫ rouquierPower x j ▷ F

/-- Finite homogeneous dotted-unit decomposition at a vacuum. -/
structure Coefficients (A : SuperAdjunction (k := k) E F) (x : E ⟶ E)
    (p : ZMod 2) (n : ℕ) where
  dot_mem : x ∈ parity (R := k) _ _ p
  coeff : ℕ → (E ≫ F ⟶ 𝟙 a)
  coeff_mem : ∀ (j : ℕ), coeff j ∈ parity (R := k) _ _ (j * p)
  total : ∑ j ∈ Finset.range n, coeff j ≫ cup A x j = 𝟙 (E ≫ F)
  entry : ∀ j l, j < n → l < n → cup A x j ≫ coeff l =
    if j = l then 𝟙 (𝟙 a) else 0

namespace Coefficients

variable {A : SuperAdjunction (k := k) E F} {x : E ⟶ E} {p : ZMod 2} {n : ℕ}
  (C : Coefficients A x p n)

/-- The top coefficient cap, retaining its parity. -/
def cap : E ≫ F ⟶ 𝟙 a := if 0 < n then C.coeff (n - 1) else 0

/-- The cap has the parity prescribed by the last identity summand. -/
theorem cap_mem : C.cap ∈ parity (R := k) _ _ (((n - 1 : ℕ) : ZMod 2) * p) := by
  unfold cap
  split_ifs
  · exact C.coeff_mem _
  · exact Submodule.zero_mem _

/-- The finite boundary pairs the last dotted unit with one and all others with zero. -/
theorem cup_cap (hn : 0 < n) {j : ℕ} (hj : j < n) :
    cup A x j ≫ C.cap = if j = n - 1 then 𝟙 (𝟙 a) else 0 := by
  rw [cap, ite_eq_left hn]
  exact C.entry j (n - 1) hj (by omega)

include C in
/-- Dotted units jointly detect maps out of the boundary composite. -/
theorem hom_ext {T : a ⟶ a} (f g : E ≫ F ⟶ T)
    (he : ∀ j, j < n → cup A x j ≫ f = cup A x j ≫ g) : f = g := by
  calc
    f = (∑ j ∈ Finset.range n, C.coeff j ≫ cup A x j) ≫ f := by
      rw [C.total, Category.id_comp]
    _ = (∑ j ∈ Finset.range n, C.coeff j ≫ cup A x j) ≫ g := by
      simp only [Preadditive.sum_comp, Category.assoc]
      apply Finset.sum_congr rfl
      intro j hj
      rw [he j (Finset.mem_range.mp hj)]
    _ = g := by rw [C.total, Category.id_comp]

/-- Extraction at a negative-height vacuum. The only extra hypothesis is that
its common `EF` summand vanishes; all inverse coefficients are inherited. -/
def ofVacuumInverse {a₀ : B} {E₀ : a₀ ⟶ a} {F₀ : a ⟶ a₀}
    {A₀ : SuperAdjunction (k := k) E₀ F₀} {x₀ : E₀ ⟶ E₀}
    {t : E₀ ≫ E ⟶ E₀ ≫ E} {h : ℤ}
    (L : SuperRouquierLoc A₀ A x₀ x t p h) (hh : h ≤ 0)
    (hv : 𝟙 (F₀ ≫ E₀) = 0) : Coefficients A x p (-h).toNat where
  dot_mem := L.dot₂_mem
  coeff := (L.invNeg hh).g'
  coeff_mem := (L.invNeg hh).g'_mem
  total := by
    have hz : rouquierMate A₀ A t = 0 := by
      calc
        rouquierMate A₀ A t = 𝟙 (F₀ ≫ E₀) ≫ rouquierMate A₀ A t :=
          (Category.id_comp _).symm
        _ = 0 := by rw [hv, Limits.zero_comp]
    have ht := (L.invNeg hh).total
    have hc (f : E ≫ F ⟶ F₀ ≫ E₀) : f ≫ rouquierMate A₀ A t = 0 := by
      rw [hz, Limits.comp_zero]
    rw [hc, zero_add] at ht
    exact ht
  entry := (L.invNeg hh).gg

/-- For an even cutoff at an odd colour, the boundary cap is odd. -/
example (C : Coefficients A x 1 2) : C.cap ∈ parity (R := k) _ _ 1 := by
  simpa using C.cap_mem

end Coefficients
end RouquierBoundary
end OddMath.SKM
