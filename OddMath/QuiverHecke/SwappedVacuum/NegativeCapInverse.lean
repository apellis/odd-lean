import OddMath.QuiverHecke.SwappedVacuum.NegativeCapMoments
import OddMath.QuiverHecke.SwappedAssembly.CentralInverse.CapWindows

/-! # The prescribed negative-height inverse cap

SwappedVacuumNonpositiveBubbles §3, equations (9)–(11): the polynomial
coefficient-extraction cap is the last row of the given augmented inverse.
This identifies the inverse row by its forward tests; it does not construct
the swapped action or assume its bubble values.
-/
noncomputable section
namespace OddMath.QuiverHecke.SwappedVacuum
open CategoryTheory Finset SwappedAssembly
universe u v w
variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The forward columns of a cup-window inverse detect every outgoing map. -/
theorem cup_inverse_hom_ext {X Y O Z : C} {h : ℕ}
    {s : X ⟶ Y} {u : Fin h → (O ⟶ Y)} {j : Y ⟶ X} {B : Fin h → (Y ⟶ O)}
    (H : ProbeWindow.IsCupInverse s u j B) {f g : Y ⟶ Z}
    (hs : s ≫ f = s ≫ g) (hu : ∀ n, u n ≫ f = u n ≫ g) : f = g := by
  have hd := H.2.2.2.2
  calc
    f = (j ≫ s + ∑ n, B n ≫ u n) ≫ f := by rw [hd, Category.id_comp]
    _ = (j ≫ s + ∑ n, B n ≫ u n) ≫ g := by
      simp only [Preadditive.add_comp, Preadditive.sum_comp, Category.assoc, hs, hu]
    _ = g := by rw [hd, Category.id_comp]

/-- A map with the row tests of a specified inverse slot equals that slot. -/
theorem cup_inverse_row_eq {X Y O : C} {h : ℕ}
    {s : X ⟶ Y} {u : Fin h → (O ⟶ Y)} {j : Y ⟶ X} {B : Fin h → (Y ⟶ O)}
    (H : ProbeWindow.IsCupInverse s u j B) (n : Fin h) (f : Y ⟶ O)
    (hs : s ≫ f = 0) (hu : ∀ m, u m ≫ f = if m = n then 𝟙 O else 0) :
    f = B n := by
  apply cup_inverse_hom_ext H
  · rw [hs, H.2.1 n]
  · intro m
    rw [hu m, H.2.2.2.1 m n]

variable {k : Type w} [CommRing k] [Linear k C] {V X Y : C}

/-- The actual last inverse row is coefficient extraction after the probe
polynomial, from the signed slide and the reservoir extraction window. -/
theorem negative_inverse_cap_eq_polynomial (q : k) (x : End X) (y : End Y)
    (s : X ⟶ Y) (u : V ⟶ Y) (v : X ⟶ V) (ell : Y ⟶ V)
    (N P : ℕ) (hPN : P < N) (c : ℕ → k) (hmonic : c P = 1)
    (hsupport : ∀ n ≤ P, c n * q ^ n = c n)
    (hslide : s ≫ y - q • (x ≫ s) = v ≫ u)
    (hwindow : ∀ a < N, u ≫ (y ^ a) ≫ ell = if a + 1 = N then 𝟙 V else 0)
    (hprobe : capPolynomial c P x = 0)
    (j : Y ⟶ X) (B : Fin (N-P) → (Y ⟶ V))
    (H : ProbeWindow.IsCupInverse s (fun n => u ≫ (y ^ n.val)) j B) :
    B ⟨N-P-1, by omega⟩ = capPolynomial c P y ≫ ell := by
  symm
  apply cup_inverse_row_eq H
  · exact negative_cap_annihilates_mate q x y s u v ell N P hPN c hsupport hslide hwindow hprobe
  · intro m
    rw [Category.assoc]
    have h := negative_cap_unit_window y u ell N P c hmonic hwindow m.val (by omega)
    have he : m.val + P + 1 = N ↔ m = (⟨N-P-1, by omega⟩ : Fin (N-P)) := by
      rw [Fin.ext_iff]
      dsimp
      omega
    simpa only [he] using h

end OddMath.QuiverHecke.SwappedVacuum
