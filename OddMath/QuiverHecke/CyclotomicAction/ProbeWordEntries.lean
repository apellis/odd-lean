import OddMath.QuiverHecke.CyclotomicAction.ProbeWordCorner

/-! # Rectangular cyclotomic entries and probe cancellation

The distinct-colour step of `InvertibleDotProbe.md` §3 uses crossings
between different word corners. A dot is a unit in its own corner, not
a left-regular element of the entire cyclotomic algebra. The cancellation
below retains the actual word idempotents and rectangular entries.
-/
noncomputable section
open CategoryTheory StringDiagrams
open scoped Classical
namespace OddMath.QuiverHecke
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X]
  {k : Type w} [CommRing k] (D : SKM.Datum I X) (Sc : SKM.Scalars D k)
  [Fintype I] (a : I → Polynomial k)

def cyclotomicWordEntry {n : ℕ} (s t : Word I (n + 1))
    (f : wordObj D Sc s ⟶ wordObj D Sc t) : CyclotomicAlgebra D Sc a n :=
  cyclotomicMk D Sc a n (FiniteHomMatrix.single t s f)

theorem cyclotomicWordEntry_comp {n : ℕ} (s t u : Word I (n + 1))
    (f : wordObj D Sc s ⟶ wordObj D Sc t) (g : wordObj D Sc t ⟶ wordObj D Sc u) :
    cyclotomicWordEntry D Sc a s u (f ≫ g) =
      cyclotomicWordEntry D Sc a t u g * cyclotomicWordEntry D Sc a s t f := by
  change cyclotomicMk D Sc a n _ =
    cyclotomicMk D Sc a n _ * cyclotomicMk D Sc a n _
  rw [← map_mul, FiniteHomMatrix.single_mul_single]

theorem cyclotomicWordEntry_left_support {n : ℕ} (s t : Word I (n + 1))
    (f : wordObj D Sc s ⟶ wordObj D Sc t) :
    cyclotomicWordIdempotent D Sc a t * cyclotomicWordEntry D Sc a s t f =
      cyclotomicWordEntry D Sc a s t f := by
  change cyclotomicMk D Sc a n (FiniteHomMatrix.single t t (𝟙 _)) *
    cyclotomicMk D Sc a n (FiniteHomMatrix.single t s f) = _
  rw [← map_mul, FiniteHomMatrix.single_mul_single, Category.comp_id]
  rfl

theorem cyclotomicWordEntry_right_support {n : ℕ} (s t : Word I (n + 1))
    (f : wordObj D Sc s ⟶ wordObj D Sc t) :
    cyclotomicWordEntry D Sc a s t f * cyclotomicWordIdempotent D Sc a s =
      cyclotomicWordEntry D Sc a s t f := by
  change cyclotomicMk D Sc a n (FiniteHomMatrix.single t s f) *
    cyclotomicMk D Sc a n (FiniteHomMatrix.single s s (𝟙 _)) = _
  rw [← map_mul, FiniteHomMatrix.single_mul_single, Category.id_comp]
  rfl

end OddMath.QuiverHecke
