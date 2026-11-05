import OddMath.SKM.RouquierBoundary
import StringDiagrams.Super.Parity

/-! # Boundary coefficients through an even upper-loop chart

Brundan–Ellis (1.13)–(1.14): the actual dotted-unit boundary coefficients
transport along an even isomorphism intertwining every prescribed cup.
The two upper adjunctions may have different target objects. The common
central object and the finite window are retained, including window zero.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory BicategoryStruct
namespace OddMath.SKM.RouquierBoundaryTransport
universe u v w r
variable {k : Type r} [CommRing k] {B : Type u} [BicategoryStruct.{w,v} B]
  [∀ a b : B, Preadditive (a ⟶ b)] [∀ a b : B, Linear k (a ⟶ b)]
  [∀ a b : B, Supercategory k (a ⟶ b)]
  {a b b' : B} {E : a ⟶ b} {F : b ⟶ a} {E' : a ⟶ b'} {F' : b' ⟶ a}
  {A : SuperAdjunction (k := k) E F} {x : End E} {p : ZMod 2} {n : ℕ}

/-- Every inverse row is transported by the inverse chart, with all finite matrix identities. -/
def ofIso (V : RouquierBoundary.Coefficients A x p n)
    (A' : SuperAdjunction (k := k) E' F') (x' : End E')
    (e : E ≫ F ≅ E' ≫ F') (he : e.hom ∈ parity (R := k) _ _ 0)
    (hx' : x' ∈ parity (R := k) _ _ p)
    (hcup : ∀ j, RouquierBoundary.cup A x j ≫ e.hom = RouquierBoundary.cup A' x' j) :
    RouquierBoundary.Coefficients A' x' p n where
  dot_mem := hx'
  coeff j := e.inv ≫ V.coeff j
  coeff_mem j := by
    simpa only [zero_add] using comp_mem (Supercategory.inv_mem e he) (V.coeff_mem j)
  total := by
    have ht := congrArg (fun f => e.inv ≫ f ≫ e.hom) V.total
    simp only [Preadditive.comp_sum, Preadditive.sum_comp, Category.assoc,
      Category.id_comp, Iso.inv_hom_id] at ht
    simpa only [Category.assoc, hcup] using ht
  entry j l hj hl := by
    rw [← hcup j]
    simpa only [Category.assoc, Iso.hom_inv_id_assoc] using V.entry j l hj hl

end OddMath.SKM.RouquierBoundaryTransport
