import StringDiagrams.Super.SVec

/-! # Transporting inverse matrix rows through given charts

The normalized left cap of DeformedMatrixComparison comes from an inverse
unit-matrix row. Commuting forward matrix squares transport that exact
inverse, then its specified coordinate. These kernels are proved before
substituting concrete balanced-coend carriers.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.FiniteSuperspace
universe u
variable {k : Type u} [CommRing k]

/-- The underlying linear equivalence of a given superspace isomorphism. -/
def isoLinearEquiv {V W : SVec k} (e : V ≅ W) : V ≃ₗ[k] W where
  toLinearMap := e.hom
  invFun := e.inv
  left_inv x := congrArg (fun f : V ⟶ V => f x) e.hom_inv_id
  right_inv x := congrArg (fun f : W ⟶ W => f x) e.inv_hom_id

/-- A commuting forward matrix square also commutes on the given inverses. -/
theorem inverse_square {V W V' W' : SVec k} (e : V ≅ W) (f : V' ≅ W')
    (s : V →ₗ[k] V') (t : W →ₗ[k] W')
    (h : t ∘ₗ SVec.toLinearMap e.hom = SVec.toLinearMap f.hom ∘ₗ s) :
    s ∘ₗ SVec.toLinearMap e.inv = SVec.toLinearMap f.inv ∘ₗ t := by
  apply LinearMap.ext
  intro x
  have he := (isoLinearEquiv e).apply_symm_apply x
  have hf := (isoLinearEquiv f).symm_apply_apply (s (e.inv x))
  have hx := congrArg f.inv (LinearMap.congr_fun h (e.inv x))
  exact hf.symm.trans (hx.symm.trans (congrArg (fun z => f.inv (t z)) he))

/-- Two given matrix comparisons through a common relative chart supply
the direct old-to-new forward square, with no additional compatibility premise. -/
theorem commonChart_square {A B V W V' W' : SVec k}
    (a : A ≃ₗ[k] V) (b : B ≃ₗ[k] W) (s : A ≃ₗ[k] V') (t : B ≃ₗ[k] W')
    (e : V ≅ W) (f : V' ≅ W') (r : A →ₗ[k] B)
    (hOld : b.toLinearMap ∘ₗ r = SVec.toLinearMap e.hom ∘ₗ a.toLinearMap)
    (hNew : t.toLinearMap ∘ₗ r = SVec.toLinearMap f.hom ∘ₗ s.toLinearMap) :
    (b.symm.trans t).toLinearMap ∘ₗ SVec.toLinearMap e.hom =
      SVec.toLinearMap f.hom ∘ₗ (a.symm.trans s).toLinearMap := by
  apply LinearMap.ext
  intro x
  change t (b.symm (e.hom x)) = f.hom (s (a.symm x))
  calc
    t (b.symm (e.hom x)) = t (b.symm (e.hom (a (a.symm x)))) :=
      congrArg (fun z => t (b.symm (e.hom z))) (a.apply_symm_apply x).symm
    _ = t (b.symm (b (r (a.symm x)))) :=
      congrArg (fun z => t (b.symm z)) (LinearMap.congr_fun hOld (a.symm x)).symm
    _ = t (r (a.symm x)) := congrArg t (b.symm_apply_apply _)
    _ = f.hom (s (a.symm x)) := LinearMap.congr_fun hNew (a.symm x)

/-- Coordinate squares through a common chart retain the same change of
unshifted value coordinates. -/
theorem commonCoordinate_square {A V V' Z Z₀ Z₁ : Type u}
    [AddCommMonoid A] [Module k A] [AddCommMonoid V] [Module k V]
    [AddCommMonoid V'] [Module k V'] [AddCommMonoid Z] [Module k Z]
    [AddCommMonoid Z₀] [Module k Z₀] [AddCommMonoid Z₁] [Module k Z₁]
    (a : A ≃ₗ[k] V) (s : A ≃ₗ[k] V') (d : Z ≃ₗ[k] Z₀) (d' : Z ≃ₗ[k] Z₁)
    (z : A →ₗ[k] Z) (z₀ : V →ₗ[k] Z₀) (z₁ : V' →ₗ[k] Z₁)
    (hOld : z₀ ∘ₗ a.toLinearMap = d.toLinearMap ∘ₗ z)
    (hNew : z₁ ∘ₗ s.toLinearMap = d'.toLinearMap ∘ₗ z) :
    z₁ ∘ₗ (a.symm.trans s).toLinearMap = (d.symm.trans d').toLinearMap ∘ₗ z₀ := by
  apply LinearMap.ext
  intro x
  change z₁ (s (a.symm x)) = d' (d.symm (z₀ x))
  calc
    z₁ (s (a.symm x)) = d' (z (a.symm x)) := LinearMap.congr_fun hNew _
    _ = d' (d.symm (d (z (a.symm x)))) := congrArg d' (d.symm_apply_apply _).symm
    _ = d' (d.symm (z₀ (a (a.symm x)))) :=
      congrArg (fun y => d' (d.symm y)) (LinearMap.congr_fun hOld _).symm
    _ = d' (d.symm (z₀ x)) := congrArg (fun y => d' (d.symm (z₀ y))) (a.apply_symm_apply x)

/-- Projecting and unshifting a specified inverse row commutes with the
same charts as its forward matrix. No cap normalization is changed. -/
theorem inverse_row_square {V W V' W' : SVec k} {Z Z' : Type u}
    [AddCommMonoid Z] [Module k Z] [AddCommMonoid Z'] [Module k Z']
    (e : V ≅ W) (f : V' ≅ W') (s : V →ₗ[k] V') (t : W →ₗ[k] W')
    (d : Z →ₗ[k] Z') (z : V →ₗ[k] Z) (z' : V' →ₗ[k] Z')
    (hMatrix : t ∘ₗ SVec.toLinearMap e.hom = SVec.toLinearMap f.hom ∘ₗ s)
    (hCoordinate : z' ∘ₗ s = d ∘ₗ z) :
    d ∘ₗ (z ∘ₗ SVec.toLinearMap e.inv) =
      (z' ∘ₗ SVec.toLinearMap f.inv) ∘ₗ t := by
  apply LinearMap.ext
  intro x
  have hz := LinearMap.congr_fun hCoordinate (e.inv x)
  have hi := LinearMap.congr_fun (inverse_square e f s t hMatrix) x
  exact hz.symm.trans (congrArg z' hi)
end OddMath.FiniteSuperspace
