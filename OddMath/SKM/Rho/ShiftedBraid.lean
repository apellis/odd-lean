import OddMath.SKM.Rho.Braid
import OddMath.SKM.Rho.ShiftedWhisker

/-!
# Shifted Braid for ρ

Supporting calculations for Brundan–Ellis, *Super Kac–Moody 2-categories*,
arXiv:1701.04133v2, Proposition 9.8 with the corrected crossing sign.
These calculations use a purely even commutative coefficient ring and the
existing super Kac–Moody presentation.
-/
noncomputable section
open CategoryTheory StringDiagrams Supercategory
namespace OddMath.SKM.RhoCoefficients
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] {D : Datum I X}
  {k : Type w} [CommRing k] {Sc : Scalars D k} {sy : Symmetrizer D} {hc : Sc.Homogeneous}

def dotFirst3 (t : k) (ν μ : X) (i j a : I) (h : wt D μ (ups [i,j,a]) = ν) :
    rhoUpAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [i,j,a] h ⟶ rhoUpAt ν μ [i,j,a] h :=
  psiCoeff t (D.parity i) • cl D Sc ν [dn a,dn j,dn i] [dn a,dn j,dn i]
    ((ddotL i).map (whL [dn a,dn j] []))

theorem dotFirst3_pow (t : k) (ν μ : X) (i j a : I)
    (h : wt D μ (ups [i,j,a]) = ν) (n : ℕ) :
    cpow (dotFirst3 (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j a h) n =
      psiCoeff t (D.parity i) ^ n • cl D Sc ν [dn a,dn j,dn i] [dn a,dn j,dn i]
        ((ddotsL i n).map (whL [dn a,dn j] [])) := by
  have H : cpow (dotFirst3 (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j a h) n =
      cpow (psiCoeff t (D.parity i) • cl D Sc ν [dn a,dn j,dn i] [dn a,dn j,dn i]
        ((ddotL i).map (whL [dn a,dn j] []))) n := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg (fun f => f ≫
        (psiCoeff t (D.parity i) • cl D Sc ν [dn a,dn j,dn i] [dn a,dn j,dn i]
          ((ddotL i).map (whL [dn a,dn j] [])))) ih
  exact H.trans (placed_dot_power (D := D) (Sc := Sc) ν [dn a,dn j] [] i (psiCoeff t (D.parity i)) n)

def dotMiddle3 (t : k) (ν μ : X) (i j a : I) (h : wt D μ (ups [i,j,a]) = ν) :
    rhoUpAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [i,j,a] h ⟶ rhoUpAt ν μ [i,j,a] h :=
  psiCoeff t (D.parity j) • cl D Sc ν [dn a,dn j,dn i] [dn a,dn j,dn i]
    ((ddotL j).map (whL [dn a] [dn i]))

theorem dotMiddle3_pow (t : k) (ν μ : X) (i j a : I)
    (h : wt D μ (ups [i,j,a]) = ν) (n : ℕ) :
    cpow (dotMiddle3 (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j a h) n =
      psiCoeff t (D.parity j) ^ n • cl D Sc ν [dn a,dn j,dn i] [dn a,dn j,dn i]
        ((ddotsL j n).map (whL [dn a] [dn i])) := by
  have H : cpow (dotMiddle3 (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j a h) n =
      cpow (psiCoeff t (D.parity j) • cl D Sc ν [dn a,dn j,dn i] [dn a,dn j,dn i]
        ((ddotL j).map (whL [dn a] [dn i]))) n := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg (fun f => f ≫
        (psiCoeff t (D.parity j) • cl D Sc ν [dn a,dn j,dn i] [dn a,dn j,dn i]
          ((ddotL j).map (whL [dn a] [dn i])))) ih
  exact H.trans (placed_dot_power (D := D) (Sc := Sc) ν [dn a] [dn i] j (psiCoeff t (D.parity j)) n)

def dotLast3 (t : k) (ν μ : X) (i j a : I) (h : wt D μ (ups [i,j,a]) = ν) :
    rhoUpAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [i,j,a] h ⟶ rhoUpAt ν μ [i,j,a] h :=
  psiCoeff t (D.parity a) • cl D Sc ν [dn a,dn j,dn i] [dn a,dn j,dn i]
    ((ddotL a).map (whL [] [dn j,dn i]))

theorem dotLast3_pow (t : k) (ν μ : X) (i j a : I)
    (h : wt D μ (ups [i,j,a]) = ν) (n : ℕ) :
    cpow (dotLast3 (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j a h) n =
      psiCoeff t (D.parity a) ^ n • cl D Sc ν [dn a,dn j,dn i] [dn a,dn j,dn i]
        ((ddotsL a n).map (whL [] [dn j,dn i])) := by
  have H : cpow (dotLast3 (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j a h) n =
      cpow (psiCoeff t (D.parity a) • cl D Sc ν [dn a,dn j,dn i] [dn a,dn j,dn i]
        ((ddotL a).map (whL [] [dn j,dn i]))) n := by
    induction n with
    | zero => rfl
    | succ n ih => exact congrArg (fun f => f ≫
        (psiCoeff t (D.parity a) • cl D Sc ν [dn a,dn j,dn i] [dn a,dn j,dn i]
          ((ddotL a).map (whL [] [dn j,dn i])))) ih
  exact H.trans (placed_dot_power (D := D) (Sc := Sc) ν [] [dn j,dn i] a (psiCoeff t (D.parity a)) n)

def rhoForget3 (ν μ : X) (i j a : I) (h : wt D μ (ups [i,j,a]) = ν) :
    (rhoUpAt (Sc := Sc) (sy := sy) (hc := hc) ν μ [i,j,a] h ⟶ rhoUpAt ν μ [i,j,a] h) →ₗ[k]
      ((pres D Sc).obj (ob D ν [dn a,dn j,dn i]) ⟶ (pres D Sc).obj (ob D ν [dn a,dn j,dn i])) where
  toFun f := f
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem braidMonomial_powers (t : k) (ν μ : X) (i j : I)
    (h : wt D μ (ups [i,j,i]) = ν) (r q s : ℕ) :
    rhoForget3 (Sc := Sc) (sy := sy) (hc := hc) ν μ i j i h
      (cpow (dotLast3 t ν μ i j i h) s ≫ cpow (dotMiddle3 t ν μ i j i h) q ≫
        cpow (dotFirst3 t ν μ i j i h) r) = braidMonomial (Sc := Sc) t ν i j r q s := by
  simp only [dotFirst3_pow, dotMiddle3_pow, dotLast3_pow,
    Linear.smul_comp, Linear.comp_smul, smul_smul, rhoForget3, LinearMap.coe_mk, AddHom.coe_mk]
  have h1 : SChain [dn i,dn j,dn i] ((ddotsL i s).map (whL [] [dn j,dn i])) [dn i,dn j,dn i] :=
    (sChain_ddotsL i s).wh [] [dn j,dn i] rfl rfl
  have h2 : SChain [dn i,dn j,dn i] ((ddotsL j q).map (whL [dn i] [dn i])) [dn i,dn j,dn i] :=
    (sChain_ddotsL j q).wh [dn i] [dn i] rfl rfl
  have h3 : SChain [dn i,dn j,dn i] ((ddotsL i r).map (whL [dn i,dn j] [])) [dn i,dn j,dn i] :=
    (sChain_ddotsL i r).wh [dn i,dn j] [] rfl rfl
  have H : cl D Sc ν [dn i,dn j,dn i] [dn i,dn j,dn i]
      (reversedDots3 i j s q r) =
      cl D Sc ν [dn i,dn j,dn i] [dn i,dn j,dn i] ((ddotsL i s).map (whL [] [dn j,dn i])) ≫
      cl D Sc ν [dn i,dn j,dn i] [dn i,dn j,dn i] ((ddotsL j q).map (whL [dn i] [dn i])) ≫
      cl D Sc ν [dn i,dn j,dn i] [dn i,dn j,dn i] ((ddotsL i r).map (whL [dn i,dn j] [])) := by
    rw [cl_comp h2 h3, cl_comp h1 (h2.append h3)]
    simp only [reversedDots3, List.append_assoc]
  rw [braidMonomial, H]
  congr 1
  ring

theorem crossing_braid_eq (t : k) (ht : t^2 = -1) (ν μ : X) (i j : I)
    (h : wt D μ (ups [i,j,i]) = ν) (hij : i ≠ j) :
    (crossLeft3 (Sc := Sc) (sy := sy) (hc := hc) t ν μ i j i h ≫
      crossRight3 t ν μ j i i ((wt_swap_left3 μ i j i).trans h) ≫
      crossLeft3 t ν μ j i i ((wt_swap_right3 μ j i i).trans ((wt_swap_left3 μ i j i).trans h))) -
    (crossRight3 t ν μ i j i h ≫
      crossLeft3 t ν μ i i j ((wt_swap_right3 μ i j i).trans h) ≫
      crossRight3 t ν μ i i j ((wt_swap_left3 μ i i j).trans ((wt_swap_right3 μ i j i).trans h))) =
    (Sc.t i j : k) • ∑ s ∈ Finset.range (D.dn i j),
      zsign k (D.parity i * (D.parity j+s)) •
        (cpow (dotLast3 t ν μ i j i h) s ≫ cpow (dotMiddle3 t ν μ i j i h) 0 ≫
          cpow (dotFirst3 t ν μ i j i h) (D.dn i j-1-s)) +
    ∑ p ∈ Finset.Ioo 0 (D.dn i j), ∑ q ∈ Finset.Ioo 0 (D.dn j i),
      Sc.s i j p q • ∑ s ∈ Finset.range p,
        zsign k (D.parity i * (D.parity j+s)) •
          (cpow (dotLast3 t ν μ i j i h) s ≫ cpow (dotMiddle3 t ν μ i j i h) q ≫
            cpow (dotFirst3 t ν μ i j i h) (p-1-s)) := by
  apply (show Function.Injective (rhoForget3 (Sc := Sc) (sy := sy) (hc := hc) ν μ i j i h)
    from fun _ _ e => e)
  simp only [map_add, map_sub, map_sum, map_smul]
  simp only [braidMonomial_powers]
  simp only [crossLeft3_comp, crossRight3_comp, rhoForget3, LinearMap.coe_mk, AddHom.coe_mk]
  rw [← smul_sub]
  exact crossing_braid_eq_raw (Sc := Sc) t ht ν i j hij

end OddMath.SKM.RhoCoefficients
