/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.Spanning
import Mathlib.RingTheory.Polynomial.Vieta

/-!
# Central elements of the quiver Hecke supercategory

The squares `y_p = x_p²` of the dots on a word `t` commute with each other and with every dot,
so polynomials in them give an algebra map `φ_t : k[X_p | p ∈ ℕ] → End(t)` (`sqDots`). For a
colour `c`, the elementary symmetric functions of the `y_p` over the strands of colour `c`
commute with every morphism of the quiver Hecke supercategory `H` (`comm_hom`): across a crossing
of two strands of different colours `y_p` slides to the other strand, and across a crossing of
two strands of equal colour `y_a + y_{a+1}` and `y_a y_{a+1}` slide through by the relations
(1.8). These are the central elements used to show that `H_n` is finite over its centre
(Brundan–Ellis, arXiv:1701.04133v2, §11, proof of Theorem 11.7).
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams LinDiagram
open SKM (zsign)
universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X) {k : Type w}
  [CommRing k] (Sc : SKM.Scalars D k)

/-! ## The relations (1.8) as equalities -/

section Exact
variable (l r : List I)

theorem slide_left_ne (i j : I) (hij : i ≠ j)
    (h₁ : SChain (l ++ [i, j] ++ r) (pl _ [.dot l.length, .cross l.length]) (l ++ [j, i] ++ r))
    (h₂ : SChain (l ++ [i, j] ++ r) (pl _ [.cross l.length, .dot (l.length + 1)])
      (l ++ [j, i] ++ r)) :
    cl D Sc _ _ [.dot l.length, .cross l.length] h₁ =
      zsign k (D.parity i * D.parity j) • cl D Sc _ _ [.cross l.length, .dot (l.length + 1)] h₂ := by
  have p₁ : SChain [i, j] (dotsL [] i [j] 1 ++ crossL [] i j []) [j, i] := by
    simp [dotsL, crossL, Shape.dom, Shape.cod]
  have p₂ : SChain [i, j] (crossL [] i j [] ++ dotsL [j] i [] 1) [j, i] := by
    simp [dotsL, crossL, Shape.dom, Shape.cod]
  rw [cl_eq_lin D Sc l r _ p₁ _ h₁ (by simp [pl, PG.ld, PG.act, dotsL, crossL, wh]),
    cl_eq_lin D Sc l r _ p₂ _ h₂ (by simp [pl, PG.ld, PG.act, dotsL, crossL, wh, List.take_append])]
  have hr := lin_rel_eq D Sc l r (Rel.slideL i j hij)
  simp only [relation, whisker_sub, whisker_smul, Presentation.lin_sub,
    Presentation.lin_smul, sub_eq_zero] at hr
  exact hr

theorem slide_left_eq (i : I)
    (h₁ : SChain (l ++ [i, i] ++ r) (pl _ [.dot l.length, .cross l.length]) (l ++ [i, i] ++ r))
    (h₂ : SChain (l ++ [i, i] ++ r) (pl _ [.cross l.length, .dot (l.length + 1)])
      (l ++ [i, i] ++ r)) :
    cl D Sc _ _ [.dot l.length, .cross l.length] h₁ =
      zsign k (D.parity i * D.parity i) • cl D Sc _ _ [.cross l.length, .dot (l.length + 1)] h₂ +
        cl D Sc (l ++ [i, i] ++ r) _ [] rfl := by
  have p₁ : SChain [i, i] (dotsL [] i [i] 1 ++ crossL [] i i []) [i, i] := by
    simp [dotsL, crossL, Shape.dom, Shape.cod]
  have p₂ : SChain [i, i] (crossL [] i i [] ++ dotsL [i] i [] 1) [i, i] := by
    simp [dotsL, crossL, Shape.dom, Shape.cod]
  rw [cl_eq_lin D Sc l r _ p₁ _ h₁ (by simp [pl, PG.ld, PG.act, dotsL, crossL, wh]),
    cl_eq_lin D Sc l r _ p₂ _ h₂ (by simp [pl, PG.ld, PG.act, dotsL, crossL, wh, List.take_append])]
  have hr := lin_rel_eq D Sc l r (Rel.slideLEq i)
  simp only [relation, whisker_sub, whisker_smul, Presentation.lin_sub,
    Presentation.lin_smul, sub_eq_zero] at hr
  rw [sub_eq_iff_eq_add] at hr
  rw [hr, lin_whisker_idg, add_comm]
  rfl

theorem slide_right_ne (i j : I) (hij : i ≠ j)
    (h₁ : SChain (l ++ [i, j] ++ r) (pl _ [.cross l.length, .dot l.length]) (l ++ [j, i] ++ r))
    (h₂ : SChain (l ++ [i, j] ++ r) (pl _ [.dot (l.length + 1), .cross l.length])
      (l ++ [j, i] ++ r)) :
    cl D Sc _ _ [.cross l.length, .dot l.length] h₁ =
      zsign k (D.parity i * D.parity j) • cl D Sc _ _ [.dot (l.length + 1), .cross l.length] h₂ := by
  have p₁ : SChain [i, j] (crossL [] i j [] ++ dotsL [] j [i] 1) [j, i] := by
    simp [dotsL, crossL, Shape.dom, Shape.cod]
  have p₂ : SChain [i, j] (dotsL [i] j [] 1 ++ crossL [] i j []) [j, i] := by
    simp [dotsL, crossL, Shape.dom, Shape.cod]
  rw [cl_eq_lin D Sc l r _ p₁ _ h₁ (by simp [pl, PG.ld, PG.act, dotsL, crossL, wh]),
    cl_eq_lin D Sc l r _ p₂ _ h₂ (by simp [pl, PG.ld, PG.act, dotsL, crossL, wh, List.take_append])]
  have hr := lin_rel_eq D Sc l r (Rel.slideR i j hij)
  simp only [relation, whisker_sub, whisker_smul, Presentation.lin_sub,
    Presentation.lin_smul, sub_eq_zero] at hr
  exact hr

theorem slide_right_eq (i : I)
    (h₁ : SChain (l ++ [i, i] ++ r) (pl _ [.cross l.length, .dot l.length]) (l ++ [i, i] ++ r))
    (h₂ : SChain (l ++ [i, i] ++ r) (pl _ [.dot (l.length + 1), .cross l.length])
      (l ++ [i, i] ++ r)) :
    cl D Sc _ _ [.cross l.length, .dot l.length] h₁ =
      zsign k (D.parity i * D.parity i) • cl D Sc _ _ [.dot (l.length + 1), .cross l.length] h₂ +
        cl D Sc (l ++ [i, i] ++ r) _ [] rfl := by
  have p₁ : SChain [i, i] (crossL [] i i [] ++ dotsL [] i [i] 1) [i, i] := by
    simp [dotsL, crossL, Shape.dom, Shape.cod]
  have p₂ : SChain [i, i] (dotsL [i] i [] 1 ++ crossL [] i i []) [i, i] := by
    simp [dotsL, crossL, Shape.dom, Shape.cod]
  rw [cl_eq_lin D Sc l r _ p₁ _ h₁ (by simp [pl, PG.ld, PG.act, dotsL, crossL, wh]),
    cl_eq_lin D Sc l r _ p₂ _ h₂ (by simp [pl, PG.ld, PG.act, dotsL, crossL, wh, List.take_append])]
  have hr := lin_rel_eq D Sc l r (Rel.slideREq i)
  simp only [relation, whisker_sub, whisker_smul, Presentation.lin_sub,
    Presentation.lin_smul, sub_eq_zero] at hr
  rw [sub_eq_iff_eq_add] at hr
  rw [hr, lin_whisker_idg, add_comm]
  rfl

end Exact

theorem zsign_mul_self (x : ZMod 2) : zsign k x * zsign k x = 1 := by
  unfold zsign; split_ifs <;> simp

theorem cl_nil (t : List I) (h : SChain t (pl t []) t) : cl D Sc t t [] h = 𝟙 _ := by
  rw [cl, ← Presentation.diag_id]
  exact Presentation.diag_eq_of_layers_eq _ rfl

/-! ## Dots and their squares -/

/-- The dot on strand `p` of `t`; the identity if `t` has no strand `p`. -/
def xd (t : List I) (p : ℕ) : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t) :=
  cl D Sc t t [.dot p] (sChain_pl t [.dot p])

/-- The square of the dot on strand `p` of `t`. -/
def ySq (t : List I) (p : ℕ) : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t) :=
  xd D Sc t p ≫ xd D Sc t p

theorem xd_of_le {t : List I} {p : ℕ} (hp : t.length ≤ p) : xd D Sc t p = 𝟙 _ := by
  have e : pl t [PG.dot p] = pl t [] := by
    simp [pl, ld_eq_nil (show t.length < (PG.dot p).pos + (PG.dot p).width by
      simp [PG.pos, PG.width]; omega)]
  rw [xd, cl_congr D Sc (t := t) (t' := t) (gs := [.dot p]) (hs := []) _ rfl e, cl_nil]

theorem xd_comp_xd (t : List I) {p q : ℕ} (hpq : p ≠ q) :
    ∃ c : k, c * c = 1 ∧ xd D Sc t p ≫ xd D Sc t q = c • (xd D Sc t q ≫ xd D Sc t p) := by
  wlog hlt : p < q generalizing p q
  · obtain ⟨c, hc, e⟩ := this hpq.symm (by omega)
    refine ⟨c, hc, ?_⟩
    rw [e, smul_smul, hc, one_smul]
  by_cases hq : q < t.length
  · rw [xd, xd, cl_comp, cl_comp]
    exact far_swap D Sc (.dot p) (.dot q) (by simp [PG.pos, PG.width]; omega)
      (by simp [PG.pos, PG.width]; omega) _ _
  · rw [xd_of_le D Sc (show t.length ≤ q by omega)]
    exact ⟨1, one_mul 1, by simp⟩

theorem ySq_comp_xd (t : List I) (p q : ℕ) :
    ySq D Sc t p ≫ xd D Sc t q = xd D Sc t q ≫ ySq D Sc t p := by
  by_cases hpq : p = q
  · subst hpq; simp [ySq]
  obtain ⟨c, hc, e⟩ := xd_comp_xd D Sc t hpq
  simp only [ySq, Category.assoc, e, Linear.comp_smul]
  rw [← Category.assoc, e, Linear.smul_comp, smul_smul, hc, one_smul, Category.assoc]

theorem ySq_comp_ySq (t : List I) (p q : ℕ) :
    ySq D Sc t p ≫ ySq D Sc t q = ySq D Sc t q ≫ ySq D Sc t p := by
  calc ySq D Sc t p ≫ (xd D Sc t q ≫ xd D Sc t q)
      = (ySq D Sc t p ≫ xd D Sc t q) ≫ xd D Sc t q := (Category.assoc _ _ _).symm
    _ = xd D Sc t q ≫ (ySq D Sc t p ≫ xd D Sc t q) := by
      conv_lhs => rw [ySq_comp_xd]
      rw [Category.assoc]
    _ = (xd D Sc t q ≫ xd D Sc t q) ≫ ySq D Sc t p := by
      rw [Category.assoc, ySq_comp_xd]

/-! ## Polynomials in the squared dots -/

/-- The commutative subalgebra generated by the squared dots of `t`. -/
abbrev YAlg (t : List I) : Subalgebra k (End ((pres D Sc).obj (ob D t))) :=
  Algebra.adjoin k (Set.range fun p => (ySq D Sc t p : End _))

instance (t : List I) : CommRing (YAlg D Sc t) :=
  have h := Algebra.isMulCommutative_adjoin k (A := End ((pres D Sc).obj (ob D t))) (s := Set.range fun p => (ySq D Sc t p : End _))
    (by rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩ _; exact ySq_comp_ySq D Sc t q p)
  { (inferInstance : Ring (YAlg D Sc t)) with mul_comm := fun a b => h.is_comm.comm a b }

/-- Polynomials in the squared dots: `X_p ↦ x_p²` on the word `t`. -/
def sqDots (t : List I) : MvPolynomial ℕ k →ₐ[k] End ((pres D Sc).obj (ob D t)) :=
  (YAlg D Sc t).val.comp
    (MvPolynomial.aeval fun p => ⟨ySq D Sc t p, Algebra.subset_adjoin ⟨p, rfl⟩⟩)

@[simp] theorem sqDots_X (t : List I) (p : ℕ) : sqDots D Sc t (MvPolynomial.X p) = ySq D Sc t p := by
  simp [sqDots]

/-- The polynomials `P` with `φ_t(P) ≫ f = f ≫ φ_{t'}(σ P)`. -/
def Intw {t t' : List I} (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t'))
    (σ : MvPolynomial ℕ k →ₐ[k] MvPolynomial ℕ k) : Subalgebra k (MvPolynomial ℕ k) where
  carrier := {P | (sqDots D Sc t P : _ ⟶ _) ≫ f = f ≫ (sqDots D Sc t' (σ P) : _ ⟶ _)}
  mul_mem' {P Q} hP hQ := by
    change (sqDots D Sc t (P * Q) : _ ⟶ _) ≫ f = f ≫ (sqDots D Sc t' (σ (P * Q)) : _ ⟶ _)
    change (sqDots D Sc t P : _ ⟶ _) ≫ f = f ≫ (sqDots D Sc t' (σ P) : _ ⟶ _) at hP
    change (sqDots D Sc t Q : _ ⟶ _) ≫ f = f ≫ (sqDots D Sc t' (σ Q) : _ ⟶ _) at hQ
    rw [map_mul, map_mul, map_mul, End.mul_def, End.mul_def, Category.assoc, hP,
      ← Category.assoc, hQ, Category.assoc]
  add_mem' {P Q} hP hQ := by
    change (sqDots D Sc t (P + Q) : _ ⟶ _) ≫ f = f ≫ (sqDots D Sc t' (σ (P + Q)) : _ ⟶ _)
    change (sqDots D Sc t P : _ ⟶ _) ≫ f = f ≫ (sqDots D Sc t' (σ P) : _ ⟶ _) at hP
    change (sqDots D Sc t Q : _ ⟶ _) ≫ f = f ≫ (sqDots D Sc t' (σ Q) : _ ⟶ _) at hQ
    rw [map_add, map_add, map_add]
    exact (Preadditive.add_comp _ _ _ _ _ _).trans
      ((congrArg₂ (· + ·) hP hQ).trans (Preadditive.comp_add _ _ _ _ _ _).symm)
  algebraMap_mem' a := by
    change (sqDots D Sc t (algebraMap k _ a) : _ ⟶ _) ≫ f =
      f ≫ (sqDots D Sc t' (σ (algebraMap k _ a)) : _ ⟶ _)
    rw [AlgHom.commutes σ, AlgHom.commutes, AlgHom.commutes, Algebra.algebraMap_eq_smul_one]
    erw [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]

theorem intw_eq_top {t t' : List I} (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t'))
    (σ : MvPolynomial ℕ k →ₐ[k] MvPolynomial ℕ k) (h : ∀ p, MvPolynomial.X p ∈ Intw D Sc f σ) :
    Intw D Sc f σ = ⊤ := by
  rw [eq_top_iff, ← MvPolynomial.adjoin_range_X, Algebra.adjoin_le_iff]
  rintro _ ⟨p, rfl⟩
  exact h p

theorem sqDots_comp_xd (t : List I) (P : MvPolynomial ℕ k) (q : ℕ) :
    (sqDots D Sc t P : _ ⟶ _) ≫ xd D Sc t q = xd D Sc t q ≫ sqDots D Sc t P := by
  have := intw_eq_top D Sc (xd D Sc t q) (AlgHom.id k _) fun p => by
    show (sqDots D Sc t _ : _ ⟶ _) ≫ _ = _ ≫ (sqDots D Sc t _ : _ ⟶ _)
    simp only [AlgHom.id_apply, sqDots_X]
    exact ySq_comp_xd D Sc t p q
  have hP : P ∈ Intw D Sc (xd D Sc t q) (AlgHom.id k _) := this ▸ Algebra.mem_top
  exact hP

/-! ## Squared dots across a crossing -/

theorem sq_comp_of_comp {t t' : List I} {ψ : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')}
    {x : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t)}
    {x' : (pres D Sc).obj (ob D t') ⟶ (pres D Sc).obj (ob D t')} {c : k} (hc : c * c = 1)
    (h : x ≫ ψ = c • (ψ ≫ x')) : (x ≫ x) ≫ ψ = ψ ≫ (x' ≫ x') := by
  rw [Category.assoc, h, Linear.comp_smul, ← Category.assoc, h, Linear.smul_comp, smul_smul, hc,
    one_smul, Category.assoc]

theorem xd_comp_cross_far {t t' : List I} {a p : ℕ} (ha : a + 1 < t.length) (hpa : p ≠ a)
    (hpa' : p ≠ a + 1) (h : SChain t (pl t [.cross a]) t') :
    ∃ c : k, c * c = 1 ∧ xd D Sc t p ≫ cl D Sc t t' [.cross a] h =
      c • (cl D Sc t t' [.cross a] h ≫ xd D Sc t' p) := by
  have hl := length_of_sChain h
  by_cases hp : p < t.length
  · rw [xd, xd, cl_comp, cl_comp]
    rcases Nat.lt_or_gt_of_ne hpa with hlt | hgt
    · exact far_swap D Sc (.dot p) (.cross a) (by simp [PG.pos, PG.width]; omega)
        (by simp [PG.pos, PG.width]; omega) _ _
    · have h₁ : SChain t (pl t [PG.cross a, PG.dot p]) t' :=
        sChain_append_of h (by exact sChain_pl t' [.dot p])
      have h₂ : SChain t (pl t [PG.dot p, PG.cross a]) t' :=
        sChain_append_of (by exact sChain_pl t [.dot p]) h
      obtain ⟨c, hc, e⟩ := far_swap D Sc (k := k) (.cross a) (.dot p)
        (by simp [PG.pos, PG.width]; omega) (by simp [PG.pos, PG.width]; omega) h₁ h₂
      refine ⟨c, hc, ?_⟩
      simp only [List.singleton_append]
      rw [e, smul_smul, hc, one_smul]
  · rw [xd_of_le D Sc (show t.length ≤ p by omega), xd_of_le D Sc (show t'.length ≤ p by omega)]
    exact ⟨1, one_mul 1, by simp⟩

theorem ySq_comp_cross_far {t t' : List I} {a p : ℕ} (ha : a + 1 < t.length) (hpa : p ≠ a)
    (hpa' : p ≠ a + 1) (h : SChain t (pl t [.cross a]) t') :
    ySq D Sc t p ≫ cl D Sc t t' [.cross a] h = cl D Sc t t' [.cross a] h ≫ ySq D Sc t' p := by
  obtain ⟨c, hc, e⟩ := xd_comp_cross_far D Sc ha hpa hpa' h
  exact sq_comp_of_comp D Sc hc e

section Cross
variable (l r : List I)

theorem ySq_comp_cross_ne (i j : I) (hij : i ≠ j)
    (h : SChain (l ++ [i, j] ++ r) (pl _ [.cross l.length]) (l ++ [j, i] ++ r)) :
    ySq D Sc _ l.length ≫ cl D Sc _ _ [.cross l.length] h =
        cl D Sc _ _ [.cross l.length] h ≫ ySq D Sc _ (l.length + 1) ∧
      ySq D Sc _ (l.length + 1) ≫ cl D Sc _ _ [.cross l.length] h =
        cl D Sc _ _ [.cross l.length] h ≫ ySq D Sc _ l.length := by
  have hc := zsign_mul_self (k := k) (D.parity i * D.parity j)
  constructor
  · refine sq_comp_of_comp D Sc hc ?_
    rw [xd, xd, cl_comp, cl_comp]
    exact slide_left_ne D Sc l r i j hij _ _
  · refine sq_comp_of_comp D Sc hc ?_
    rw [xd, xd, cl_comp, cl_comp]
    simp only [List.singleton_append]
    rw [slide_right_ne D Sc l r i j hij _ (sChain_append_of (t₁ := l ++ [i, j] ++ r)
      (by exact sChain_pl (l ++ [i, j] ++ r) [PG.dot (l.length + 1)]) h),
      smul_smul, hc, one_smul]

/-- For two strands of equal colour, `y_a + y_{a+1}` and `y_a y_{a+1}` commute with the
crossing. -/
theorem ySq_comp_cross_eq (i : I)
    (h : SChain (l ++ [i, i] ++ r) (pl _ [.cross l.length]) (l ++ [i, i] ++ r)) :
    (ySq D Sc _ l.length + ySq D Sc _ (l.length + 1)) ≫ cl D Sc _ _ [.cross l.length] h =
        cl D Sc _ _ [.cross l.length] h ≫ (ySq D Sc _ l.length + ySq D Sc _ (l.length + 1)) ∧
      (ySq D Sc _ l.length ≫ ySq D Sc _ (l.length + 1)) ≫ cl D Sc _ _ [.cross l.length] h =
        cl D Sc _ _ [.cross l.length] h ≫ (ySq D Sc _ l.length ≫ ySq D Sc _ (l.length + 1)) := by
  have hc := zsign_mul_self (k := k) (D.parity i * D.parity i)
  -- (1.8): `x ψ = c ψ x' + 1` and `ψ x = c x' ψ + 1`, composing left to right
  have hL : xd D Sc (l ++ [i, i] ++ r) l.length ≫ cl D Sc _ _ [.cross l.length] h =
      zsign k (D.parity i * D.parity i) • (cl D Sc _ _ [.cross l.length] h ≫
        xd D Sc (l ++ [i, i] ++ r) (l.length + 1)) + 𝟙 _ := by
    rw [xd, xd, cl_comp, cl_comp]
    simp only [List.singleton_append]
    rw [slide_left_eq D Sc l r i _ (sChain_append_of h (by exact sChain_pl _ _)), cl_nil]
  have hR : cl D Sc _ _ [.cross l.length] h ≫ xd D Sc (l ++ [i, i] ++ r) l.length =
      zsign k (D.parity i * D.parity i) • (xd D Sc (l ++ [i, i] ++ r) (l.length + 1) ≫
        cl D Sc _ _ [.cross l.length] h) + 𝟙 _ := by
    rw [xd, xd, cl_comp, cl_comp]
    simp only [List.singleton_append]
    rw [slide_right_eq D Sc l r i _ (sChain_append_of (t₁ := l ++ [i, i] ++ r)
      (by exact sChain_pl (l ++ [i, i] ++ r) [PG.dot (l.length + 1)]) h), cl_nil]
  have hxy := ySq_comp_xd D Sc (l ++ [i, i] ++ r) l.length (l.length + 1)
  have hyy := ySq_comp_ySq D Sc (l ++ [i, i] ++ r) l.length (l.length + 1)
  simp only [ySq] at hxy hyy ⊢
  generalize zsign k (D.parity i * D.parity i) = c at *
  generalize xd D Sc (l ++ [i, i] ++ r) l.length = x at *
  generalize xd D Sc (l ++ [i, i] ++ r) (l.length + 1) = x' at *
  generalize cl D Sc _ _ [.cross l.length] h = ψ at *
  have hR' : x' ≫ ψ = c • (ψ ≫ x) - c • 𝟙 _ := by
    rw [hR, smul_add, smul_smul, hc, one_smul, add_sub_cancel_right]
  -- `y_a ψ = ψ y_{a+1} + u` and `y_{a+1} ψ = ψ y_a - u` with `u = c x' + x`
  have h1 : (x ≫ x) ≫ ψ = ψ ≫ (x' ≫ x') + (c • x' + x) := by
    rw [Category.assoc, hL, Preadditive.comp_add, Linear.comp_smul, ← Category.assoc, hL,
      Preadditive.add_comp, Linear.smul_comp, Category.assoc, Category.id_comp, smul_add,
      smul_smul, hc, one_smul, Category.comp_id, add_assoc]
  have h2 : (x' ≫ x') ≫ ψ = ψ ≫ (x ≫ x) - (c • x' + x) := by
    rw [Category.assoc, hR', Preadditive.comp_sub, Linear.comp_smul, Linear.comp_smul,
      ← Category.assoc, hR', Preadditive.sub_comp, Linear.smul_comp, Linear.smul_comp,
      Category.assoc, Category.id_comp, Category.comp_id, smul_sub, smul_smul, smul_smul, hc,
      one_smul, one_smul]
    abel
  have hu : (c • x' + x) ≫ (x ≫ x) = (x ≫ x) ≫ (c • x' + x) := by
    rw [Preadditive.add_comp, Preadditive.comp_add, Linear.smul_comp, Linear.comp_smul, hxy]
    simp
  refine ⟨?_, ?_⟩
  · rw [Preadditive.add_comp, Preadditive.comp_add, h1, h2]; abel
  · rw [Category.assoc, h2, Preadditive.comp_sub, ← Category.assoc, h1, Preadditive.add_comp,
      Category.assoc, hu, hyy]
    abel

end Cross

/-! ## Elementary symmetric functions of a set of variables -/

section Esymm
open MvPolynomial (rename)

/-- The `j`-th elementary symmetric function of the variables `X_p`, `p ∈ S`. -/
def esymmS (S : Finset ℕ) (j : ℕ) : MvPolynomial ℕ k := (S.val.map MvPolynomial.X).esymm j

theorem multiset_esymm_cons {R : Type*} [CommSemiring R] (x : R) (s : Multiset R) (n : ℕ) :
    (x ::ₘ s).esymm (n + 1) = s.esymm (n + 1) + x * s.esymm n := by
  simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.sum_map_mul_left]

theorem map_multiset_esymm {R S : Type*} [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (s : Multiset R) (n : ℕ) : f (s.esymm n) = (s.map f).esymm n := by
  simp [Multiset.esymm, map_multiset_sum, map_multiset_prod, Multiset.powersetCard_map,
    Multiset.map_map]

theorem esymmS_mem {A : Subalgebra k (MvPolynomial ℕ k)} {S : Finset ℕ}
    (h : ∀ p ∈ S, MvPolynomial.X p ∈ A) (j : ℕ) : esymmS (k := k) S j ∈ A := by
  refine Subalgebra.multiset_sum_mem _ fun x hx => ?_
  obtain ⟨T, hT, rfl⟩ := Multiset.mem_map.mp hx
  refine Subalgebra.multiset_prod_mem _ fun y hy => ?_
  obtain ⟨p, hp, rfl⟩ := Multiset.mem_map.mp (Multiset.mem_of_le (Multiset.mem_powersetCard.mp hT).1 hy)
  exact h p hp

theorem rename_esymmS (σ : ℕ ≃ ℕ) (S : Finset ℕ) (j : ℕ) :
    rename σ (esymmS (k := k) S j) = esymmS (S.map σ.toEmbedding) j := by
  rw [esymmS, ← AlgHom.coe_toRingHom, map_multiset_esymm]
  simp [esymmS, Multiset.map_map]

/-- Vieta: `X_p` is a root of `∏_{q ∈ S} (T - X_q)` for `p ∈ S`. -/
theorem X_pow_card {S : Finset ℕ} {p : ℕ} (hp : p ∈ S) :
    (MvPolynomial.X p : MvPolynomial ℕ k) ^ S.card = ∑ j ∈ Finset.range S.card,
      (-1) ^ j * (esymmS S (j + 1) * MvPolynomial.X p ^ (S.card - (j + 1))) := by
  have h := congrArg (Polynomial.eval (MvPolynomial.X p : MvPolynomial ℕ k))
    (Multiset.prod_X_sub_X_eq_sum_esymm (S.val.map (MvPolynomial.X : ℕ → MvPolynomial ℕ k)))
  rw [Polynomial.eval_multiset_prod, Multiset.prod_eq_zero (by
    simp only [Multiset.map_map, Function.comp_def, Multiset.mem_map]
    exact ⟨p, hp, by simp⟩), Polynomial.eval_finsetSum, Multiset.card_map,
    Finset.card_val, Finset.sum_range_succ'] at h
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_one,
    Polynomial.eval_C, Polynomial.eval_X, pow_zero, one_mul, Nat.sub_zero] at h
  have e0 : (S.val.map (MvPolynomial.X : ℕ → MvPolynomial ℕ k)).esymm 0 = 1 := by
    simp [Multiset.esymm]
  rw [e0, one_mul] at h
  rw [eq_neg_of_add_eq_zero_right h.symm, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [esymmS, pow_succ]
  ring


theorem esymmS_insert_insert_mem {A : Subalgebra k (MvPolynomial ℕ k)} {S : Finset ℕ} {a b : ℕ}
    (hab : a ≠ b) (ha : a ∉ S) (hb : b ∉ S) (hS : ∀ p ∈ S, MvPolynomial.X p ∈ A)
    (h₁ : MvPolynomial.X a + MvPolynomial.X b ∈ A) (h₂ : MvPolynomial.X a * MvPolynomial.X b ∈ A)
    (j : ℕ) : esymmS (k := k) (insert a (insert b S)) j ∈ A := by
  have hv : (insert a (insert b S)).val.map (MvPolynomial.X : ℕ → MvPolynomial ℕ k) =
      MvPolynomial.X a ::ₘ MvPolynomial.X b ::ₘ S.val.map MvPolynomial.X := by
    rw [Finset.insert_val_of_notMem (by simp [hab, ha]), Finset.insert_val_of_notMem hb]
    simp
  have he : ∀ n, (S.val.map (MvPolynomial.X : ℕ → MvPolynomial ℕ k)).esymm n ∈ A :=
    esymmS_mem hS
  have e0 : ∀ m : Multiset (MvPolynomial ℕ k), m.esymm 0 = 1 := by simp [Multiset.esymm]
  rw [esymmS, hv]
  rcases j with _ | _ | n
  · rw [e0]; exact one_mem _
  · rw [multiset_esymm_cons, multiset_esymm_cons, e0, e0, mul_one, mul_one, add_assoc,
      add_comm (MvPolynomial.X b)]
    exact add_mem (he 1) h₁
  · rw [multiset_esymm_cons, multiset_esymm_cons, multiset_esymm_cons,
      show ∀ x y z w v : MvPolynomial ℕ k, x + y * z + w * (z + y * v) =
        x + (w + y) * z + (w * y) * v by intros; ring]
    exact add_mem (add_mem (he _) (mul_mem h₁ (he _))) (mul_mem h₂ (he _))

end Esymm

/-! ## The central family -/

open scoped Classical in
/-- The strands of `t` of colour `c`. -/
def colPos (t : List I) (c : I) : Finset ℕ :=
  (Finset.range t.length).filter fun p => t[p]? = some c

theorem mem_colPos {t : List I} {c : I} {p : ℕ} : p ∈ colPos t c ↔ t[p]? = some c := by
  simp only [colPos, Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨(List.getElem?_eq_some_iff.mp h).1, h⟩⟩

theorem getElem?_swap (l r : List I) (i j : I) (p : ℕ) :
    (l ++ [j, i] ++ r)[p]? = (l ++ [i, j] ++ r)[Equiv.swap l.length (l.length + 1) p]? := by
  simp only [List.append_assoc, List.cons_append, List.nil_append]
  rcases lt_trichotomy p l.length with h | rfl | h
  · rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega), List.getElem?_append_left h,
      List.getElem?_append_left h]
  · rw [Equiv.swap_apply_left, List.getElem?_append_right le_rfl,
      List.getElem?_append_right (by omega)]
    simp
  · rw [List.getElem?_append_right (by omega)]
    rcases Nat.lt_or_ge (l.length + 1) p with h' | h'
    · rw [Equiv.swap_apply_of_ne_of_ne (by omega) (by omega),
        List.getElem?_append_right (by omega),
        show p - l.length = (p - l.length - 2) + 2 by omega]
      simp
    · obtain rfl : p = l.length + 1 := by omega
      rw [Equiv.swap_apply_right, List.getElem?_append_right le_rfl]
      simp

theorem colPos_swap (l r : List I) (i j c : I) :
    colPos (l ++ [j, i] ++ r) c =
      (colPos (l ++ [i, j] ++ r) c).map (Equiv.swap l.length (l.length + 1)).toEmbedding := by
  ext p
  rw [Finset.mem_map_equiv, mem_colPos, mem_colPos, getElem?_swap, Equiv.symm_swap]

/-- The elementary symmetric functions of the variables of each colour of `t`. -/
def symmMap (t : List I) : MvPolynomial (I × ℕ) k →ₐ[k] MvPolynomial ℕ k :=
  MvPolynomial.aeval fun cj => esymmS (colPos t cj.1) cj.2

/-- The central family: the elementary symmetric functions, colour by colour, of the squared
dots of `t`. -/
def zeta (t : List I) : MvPolynomial (I × ℕ) k →ₐ[k] End ((pres D Sc).obj (ob D t)) :=
  (sqDots D Sc t).comp (symmMap t)

theorem zeta_comp_xd (t : List I) (q : MvPolynomial (I × ℕ) k) (p : ℕ) :
    (zeta D Sc t q : _ ⟶ _) ≫ xd D Sc t p = xd D Sc t p ≫ zeta D Sc t q :=
  sqDots_comp_xd D Sc t _ p

section Cross
variable (l r : List I)

theorem zeta_comp_cross_ne (i j : I) (hij : i ≠ j)
    (h : SChain (l ++ [i, j] ++ r) (pl _ [.cross l.length]) (l ++ [j, i] ++ r))
    (q : MvPolynomial (I × ℕ) k) :
    (zeta D Sc _ q : _ ⟶ _) ≫ cl D Sc _ _ [.cross l.length] h =
      cl D Sc _ _ [.cross l.length] h ≫ zeta D Sc _ q := by
  set σ := Equiv.swap l.length (l.length + 1)
  have htop := intw_eq_top D Sc (cl D Sc _ _ [.cross l.length] h) (MvPolynomial.rename σ) fun p => by
    show (sqDots D Sc _ _ : _ ⟶ _) ≫ _ = _ ≫ (sqDots D Sc _ _ : _ ⟶ _)
    rw [MvPolynomial.rename_X, sqDots_X, sqDots_X]
    obtain ⟨h₁, h₂⟩ := ySq_comp_cross_ne D Sc l r i j hij h
    by_cases hp : p = l.length
    · subst hp; rw [Equiv.swap_apply_left]; exact h₁
    by_cases hp' : p = l.length + 1
    · subst hp'; rw [Equiv.swap_apply_right]; exact h₂
    rw [Equiv.swap_apply_of_ne_of_ne hp hp']
    exact ySq_comp_cross_far D Sc (by simp) hp hp' h
  have hσ : (MvPolynomial.rename σ).comp (symmMap (k := k) (l ++ [i, j] ++ r)) =
      symmMap (l ++ [j, i] ++ r) := by
    refine MvPolynomial.algHom_ext fun cj => ?_
    simp only [AlgHom.comp_apply, symmMap, MvPolynomial.aeval_X]
    rw [rename_esymmS, colPos_swap l r i j]
  have hmem : symmMap (k := k) (l ++ [i, j] ++ r) q ∈
      Intw D Sc (cl D Sc _ _ [.cross l.length] h) (MvPolynomial.rename σ) := htop ▸ Algebra.mem_top
  have := hmem
  change (sqDots D Sc _ _ : _ ⟶ _) ≫ _ = _ ≫ (sqDots D Sc _ _ : _ ⟶ _) at this
  rw [show MvPolynomial.rename σ (symmMap (l ++ [i, j] ++ r) q) = symmMap (l ++ [j, i] ++ r) q by
    rw [← hσ]; rfl] at this
  exact this

theorem zeta_comp_cross_eq (i : I)
    (h : SChain (l ++ [i, i] ++ r) (pl _ [.cross l.length]) (l ++ [i, i] ++ r))
    (q : MvPolynomial (I × ℕ) k) :
    (zeta D Sc _ q : _ ⟶ _) ≫ cl D Sc _ _ [.cross l.length] h =
      cl D Sc _ _ [.cross l.length] h ≫ zeta D Sc _ q := by
  set A := Intw D Sc (cl D Sc _ _ [.cross l.length] h) (AlgHom.id k _)
  have hfar : ∀ p, p ≠ l.length → p ≠ l.length + 1 → MvPolynomial.X p ∈ A := fun p hp hp' => by
    show (sqDots D Sc _ _ : _ ⟶ _) ≫ _ = _ ≫ (sqDots D Sc _ _ : _ ⟶ _)
    rw [AlgHom.id_apply, sqDots_X]
    exact ySq_comp_cross_far D Sc (by simp) hp hp' h
  obtain ⟨hs, hp⟩ := ySq_comp_cross_eq D Sc l r i h
  have h₁ : MvPolynomial.X l.length + MvPolynomial.X (l.length + 1) ∈ A := by
    show (sqDots D Sc _ _ : _ ⟶ _) ≫ _ = _ ≫ (sqDots D Sc _ _ : _ ⟶ _)
    rw [AlgHom.id_apply, map_add, sqDots_X, sqDots_X]
    exact hs
  have h₂ : MvPolynomial.X l.length * MvPolynomial.X (l.length + 1) ∈ A := by
    show (sqDots D Sc _ _ : _ ⟶ _) ≫ _ = _ ≫ (sqDots D Sc _ _ : _ ⟶ _)
    rw [AlgHom.id_apply, map_mul, sqDots_X, sqDots_X, End.mul_def]
    rw [ySq_comp_ySq] at hp
    exact hp
  have hgen : ∀ c n, esymmS (k := k) (colPos (l ++ [i, i] ++ r) c) n ∈ A := by
    intro c n
    by_cases hc : c = i
    · subst hc
      set S := ((colPos (l ++ [c, c] ++ r) c).erase l.length).erase (l.length + 1)
      have e : colPos (l ++ [c, c] ++ r) c = insert l.length (insert (l.length + 1) S) := by
        ext p
        simp only [S, Finset.mem_insert, Finset.mem_erase]
        constructor
        · intro hp; by_cases h1 : p = l.length; · exact Or.inl h1
          by_cases h2 : p = l.length + 1; · exact Or.inr (Or.inl h2)
          exact Or.inr (Or.inr ⟨h2, h1, hp⟩)
        · rintro (rfl | rfl | ⟨-, -, hp⟩)
          · rw [mem_colPos]; simp
          · rw [mem_colPos]; simp
          · exact hp
      rw [e]
      exact esymmS_insert_insert_mem (by omega) (by simp [S]) (by simp [S])
        (fun p hp => hfar p (by simp [S] at hp; exact hp.2.1) (by simp [S] at hp; exact hp.1))
        h₁ h₂ n
    · refine esymmS_mem (fun p hp => hfar p ?_ ?_) n
      · rintro rfl; rw [mem_colPos] at hp; simp at hp; exact hc hp.symm
      · rintro rfl; rw [mem_colPos] at hp; simp at hp; exact hc hp.symm
  have hmem : symmMap (k := k) (l ++ [i, i] ++ r) q ∈ A := by
    induction q using MvPolynomial.induction_on with
    | C a => rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]; exact algebraMap_mem _ _
    | add P Q hP hQ => rw [map_add]; exact add_mem hP hQ
    | mul_X P cj hP =>
      rw [map_mul, symmMap, MvPolynomial.aeval_X]
      exact mul_mem hP (hgen _ _)
  exact hmem

end Cross

theorem zeta_comp_gen {t t' : List I} (g : PG) (h : SChain t (pl t [g]) t')
    (q : MvPolynomial (I × ℕ) k) :
    (zeta D Sc t q : _ ⟶ _) ≫ cl D Sc t t' [g] h = cl D Sc t t' [g] h ≫ zeta D Sc t' q := by
  cases g with
  | dot p =>
    obtain rfl : t = t' := tgt_eq h
    exact zeta_comp_xd D Sc t q p
  | cross a =>
    by_cases ha : a + 1 < t.length
    · obtain ⟨l, x, y, r, rfl, rfl⟩ := exists_split_cross ha
      have ht : tgt (l ++ [x, y] ++ r) [.cross l.length] = l ++ [y, x] ++ r := by
        simp [PG.act]
      obtain rfl : _ = t' := ht ▸ tgt_eq h
      by_cases hxy : x = y
      · subst hxy
        exact zeta_comp_cross_eq D Sc l r x h q
      · exact zeta_comp_cross_ne D Sc l r x y hxy h q
    · have e : pl t [PG.cross a] = pl t [] := by
        simp [pl, ld_eq_nil (show t.length < (PG.cross a).pos + (PG.cross a).width by
          simp [PG.pos, PG.width]; omega)]
      obtain rfl : t = t' := (e ▸ h :)
      rw [cl_congr D Sc (t := t) (t' := t) (gs := [.cross a]) (hs := []) _ rfl e, cl_nil]
      simp

theorem zeta_comp_cl {t t' : List I} (gs : List PG) (h : SChain t (pl t gs) t')
    (q : MvPolynomial (I × ℕ) k) :
    (zeta D Sc t q : _ ⟶ _) ≫ cl D Sc t t' gs h = cl D Sc t t' gs h ≫ zeta D Sc t' q := by
  induction gs generalizing t with
  | nil =>
    obtain rfl : t = t' := h
    rw [cl_nil]; simp
  | cons g gs ih =>
    have e := cl_append D Sc [g] gs h
    simp only [List.singleton_append] at e
    rw [e, ← Category.assoc, zeta_comp_gen, Category.assoc, ih, Category.assoc]

/-- The central family commutes with every morphism of `H`. -/
theorem zeta_comp {t t' : List I} (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t'))
    (q : MvPolynomial (I × ℕ) k) : (zeta D Sc t q : _ ⟶ _) ≫ f = f ≫ zeta D Sc t' q := by
  induction f using (pres D Sc).hom_induction with
  | diag d =>
    obtain ⟨ls, h, rfl⟩ := exists_mkD d
    rw [diag_mkD_eq_cl D Sc ls h _ (exists_pl h)]
    exact zeta_comp_cl D Sc _ _ q
  | zero => simp
  | add f g hf hg => rw [Preadditive.comp_add, Preadditive.add_comp, hf, hg]
  | smul c f hf => rw [Linear.comp_smul, Linear.smul_comp, hf]

end OddMath.QuiverHecke
