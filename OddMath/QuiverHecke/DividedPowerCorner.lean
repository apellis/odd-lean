/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.EnvelopeDividedPowers
import OddMath.QuiverHecke.CornerProjectors
import OddMath.QuiverHecke.HomDimension
import OddMath.QuiverHecke.Centre
import OddMath.Frontier.OnhStructure


/-!
# Endomorphisms of the divided-power projectives in degrees `≤ 0`

Input to the surjectivity half of Brundan–Ellis, arXiv:1701.04133v2, Theorem 11.3, along the
route of Khovanov–Lauda, arXiv:0803.4121v2, §3.2, here for projectives. Let `b = 1_{i^{(r)}}` be
the divided-power idempotent of the word `iʳ` (`evenCornerProjector`, `oddCornerProjector`).
Then for every map `g : iʳ → iʳ` of the quiver Hecke supercategory of degree `d ≤ 0`,
`b g b` is a scalar multiple of `b` (`evenCornerProjector_mul_mul_mem`,
`oddCornerProjector_mul_mul_mem`), over any commutative ring and for homogeneous scalars. So
the degree-zero part of `End(P(i^{(r)}))` is spanned by the identity, and its maps of negative
degree vanish.

Proof. `End(iʳ)` is spanned by the image of the (odd) nilHecke ring, since every diagram on `iʳ`
is a product of dots and crossings (`span_range_evenNilHecke`, `span_range_oddNilHecke`). In
the nilHecke ring, `b T b = c · b` with `c` a polynomial in the dots: for an even colour,
`π_{w_0} T π_{w_0} = ∂_{w_0}(x^ρ T(1)) π_{w_0}` (categorification-lean,
`Categorification.NilHecke.demIdem_mul_mul_demIdem`; Khovanov–Lauda §2.2); for an odd colour,
`e T e = e f` with `f` a skew polynomial (Ellis–Khovanov–Lauda, arXiv:1111.1320v1, §4.1.2,
`OnhStructure.thick_cornerPre`), transported along the reflected opposite that defines
`oppositeProjector` (`oppositeProjector_mul_mul`). Monomials of positive degree in the dots have
positive degree, so `b g b` lies in the span of maps of positive degree plus `k b`; its
component in degree `d ≤ 0` is then a multiple of `b` (`mem_span_singleton_of_mem_sup`). For
`r ≤ 1`, `b = 1` and only dots occur (`corner_mem_span_one`).
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams

universe u v w
variable {I : Type u} {X : Type v} [AddCommGroup X] (D : SKM.Datum I X)
variable {k : Type w} [CommRing k] (Sc : SKM.Scalars D k)

theorem act_replicate (g : PG) (r : ℕ) (i : I) :
    g.act (List.replicate r i) = List.replicate r i := by
  cases g with
  | dot a => rfl
  | cross a =>
    simp only [PG.act, List.drop_replicate]
    by_cases h : a + 1 < r
    · obtain ⟨m, rfl⟩ : ∃ m, r = a + 1 + 1 + m := ⟨r - a - 2, by omega⟩
      simp only [show a + 1 + 1 + m - a = m + 1 + 1 by omega, List.replicate_succ,
        List.take_replicate]
      rw [show min a (a + 1 + 1 + m) = a by omega, ← List.replicate_succ, ← List.replicate_succ,
        ← List.replicate_add]
      congr 1; omega
    · rcases hr : r - a with _ | _ | m
      · rfl
      · rfl
      · omega

theorem cl_eq_one_of_pl_eq_nil {t : List I} {gs : List PG} (hgs : pl t gs = [])
    (h : SChain t (pl t gs) t) : cl D Sc t t gs h = 𝟙 _ := by
  rw [cl, ← Presentation.diag_id]
  exact Presentation.diag_eq_of_layers_eq _ (by simp [hgs, layList])

/-- The diagrams on `iʳ` lie in any submonoid of `End(iʳ)` containing the diagrams of single
dots and crossings. -/
theorem cl_replicate_mem (i : I) (r : ℕ) (S : Submonoid (Corner D Sc i r))
    (hdot : ∀ a (h : SChain (List.replicate r i) (pl (List.replicate r i) [PG.dot a])
      (List.replicate r i)), cl D Sc _ _ [PG.dot a] h ∈ S)
    (hcross : ∀ a (h : SChain (List.replicate r i) (pl (List.replicate r i) [PG.cross a])
      (List.replicate r i)), cl D Sc _ _ [PG.cross a] h ∈ S)
    (gs : List PG) (h : SChain (List.replicate r i) (pl (List.replicate r i) gs)
      (List.replicate r i)) : cl D Sc _ _ gs h ∈ S := by
  induction gs with
  | nil => rw [cl_nil]; exact S.one_mem
  | cons g gs ih =>
    have e := cl_append D Sc [g] gs (t := List.replicate r i) h
    simp only [List.singleton_append] at e
    rw [e]
    have key : ∀ (u : List I) (hu : u = List.replicate r i)
        (h₁ : SChain (List.replicate r i) (pl (List.replicate r i) [g]) u)
        (h₂ : SChain u (pl u gs) (List.replicate r i)),
        (cl D Sc _ u [g] h₁ ≫ cl D Sc u _ gs h₂ : Corner D Sc i r) ∈ S := by
      rintro u rfl h₁ h₂
      refine S.mul_mem (ih h₂) ?_
      cases g with
      | dot a => exact hdot a h₁
      | cross a => exact hcross a h₁
    exact key _ (by simp [act_replicate]) _ _

section Generic

variable {V : Type*} [AddCommGroup V] [Module k V] (N : ℤ → Submodule k V)
  [DirectSum.Decomposition N]

/-- In a `ℤ`-graded module, an element of degree `d ≤ 0` that is a combination of elements of
positive degree and of an element `b` of degree `0` is a multiple of `b`. -/
theorem mem_span_singleton_of_mem_sup {b x : V} (hb : b ∈ N 0) {d : ℤ} (hd : d ≤ 0)
    (hx : x ∈ N d)
    (hM : x ∈ Submodule.span k {y | ∃ e : ℤ, 0 < e ∧ y ∈ N e} ⊔ k ∙ b) :
    x ∈ k ∙ b := by
  classical
  obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.1 hM
  have hu0 : (DirectSum.decompose N u d : V) = 0 := by
    clear hx hM
    induction hu using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨e, he, hye⟩ := hy
      rw [DirectSum.decompose_of_mem_ne N hye (by omega)]
    | zero => simp
    | add y z _ _ hy hz => rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add, hy,
        hz, add_zero]
    | smul c y _ hy => rw [DirectSum.decompose_smul, DFinsupp.smul_apply, Submodule.coe_smul, hy,
        smul_zero]
  have hv0 : v ∈ N 0 := by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
    exact Submodule.smul_mem _ c hb
  have h := DirectSum.decompose_of_mem_same N hx
  rw [DirectSum.decompose_add, DirectSum.add_apply, Submodule.coe_add, hu0, zero_add] at h
  rw [← h]
  by_cases h0 : d = 0
  · subst h0
    rw [DirectSum.decompose_of_mem_same N hv0]; exact hv
  · rw [DirectSum.decompose_of_mem_ne N hv0 (Ne.symm h0)]; exact zero_mem _

end Generic


/-! ## Even colours -/

section Even

open Categorification.NilHecke

variable (sy : SKM.Symmetrizer D) (i : I) (hi : D.parity i = 0) (r : ℕ)

/-- Every diagram on `iʳ`, for an even colour `i`, is in the image of the nilHecke ring. -/
theorem cl_mem_range_evenNilHecke (gs : List PG)
    (h : SChain (List.replicate r i) (pl (List.replicate r i) gs) (List.replicate r i)) :
    cl D Sc _ _ gs h ∈ (evenNilHecke D Sc i hi r).range := by
  refine cl_replicate_mem D Sc i r (evenNilHecke D Sc i hi r).range.toSubmonoid ?_ ?_ gs h
  · intro a h
    by_cases ha : a < r
    · exact ⟨⟨mulX ℤ r ⟨a, ha⟩, mulX_mem _⟩,
        (evenNilHecke_mulX D Sc i hi r ⟨a, ha⟩).trans
          ((evenCorner_x D Sc i hi ha).trans (genE_eq D Sc h))⟩
    · rw [cl_eq_one_of_pl_eq_nil D Sc (by
        simp [pl, PG.ld, List.drop_replicate, show r - a = 0 by omega]) h]
      exact (evenNilHecke D Sc i hi r).range.toSubmonoid.one_mem
  · intro a h
    by_cases ha : a + 1 < r
    · exact ⟨⟨dd ℤ r a, dd_mem a⟩,
        (evenNilHecke_dd D Sc i hi r a).trans
          ((evenCorner_ψ D Sc i hi ha).trans (genE_eq D Sc h))⟩
    · rw [cl_eq_one_of_pl_eq_nil D Sc (by
        rcases hr : r - a with _ | _ | m
        · simp [pl, PG.ld, List.drop_replicate, hr]
        · simp [pl, PG.ld, List.drop_replicate, hr]
        · omega) h]
      exact (evenNilHecke D Sc i hi r).range.toSubmonoid.one_mem

/-- `End(iʳ)` is spanned by the image of the nilHecke ring. -/
theorem span_range_evenNilHecke :
    Submodule.span k (Set.range (evenNilHecke D Sc i hi r)) = ⊤ := by
  rw [eq_top_iff, ← span_nf D Sc (List.replicate r i) (List.replicate r i)]
  refine Submodule.span_mono ?_
  rintro _ ⟨n, rfl⟩
  exact cl_mem_range_evenNilHecke D Sc i hi r _ _

theorem evenCornerProjector_mul_mul (T : nilHecke ℤ r) :
    evenCornerProjector D Sc i hi r * evenNilHecke D Sc i hi r T *
        evenCornerProjector D Sc i hi r =
      evenDots D Sc i hi r (ddw (w0Word r) (yDeltaSign r * T.1 1)) *
        evenCornerProjector D Sc i hi r := by
  rw [evenCornerProjector, ← map_mul, ← map_mul, evenDots_apply, ← map_mul]
  exact congrArg _ (Subtype.ext (demIdem_mul_mul_demIdem T.2))

/-- The maps `iʳ → iʳ` of positive degree, spanning. -/
abbrev posSpan (i : I) (r : ℕ) : Submodule k (Corner D Sc i r) :=
  Submodule.span k {y | ∃ e : ℤ, 0 < e ∧
    y ∈ homDegree D sy Sc (List.replicate r i) (List.replicate r i) e}

theorem evenDots_mul_mem (c : MvPolynomial (Fin r) ℤ) :
    evenDots D Sc i hi r c * evenCornerProjector D Sc i hi r ∈
      posSpan D Sc sy i r ⊔ k ∙ evenCornerProjector D Sc i hi r := by
  classical
  have hb := evenNilHecke_demIdem_mem D Sc hi r (gdeg_dot_eq D sy) (gdeg_cross_self_eq D sy)
  rw [c.as_sum, map_sum, Finset.sum_mul]
  refine Submodule.sum_mem _ fun A _ => ?_
  rw [show MvPolynomial.monomial A (c.coeff A) = c.coeff A • MvPolynomial.monomial A 1 by
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one], map_zsmul, smul_mul_assoc]
  refine Submodule.smul_of_tower_mem _ _ ?_
  by_cases hA : A = 0
  · subst hA
    rw [← MvPolynomial.C_apply, MvPolynomial.C_1, map_one, one_mul]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · refine Submodule.mem_sup_left (Submodule.subset_span ?_)
    have hy := evenDots_prod_mem D Sc hi r (gdeg_dot_eq D sy) (fun a => A a) A.support
    rw [MvPolynomial.prod_X_pow_eq_monomial] at hy
    have hyb := mul_mem_cornerDeg D Sc (gdeg D sy) hy hb
    rw [add_zero] at hyb
    refine ⟨_, ?_, hyb⟩
    obtain ⟨a, ha⟩ : ∃ a, a ∈ A.support := by
      by_contra h; push Not at h
      exact hA (Finsupp.support_eq_empty.1 (Finset.eq_empty_of_forall_notMem h))
    have hpos : 0 < ∑ a ∈ A.support, 2 * (A a : ℤ) :=
      lt_of_lt_of_le (by have := Finsupp.mem_support_iff.1 ha; positivity)
        (Finset.single_le_sum (f := fun a => 2 * (A a : ℤ)) (fun _ _ => by positivity) ha)
    rw [smul_eq_mul]
    exact mul_pos hpos (sy.pos i)

/-- **`End(P(i^{(r)}))` in degrees `≤ 0`, even colour.** For a map `g : iʳ → iʳ` of degree
`d ≤ 0`, `1_{i^{(r)}} g 1_{i^{(r)}}` is a multiple of `1_{i^{(r)}}`. -/
theorem evenCornerProjector_mul_mul_mem (hc : Sc.Homogeneous) {d : ℤ} (hd : d ≤ 0)
    {g : Corner D Sc i r}
    (hg : g ∈ homDegree D sy Sc (List.replicate r i) (List.replicate r i) d) :
    evenCornerProjector D Sc i hi r * g * evenCornerProjector D Sc i hi r ∈
      k ∙ evenCornerProjector D Sc i hi r := by
  have hb := evenNilHecke_demIdem_mem D Sc hi r (gdeg_dot_eq D sy) (gdeg_cross_self_eq D sy)
  have hM : evenCornerProjector D Sc i hi r * g * evenCornerProjector D Sc i hi r ∈
      posSpan D Sc sy i r ⊔ k ∙ evenCornerProjector D Sc i hi r := by
    have hg' : g ∈ Submodule.span k (Set.range (evenNilHecke D Sc i hi r)) := by
      rw [span_range_evenNilHecke]; trivial
    clear hg
    induction hg' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨T, rfl⟩ := hy
      rw [evenCornerProjector_mul_mul]
      exact evenDots_mul_mem D Sc sy i hi r _
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add, add_mul]; exact add_mem hy hz
    | smul c y _ hy => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ c hy
  let _ := (isInternal_homDegree D sy Sc hc (List.replicate r i)
    (List.replicate r i)).chooseDecomposition
  refine mem_span_singleton_of_mem_sup (homDegree D sy Sc (List.replicate r i)
    (List.replicate r i)) hb hd ?_ hM
  have := mul_mem_cornerDeg D Sc (gdeg D sy) (mul_mem_cornerDeg D Sc (gdeg D sy) hb hg) hb
  rw [zero_add, add_zero] at this
  exact this

end Even

/-! ## Odd colours -/

section Odd

open OddMath.Frontier NilHeckeAction OddMath.SKM.DividedPowerIdempotents
open DividedPowerModules (oddCornerProjector)

variable (sy : SKM.Symmetrizer D) (i : I) (hi : D.parity i = 1) (n : ℕ)

/-- Every diagram on `i^{n+2}`, for an odd colour `i`, is in the image of the odd nilHecke
ring. -/
theorem cl_mem_range_oddNilHecke (gs : List PG)
    (h : SChain (List.replicate (n + 2) i) (pl (List.replicate (n + 2) i) gs)
      (List.replicate (n + 2) i)) :
    cl D Sc _ _ gs h ∈ (oddNilHecke D Sc i hi n).range := by
  refine cl_replicate_mem D Sc i (n + 2) (oddNilHecke D Sc i hi n).range.toSubmonoid ?_ ?_ gs h
  · intro a h
    by_cases ha : a < n + 2
    · refine ⟨dot n ⟨a, ha⟩, ?_⟩
      show oddCorner D Sc i hi (n + 2)
        (Diagrams.OddNilHecke.toDiagramsOver k n (dot n ⟨a, ha⟩)) = _
      rw [Diagrams.OddNilHecke.toDiagramsOver_dot]
      exact (oddCorner_x D Sc i hi ha).trans (genE_eq D Sc h)
    · rw [cl_eq_one_of_pl_eq_nil D Sc (by
        simp [pl, PG.ld, List.drop_replicate, show n + 2 - a = 0 by omega]) h]
      exact (oddNilHecke D Sc i hi n).range.toSubmonoid.one_mem
  · intro a h
    by_cases ha : a + 1 < n + 2
    · refine ⟨crossing n ⟨a, by omega⟩, ?_⟩
      show oddCorner D Sc i hi (n + 2)
        (Diagrams.OddNilHecke.toDiagramsOver k n (crossing n ⟨a, by omega⟩)) = _
      rw [Diagrams.OddNilHecke.toDiagramsOver_crossing]
      exact (oddCorner_ψ D Sc i hi ha).trans (genE_eq D Sc h)
    · rw [cl_eq_one_of_pl_eq_nil D Sc (by
        rcases hr : n + 2 - a with _ | _ | m
        · simp [pl, PG.ld, List.drop_replicate, hr]
        · simp [pl, PG.ld, List.drop_replicate, hr]
        · omega) h]
      exact (oddNilHecke D Sc i hi n).range.toSubmonoid.one_mem

theorem span_range_oddNilHecke :
    Submodule.span k (Set.range (oddNilHecke D Sc i hi n)) = ⊤ := by
  rw [eq_top_iff, ← span_nf D Sc (List.replicate (n + 2) i) (List.replicate (n + 2) i)]
  refine Submodule.span_mono ?_
  rintro _ ⟨m, rfl⟩
  exact cl_mem_range_oddNilHecke D Sc i hi n _ _

/-- The corner of the reflected projector: `e' T e' = ρ(f) e'` for a polynomial `f` in the
dots, where `ρ` is the reflected opposite. -/
theorem oppositeProjector_mul_mul (T : Presented n) :
    ∃ f : OddMath.SkewPolynomial.SkewPolynomial (n + 2),
      oppositeProjector n * T * oppositeProjector n =
        reflectedOpposite n (OnhPolynomial.polyElem n f) * oppositeProjector n := by
  set T' := OnhReflection.sigma n (NilHeckeRightBasis.reverseLinear n T)
  have hT : reflectedOpposite n T' = T := by
    simp only [reflectedOpposite, T', OnhReflection.sigma_apply]
    rw [OnhReflection.sigmaHom_involutive n, NilHeckeRightBasis.reverse_involutive n]
  refine ⟨OnhStructure.cornerPre T', ?_⟩
  have e := OnhStructure.thick_cornerPre T'
  rw [OnhStructure.thick, ThickDots.projector_poly_projector_eq _
    (OnhStructure.cornerPre_mem T')] at e
  rw [← hT, oppositeProjector]
  calc reflectedOpposite n (ZeroHecke.projector n) * reflectedOpposite n T' *
        reflectedOpposite n (ZeroHecke.projector n)
      = reflectedOpposite n (ZeroHecke.projector n * T' * ZeroHecke.projector n) := by
        rw [reflectedOpposite_mul, reflectedOpposite_mul, mul_assoc]
    _ = reflectedOpposite n (ZeroHecke.projector n *
          OnhPolynomial.polyElem n (OnhStructure.cornerPre T')) := by rw [e]
    _ = _ := reflectedOpposite_mul _ _

theorem reflectedOpposite_add (x y : Presented n) :
    reflectedOpposite n (x + y) = reflectedOpposite n x + reflectedOpposite n y := by
  simp [reflectedOpposite]

theorem reflectedOpposite_zsmul (c : ℤ) (x : Presented n) :
    reflectedOpposite n (c • x) = c • reflectedOpposite n x := by
  simp only [reflectedOpposite, map_zsmul]

theorem oddPoly_mul_mem (f : OddMath.SkewPolynomial.SkewPolynomial (n + 2)) :
    oddNilHecke D Sc i hi n
        (reflectedOpposite n (OnhPolynomial.polyElem n f) * oppositeProjector n) ∈
      posSpan D Sc sy i (n + 2) ⊔ k ∙ oddCornerProjector D Sc i hi (n + 2) := by
  have hb := oddNilHecke_mem_integerDegree D Sc sy i hi (oppositeProjector_degree n)
  rw [mul_zero] at hb
  induction f using Finsupp.induction_linear with
  | zero => simp [reflectedOpposite]
  | add f g hf hg =>
    rw [map_add, reflectedOpposite_add, add_mul, map_add]; exact add_mem hf hg
  | single A c =>
    rw [← Finsupp.smul_single_one, map_zsmul, reflectedOpposite_zsmul, smul_mul_assoc,
      map_zsmul]
    refine zsmul_mem ?_ c
    by_cases hA : A = 0
    · subst hA
      rw [show (Finsupp.single (0 : Fin (n + 2) → ℕ) (1 : ℤ)) = 1 from rfl, map_one,
        reflectedOpposite_one, one_mul]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    · refine Submodule.mem_sup_left (Submodule.subset_span ?_)
      have hp := OnhPolynomial.polyElem_monomial (n := n) A
      simp only [OddMath.SkewPolynomial.monomial] at hp
      rw [hp, map_mul]
      have hy := oddNilHecke_mem_integerDegree D Sc sy i hi
        (OddMath.SKM.DividedPowerDecomposition.reflectedOpposite_degree
          (EQOnhDG.degreePiece_le_grading _ (NilHeckeGrading.dotMonomial_mem A)))
      have hyb := mul_mem_cornerDeg D Sc (gdeg D sy) hy hb
      rw [add_zero] at hyb
      refine ⟨_, ?_, hyb⟩
      obtain ⟨a, ha⟩ : ∃ a, A a ≠ 0 := by
        by_contra h
        exact hA (funext fun a => not_not.1 fun h' => h ⟨a, h'⟩)
      have hpos : (0 : ℤ) < ((∑ j, A j : ℕ) : ℤ) := by
        have := Finset.single_le_sum (f := A) (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)
        omega
      exact mul_pos (mul_pos (by norm_num) (sy.pos i)) hpos

/-- **`End(P(i^{(n+2)}))` in degrees `≤ 0`, odd colour.** -/
theorem oddCornerProjector_succ_succ_mul_mul_mem (hc : Sc.Homogeneous) {d : ℤ} (hd : d ≤ 0)
    {g : Corner D Sc i (n + 2)}
    (hg : g ∈ homDegree D sy Sc (List.replicate (n + 2) i) (List.replicate (n + 2) i) d) :
    oddCornerProjector D Sc i hi (n + 2) * g * oddCornerProjector D Sc i hi (n + 2) ∈
      k ∙ oddCornerProjector D Sc i hi (n + 2) := by
  have hb := oddNilHecke_mem_integerDegree D Sc sy i hi (oppositeProjector_degree n)
  rw [mul_zero] at hb
  have hM : oddCornerProjector D Sc i hi (n + 2) * g * oddCornerProjector D Sc i hi (n + 2) ∈
      posSpan D Sc sy i (n + 2) ⊔ k ∙ oddCornerProjector D Sc i hi (n + 2) := by
    have hg' : g ∈ Submodule.span k (Set.range (oddNilHecke D Sc i hi n)) := by
      rw [span_range_oddNilHecke]; trivial
    clear hg
    induction hg' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨T, rfl⟩ := hy
      obtain ⟨f, hf⟩ := oppositeProjector_mul_mul n T
      change oddNilHecke D Sc i hi n _ * _ * oddNilHecke D Sc i hi n _ ∈ _
      rw [← map_mul, ← map_mul, hf]
      exact oddPoly_mul_mem D Sc sy i hi n f
    | zero => simp
    | add y z _ _ hy hz => rw [mul_add, add_mul]; exact add_mem hy hz
    | smul c y _ hy => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ c hy
  let _ := (isInternal_homDegree D sy Sc hc (List.replicate (n + 2) i)
    (List.replicate (n + 2) i)).chooseDecomposition
  refine mem_span_singleton_of_mem_sup (homDegree D sy Sc (List.replicate (n + 2) i)
    (List.replicate (n + 2) i)) hb hd ?_ hM
  have := mul_mem_cornerDeg D Sc (gdeg D sy) (mul_mem_cornerDeg D Sc (gdeg D sy) hb hg) hb
  rw [zero_add, add_zero] at this
  exact this

end Odd

/-! ## Words of length at most one -/

section Small

variable (sy : SKM.Symmetrizer D) (i : I) (r : ℕ)

/-- The maps `iʳ → iʳ` equal to `1` or of positive degree. -/
def onePosSubmonoid : Submonoid (Corner D Sc i r) where
  carrier := {y | y = 1 ∨ ∃ e : ℤ, 0 < e ∧
    y ∈ homDegree D sy Sc (List.replicate r i) (List.replicate r i) e}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro y z (rfl | ⟨e, he, hy⟩) (rfl | ⟨e', he', hz⟩)
    · exact Or.inl (one_mul _)
    · rw [one_mul]; exact Or.inr ⟨e', he', hz⟩
    · rw [mul_one]; exact Or.inr ⟨e, he, hy⟩
    · exact Or.inr ⟨e + e', by omega, mul_mem_cornerDeg D Sc (gdeg D sy) hy hz⟩

/-- For `r ≤ 1`, a map `iʳ → iʳ` of degree `d ≤ 0` is a multiple of the identity. -/
theorem corner_mem_span_one (hc : Sc.Homogeneous) (hr : r ≤ 1) {d : ℤ} (hd : d ≤ 0)
    {g : Corner D Sc i r}
    (hg : g ∈ homDegree D sy Sc (List.replicate r i) (List.replicate r i) d) :
    g ∈ k ∙ (1 : Corner D Sc i r) := by
  have hS : ∀ y ∈ onePosSubmonoid D Sc sy i r, y ∈ posSpan D Sc sy i r ⊔ k ∙ 1 := by
    rintro y (rfl | hy)
    · exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
    · exact Submodule.mem_sup_left (Submodule.subset_span hy)
  have hM : g ∈ posSpan D Sc sy i r ⊔ k ∙ 1 := by
    have hg' : g ∈ Submodule.span k (Set.range fun m : NFIdx (List.replicate r i)
        (List.replicate r i) => m.nf (D := D) (Sc := Sc)) := by
      rw [span_nf]; trivial
    refine Submodule.span_le.2 ?_ hg'
    rintro _ ⟨m, rfl⟩
    refine hS _ (cl_replicate_mem D Sc i r _ ?_ ?_ _ _)
    · intro a h
      by_cases ha : a < r
      · obtain rfl : r = 1 := by omega
        obtain rfl : a = 0 := by omega
        refine Or.inr ⟨2 * sy.d i, mul_pos (by norm_num) (sy.pos i), ?_⟩
        have := Presentation.diag_mem_homDeg' (P := pres D Sc) (degree_gdeg_mkD D sy _ h)
        simpa [cl, pl, PG.ld, layList, lay, gdeg] using this
      · rw [cl_eq_one_of_pl_eq_nil D Sc (by
          simp [pl, PG.ld, List.drop_replicate, show r - a = 0 by omega]) h]
        exact Or.inl rfl
    · intro a h
      rw [cl_eq_one_of_pl_eq_nil D Sc (by
        rcases hr' : r - a with _ | _ | m
        · simp [pl, PG.ld, List.drop_replicate, hr']
        · simp [pl, PG.ld, List.drop_replicate, hr']
        · omega) h]
      exact Or.inl rfl
  let _ := (isInternal_homDegree D sy Sc hc (List.replicate r i)
    (List.replicate r i)).chooseDecomposition
  exact mem_span_singleton_of_mem_sup (homDegree D sy Sc (List.replicate r i)
    (List.replicate r i)) (one_mem_cornerDeg D Sc (gdeg D sy) i r) hd hg hM

end Small

section OddAll

open DividedPowerModules (oddCornerProjector)

variable (sy : SKM.Symmetrizer D) (i : I) (hi : D.parity i = 1)

/-- **`End(P(i^{(r)}))` in degrees `≤ 0`, odd colour.** For a map `g : iʳ → iʳ` of degree
`d ≤ 0`, `1_{i^{(r)}} g 1_{i^{(r)}}` is a multiple of `1_{i^{(r)}}`. -/
theorem oddCornerProjector_mul_mul_mem (hc : Sc.Homogeneous) (r : ℕ) {d : ℤ} (hd : d ≤ 0)
    {g : Corner D Sc i r}
    (hg : g ∈ homDegree D sy Sc (List.replicate r i) (List.replicate r i) d) :
    oddCornerProjector D Sc i hi r * g * oddCornerProjector D Sc i hi r ∈
      k ∙ oddCornerProjector D Sc i hi r :=
  match r with
  | 0 => by
    simp only [DividedPowerModules.oddCornerProjector, one_mul, mul_one]
    exact corner_mem_span_one D Sc sy i 0 hc (by omega) hd hg
  | 1 => by
    simp only [DividedPowerModules.oddCornerProjector, one_mul, mul_one]
    exact corner_mem_span_one D Sc sy i 1 hc le_rfl hd hg
  | n + 2 => oddCornerProjector_succ_succ_mul_mul_mem D Sc sy i hi n hc hd hg

end OddAll

end OddMath.QuiverHecke
