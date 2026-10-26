/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import OddMath.QuiverHecke.CyclotomicAction.IntertwinerWords
import OddMath.QuiverHecke.MixedRelations

/-!
# Crossings through the moving-strand map

Ports the crossing part of `Categorification/KLR/Intertwiner.lean` (`ψ_mul_gInt_mul_gInt`,
Kang–Kashiwara arXiv:1102.4677v4, Lemma 4.12, second identity) to the quiver Hecke
supercategory, following Kang–Kashiwara–Oh, arXiv:1206.5933v2, Lemma 8.3 ((8.12) and the braid
identity) and the first identity of (8.13) for the crossings of `R(β)`. The downstream
consumer is the balance of the map `Q` of KKO Proposition 8.4 over the old crossings
(`Q_balanced` of the action plan) and the product `QP` of Theorem 8.5.

## Main results

* `variants_comp_of`: a morphism that intertwines the two dots and the crossing of two
  same-colour strands, up to a common sign, intertwines the variants `g` with that sign.
* `cross_left_comp_intertwinerHom`, `cross_right_comp_intertwinerHom`: a crossing away from the
  pair passes through `g` with the sign `(-1)^{p(ν_c)p(ν_{c+1})p(ν_a)p(ν_{a+1})}` (KKO (8.12)).
* `cross_left_comp_moveHom`: a crossing to the left of the moving strand passes through
  `g_n ⋯ g_1` with the sign `(-1)^{p(x)p(y)p(i)p(ν)}`.
* `meetLeft`, `meetRight`: the two sides of `τ_{a+1} g_a g_{a+1} = g_a g_{a+1} τ_a` on
  `i, j, c`; `meetLeft_eq_of_ne` (both `j, c` differ from `i`: the braid relation (1.9)) and
  `meetLeft_eq_self` (`i = j = c`: `braid_element`, `braid_gEven`), `meetLeft_eq_of_eq_ne`
  (`i = j ≠ c`: the exact braid relation on `i, i, c` and the dot slides intertwine the
  variants, `meet_core_eq_ne`), combined in `meetLeft_eq` (all cases except `c = i ≠ j`).
* `cross_comp_moveHom`: the first identity of KKO (8.13) for an old crossing `ψ` of `j, c` in
  `ν`: `ψ g_n ⋯ g_1 = (-1)^{p(j)p(c)p(i)p(ν)} g_n ⋯ g_1 ψ`, given the three-strand identity
  for `i, j, c`.

* `cross_comp_moveHom_of`: the same, unconditionally unless `c = i ≠ j`.

The three-strand identity for `c = i ≠ j`, where the correction term of `braid_iji` cancels
against the quadratic relation `cross_cross_ne`, is `IntertwinerMeet`.
-/

noncomputable section
namespace OddMath.QuiverHecke
open CategoryTheory StringDiagrams SignedNilHecke
open SKM (zsign)
open scoped Classical

variable {I : Type*} {X : Type*} [AddCommGroup X] (D : SKM.Datum I X) {k : Type*} [CommRing k]
  (Sc : SKM.Scalars D k)

/-- A morphism intertwining `u`, `v`, `T` with `u'`, `v'`, `T'` up to a common sign
intertwines both same-colour variants with that sign. -/
theorem variants_comp_of {t t' : List I}
    (f : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t'))
    {u v T : End ((pres D Sc).obj (ob D t))} {u' v' T' : End ((pres D Sc).obj (ob D t'))}
    (q : ZMod 2) (hu : u ≫ f = zsign k q • (f ≫ u')) (hv : v ≫ f = zsign k q • (f ≫ v'))
    (ht : T ≫ f = zsign k q • (f ≫ T')) :
    (OddNilHecke.Intertwiner.element u v T : End ((pres D Sc).obj (ob D t))) ≫ f =
        zsign k q • (f ≫ (OddNilHecke.Intertwiner.element u' v' T' :
          End ((pres D Sc).obj (ob D t')))) ∧
      (gEven u v T : End ((pres D Sc).obj (ob D t))) ≫ f =
        zsign k q • (f ≫ (gEven u' v' T' : End ((pres D Sc).obj (ob D t')))) := by
  have s₁ : ∀ (x y : End ((pres D Sc).obj (ob D t))) (g : End ((pres D Sc).obj (ob D t))),
      (x - y) ≫ g = x ≫ g - y ≫ g := fun x y g => Preadditive.sub_comp x y g
  have s₂ : ∀ (x y : End ((pres D Sc).obj (ob D t))) (g : (pres D Sc).obj (ob D t) ⟶
      (pres D Sc).obj (ob D t')), (x - y) ≫ g = x ≫ g - y ≫ g := fun x y g =>
    Preadditive.sub_comp x y g
  have s₃ : ∀ (g : End ((pres D Sc).obj (ob D t))) (x y : End ((pres D Sc).obj (ob D t))),
      g ≫ (x - y) = g ≫ x - g ≫ y := fun g x y => Preadditive.comp_sub g x y
  have s₄ : ∀ (g : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t'))
      (x y : End ((pres D Sc).obj (ob D t'))), g ≫ (x - y) = g ≫ x - g ≫ y := fun g x y =>
    Preadditive.comp_sub g x y
  have a₁ : ∀ (x y : End ((pres D Sc).obj (ob D t))) (g : End ((pres D Sc).obj (ob D t))),
      (x + y) ≫ g = x ≫ g + y ≫ g := fun x y g => Preadditive.add_comp _ _ _ x y g
  have a₂ : ∀ (x y : End ((pres D Sc).obj (ob D t))) (g : (pres D Sc).obj (ob D t) ⟶
      (pres D Sc).obj (ob D t')), (x + y) ≫ g = x ≫ g + y ≫ g := fun x y g =>
    Preadditive.add_comp _ _ _ x y g
  have a₃ : ∀ (g : End ((pres D Sc).obj (ob D t))) (x y : End ((pres D Sc).obj (ob D t))),
      g ≫ (x + y) = g ≫ x + g ≫ y := fun g x y => Preadditive.comp_add _ _ _ g x y
  have a₄ : ∀ (g : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t'))
      (x y : End ((pres D Sc).obj (ob D t'))), g ≫ (x + y) = g ≫ x + g ≫ y := fun g x y =>
    Preadditive.comp_add _ _ _ g x y
  have s₅ : ∀ x y g : End ((pres D Sc).obj (ob D t')), (x - y) ≫ g = x ≫ g - y ≫ g :=
    fun x y g => Preadditive.sub_comp x y g
  have s₆ : ∀ g x y : End ((pres D Sc).obj (ob D t')), g ≫ (x - y) = g ≫ x - g ≫ y :=
    fun g x y => Preadditive.comp_sub g x y
  have a₅ : ∀ x y g : End ((pres D Sc).obj (ob D t')), (x + y) ≫ g = x ≫ g + y ≫ g :=
    fun x y g => Preadditive.add_comp _ _ _ x y g
  have a₆ : ∀ g x y : End ((pres D Sc).obj (ob D t')), g ≫ (x + y) = g ≫ x + g ≫ y :=
    fun g x y => Preadditive.comp_add _ _ _ g x y
  have hz : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  rcases hz q with rfl | rfl
  · rw [show zsign k (0 : ZMod 2) = 1 by simp [zsign], one_smul] at hu hv ht
    rw [show zsign k (0 : ZMod 2) = 1 by simp [zsign], one_smul, one_smul]
    have hu' : ∀ r : End ((pres D Sc).obj (ob D t')), u ≫ f ≫ r = f ≫ u' ≫ r := fun r => by
      rw [← Category.assoc, hu, Category.assoc]
    have hv' : ∀ r : End ((pres D Sc).obj (ob D t')), v ≫ f ≫ r = f ≫ v' ≫ r := fun r => by
      rw [← Category.assoc, hv, Category.assoc]
    have ht' : ∀ r : End ((pres D Sc).obj (ob D t')), T ≫ f ≫ r = f ≫ T' ≫ r := fun r => by
      rw [← Category.assoc, ht, Category.assoc]
    constructor
    · simp only [OddNilHecke.Intertwiner.element, OddNilHecke.Intertwiner.squareDiff, pow_two,
        End.mul_def, s₁, s₂, s₃, s₄, s₅, s₆,
        Category.assoc, hu, hv, hu', hv', ht']
    · simp only [gEven, phiEven, End.mul_def, End.one_def, s₁, s₂, s₃, s₄, s₅, s₆, a₁, a₂, a₄, a₅,
        
        Category.assoc, Category.id_comp, hu, hv, hu', hv', ht']
  · rw [show zsign k (1 : ZMod 2) = -1 by simp [zsign], neg_one_smul] at hu hv ht
    rw [show zsign k (1 : ZMod 2) = -1 by simp [zsign], neg_one_smul, neg_one_smul]
    have hu' : ∀ r : End ((pres D Sc).obj (ob D t')), u ≫ f ≫ r = -(f ≫ u' ≫ r) := fun r => by
      rw [← Category.assoc, hu, Preadditive.neg_comp, Category.assoc]
    have hv' : ∀ r : End ((pres D Sc).obj (ob D t')), v ≫ f ≫ r = -(f ≫ v' ≫ r) := fun r => by
      rw [← Category.assoc, hv, Preadditive.neg_comp, Category.assoc]
    have ht' : ∀ r : End ((pres D Sc).obj (ob D t')), T ≫ f ≫ r = -(f ≫ T' ≫ r) := fun r => by
      rw [← Category.assoc, ht, Preadditive.neg_comp, Category.assoc]
    constructor
    · simp only [OddNilHecke.Intertwiner.element, OddNilHecke.Intertwiner.squareDiff, pow_two,
        End.mul_def, s₁, s₂, s₃, s₄, s₅, s₆,
        Preadditive.comp_neg, neg_neg, Category.assoc, hu, hv, hu',
        hv', ht']
      abel
    · simp only [gEven, phiEven, End.mul_def, End.one_def, s₁, s₂, s₃, s₄, s₅, s₆, a₁, a₂, a₄, a₅,
        
        Preadditive.comp_neg, neg_neg, Category.assoc, Category.id_comp,
        hu, hv, hu', hv', ht']
      abel

theorem cl_interchange_gen {t t' : List I} (l m v : List I) (g h : Shape I)
    (ht : t = l ++ g.dom ++ m ++ h.dom ++ v) (ht' : t' = l ++ g.cod ++ m ++ h.cod ++ v)
    {p₁ p₂ q₁ q₂ : ℕ} (hp₁ : l.length = p₁) (hp₂ : l.length = p₂)
    (hq₁ : (l ++ g.dom ++ m).length = q₁) (hq₂ : (l ++ g.dom ++ m).length = q₂)
    (h₁ : SChain t (pl t [PG.ofShape g p₁, PG.ofShape h q₁]) t')
    (h₂ : SChain t (pl t [PG.ofShape h q₂, PG.ofShape g p₂]) t') :
    cl D Sc t t' [PG.ofShape g p₁, PG.ofShape h q₁] h₁ =
      zsign k (g.parity D * h.parity D) • cl D Sc t t' [PG.ofShape h q₂, PG.ofShape g p₂] h₂ := by
  subst ht ht' hp₁ hp₂ hq₁ hq₂
  exact cl_interchange D Sc l m v g h h₁ h₂

theorem crossE_eq_cl {w : List I} {a : ℕ} (h : SChain w (pl w [.cross a]) w) :
    crossE D Sc w a = cl D Sc w w [.cross a] h :=
  genE_eq D Sc h

/-- Turning an interchange `c ≫ y' = σ • (y ≫ c)` around. -/
theorem comp_eq_zsign_of {t t' : List I} {c : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')}
    {y : End ((pres D Sc).obj (ob D t))} {y' : End ((pres D Sc).obj (ob D t'))} {q : ZMod 2}
    (h : c ≫ y' = zsign k q • (y ≫ c)) : y ≫ c = zsign k q • (c ≫ y') := by
  rw [h, smul_smul, zsign_mul_self, one_smul]

theorem zsign_swap {t t' : List I} {c : (pres D Sc).obj (ob D t) ⟶ (pres D Sc).obj (ob D t')}
    {y : End ((pres D Sc).obj (ob D t))} {y' : End ((pres D Sc).obj (ob D t'))} {q : ZMod 2}
    (h : y ≫ c = zsign k q • (c ≫ y')) : c ≫ y' = zsign k q • (y ≫ c) := by
  rw [h, smul_smul, zsign_mul_self, one_smul]

/-- KKO (8.12) for a crossing to the left of the pair: it passes through `g` with the sign
`(-1)^{p(x)p(y)p(i)p(j)}`. -/
theorem cross_left_comp_intertwinerHom (l₁ l₂ r : List I) (x y i j : I) :
    cl D Sc (l₁ ++ [x, y] ++ l₂ ++ [i, j] ++ r) (l₁ ++ [y, x] ++ l₂ ++ [i, j] ++ r)
        [.cross l₁.length] (sChain_ofShape' l₁ (l₂ ++ [i, j] ++ r) (.cross x y)
          (by simp [Shape.dom]) (by simp [Shape.cod]) rfl) ≫
        intertwinerHom D Sc (l₁ ++ [y, x] ++ l₂) r i j =
      zsign k (D.parity x * D.parity y * (D.parity i * D.parity j)) •
        (intertwinerHom D Sc (l₁ ++ [x, y] ++ l₂) r i j ≫
          cl D Sc (l₁ ++ [x, y] ++ l₂ ++ [j, i] ++ r) (l₁ ++ [y, x] ++ l₂ ++ [j, i] ++ r)
            [.cross l₁.length] (sChain_ofShape' l₁ (l₂ ++ [j, i] ++ r) (.cross x y)
              (by simp [Shape.dom]) (by simp [Shape.cod]) rfl)) := by
  by_cases h : i = j
  · subst h
    rw [intertwinerHom_self, intertwinerHom_self]
    have hu : cl D Sc (l₁ ++ [x, y] ++ l₂ ++ [i, i] ++ r) (l₁ ++ [y, x] ++ l₂ ++ [i, i] ++ r)
        [.cross l₁.length] (sChain_ofShape' l₁ (l₂ ++ [i, i] ++ r) (.cross x y)
          (by simp [Shape.dom]) (by simp [Shape.cod]) rfl) ≫
          dotE D Sc (l₁ ++ [y, x] ++ l₂ ++ [i, i] ++ r) (l₁ ++ [y, x] ++ l₂).length =
        zsign k (D.parity x * D.parity y * D.parity i) •
          (dotE D Sc (l₁ ++ [x, y] ++ l₂ ++ [i, i] ++ r) (l₁ ++ [x, y] ++ l₂).length ≫
            cl D Sc (l₁ ++ [x, y] ++ l₂ ++ [i, i] ++ r) (l₁ ++ [y, x] ++ l₂ ++ [i, i] ++ r)
              [.cross l₁.length] (sChain_ofShape' l₁ (l₂ ++ [i, i] ++ r) (.cross x y)
                (by simp [Shape.dom]) (by simp [Shape.cod]) rfl)) := by
      rw [dotE_eq_cl D Sc (sChain_dotAny _ _), dotE_eq_cl D Sc (sChain_dotAny _ _), cl_comp,
        cl_comp]
      exact cl_interchange_gen D Sc l₁ l₂ ([i] ++ r) (.cross x y) (.dot i)
        (by simp [Shape.dom]) (by simp [Shape.cod]) rfl rfl (by simp [Shape.dom]) rfl _ _
    have hv : cl D Sc (l₁ ++ [x, y] ++ l₂ ++ [i, i] ++ r) (l₁ ++ [y, x] ++ l₂ ++ [i, i] ++ r)
        [.cross l₁.length] (sChain_ofShape' l₁ (l₂ ++ [i, i] ++ r) (.cross x y)
          (by simp [Shape.dom]) (by simp [Shape.cod]) rfl) ≫
          dotE D Sc (l₁ ++ [y, x] ++ l₂ ++ [i, i] ++ r) ((l₁ ++ [y, x] ++ l₂).length + 1) =
        zsign k (D.parity x * D.parity y * D.parity i) •
          (dotE D Sc (l₁ ++ [x, y] ++ l₂ ++ [i, i] ++ r) ((l₁ ++ [x, y] ++ l₂).length + 1) ≫
            cl D Sc (l₁ ++ [x, y] ++ l₂ ++ [i, i] ++ r) (l₁ ++ [y, x] ++ l₂ ++ [i, i] ++ r)
              [.cross l₁.length] (sChain_ofShape' l₁ (l₂ ++ [i, i] ++ r) (.cross x y)
                (by simp [Shape.dom]) (by simp [Shape.cod]) rfl)) := by
      rw [dotE_eq_cl D Sc (sChain_dotAny _ _), dotE_eq_cl D Sc (sChain_dotAny _ _), cl_comp,
        cl_comp]
      exact cl_interchange_gen D Sc l₁ (l₂ ++ [i]) r (.cross x y) (.dot i)
        (by simp [Shape.dom]) (by simp [Shape.cod]) rfl rfl
        (by simp only [Shape.dom, List.length_append, List.length_cons, List.length_nil]; omega)
        (by simp only [Shape.dom, List.length_append, List.length_cons, List.length_nil]; omega) _ _
    have hT : cl D Sc (l₁ ++ [x, y] ++ l₂ ++ [i, i] ++ r) (l₁ ++ [y, x] ++ l₂ ++ [i, i] ++ r)
        [.cross l₁.length] (sChain_ofShape' l₁ (l₂ ++ [i, i] ++ r) (.cross x y)
          (by simp [Shape.dom]) (by simp [Shape.cod]) rfl) ≫
          crossE D Sc (l₁ ++ [y, x] ++ l₂ ++ [i, i] ++ r) (l₁ ++ [y, x] ++ l₂).length =
        zsign k (D.parity x * D.parity y * D.parity i) •
          (crossE D Sc (l₁ ++ [x, y] ++ l₂ ++ [i, i] ++ r) (l₁ ++ [x, y] ++ l₂).length ≫
            cl D Sc (l₁ ++ [x, y] ++ l₂ ++ [i, i] ++ r) (l₁ ++ [y, x] ++ l₂ ++ [i, i] ++ r)
              [.cross l₁.length] (sChain_ofShape' l₁ (l₂ ++ [i, i] ++ r) (.cross x y)
                (by simp [Shape.dom]) (by simp [Shape.cod]) rfl)) := by
      rw [crossE_eq_cl D Sc (sChain_ofShape' (l₁ ++ [y, x] ++ l₂) r (.cross i i)
          (t := l₁ ++ [y, x] ++ l₂ ++ [i, i] ++ r) (t' := l₁ ++ [y, x] ++ l₂ ++ [i, i] ++ r)
          rfl rfl rfl),
        crossE_eq_cl D Sc (sChain_ofShape' (l₁ ++ [x, y] ++ l₂) r (.cross i i)
          (t := l₁ ++ [x, y] ++ l₂ ++ [i, i] ++ r) (t' := l₁ ++ [x, y] ++ l₂ ++ [i, i] ++ r)
          rfl rfl rfl),
        cl_comp, cl_comp, ← parity_sq (D.parity i)]
      exact cl_interchange_gen D Sc l₁ l₂ r (.cross x y) (.cross i i)
        (by simp [Shape.dom]) (by simp [Shape.cod]) rfl rfl (by simp [Shape.dom]) rfl _ _
    have hS := variants_comp_of D Sc _ _ (comp_eq_zsign_of D Sc hu) (comp_eq_zsign_of D Sc hv)
      (comp_eq_zsign_of D Sc hT)
    rw [parity_sq]
    unfold sameIntertwiner
    split_ifs
    · exact zsign_swap D Sc hS.1
    · exact zsign_swap D Sc hS.2
  · rw [intertwinerHom_of_ne D Sc _ r h, intertwinerHom_of_ne D Sc _ r h, cl_comp, cl_comp]
    exact cl_interchange_gen D Sc l₁ l₂ r (.cross x y) (.cross i j) (by simp [Shape.dom])
      (by simp [Shape.cod]) rfl rfl
      (by simp only [Shape.dom, List.length_append, List.length_cons, List.length_nil])
      (by simp only [Shape.dom, List.length_append, List.length_cons, List.length_nil])
      _ _

theorem eq_zsign_smul_symm {M : Type*} [AddCommGroup M] [Module k M] {a b : M} {q : ZMod 2}
    (h : a = zsign k q • b) : b = zsign k q • a := by
  rw [h, smul_smul, zsign_mul_self, one_smul]

/-- KKO (8.12) for a crossing to the right of the pair: it passes through `g` with the sign
`(-1)^{p(i)p(j)p(x)p(y)}`. -/
theorem cross_right_comp_intertwinerHom (l m v : List I) (x y i j : I) :
    cl D Sc (l ++ [i, j] ++ (m ++ x :: y :: v)) (l ++ [i, j] ++ (m ++ y :: x :: v))
        [.cross (l ++ [i, j] ++ m).length] (sChain_ofShape' (l ++ [i, j] ++ m) v (.cross x y)
          (by simp [Shape.dom]) (by simp [Shape.cod]) rfl) ≫
        intertwinerHom D Sc l (m ++ y :: x :: v) i j =
      zsign k (D.parity i * D.parity j * (D.parity x * D.parity y)) •
        (intertwinerHom D Sc l (m ++ x :: y :: v) i j ≫
          cl D Sc (l ++ [j, i] ++ (m ++ x :: y :: v)) (l ++ [j, i] ++ (m ++ y :: x :: v))
            [.cross (l ++ [j, i] ++ m).length] (sChain_ofShape' (l ++ [j, i] ++ m) v
              (.cross x y) (by simp [Shape.dom]) (by simp [Shape.cod]) rfl)) := by
  by_cases h : i = j
  · subst h
    have hu := eq_zsign_smul_symm (k := k) (q := D.parity i * (D.parity x * D.parity y))
      (a := dotE D Sc (l ++ [i, i] ++ (m ++ x :: y :: v)) l.length ≫
        cl D Sc (l ++ [i, i] ++ (m ++ x :: y :: v)) (l ++ [i, i] ++ (m ++ y :: x :: v))
          [.cross (l ++ [i, i] ++ m).length] (sChain_ofShape' (l ++ [i, i] ++ m) v (.cross x y)
            (by simp [Shape.dom]) (by simp [Shape.cod]) rfl))
      (b := cl D Sc (l ++ [i, i] ++ (m ++ x :: y :: v)) (l ++ [i, i] ++ (m ++ y :: x :: v))
          [.cross (l ++ [i, i] ++ m).length] (sChain_ofShape' (l ++ [i, i] ++ m) v (.cross x y)
            (by simp [Shape.dom]) (by simp [Shape.cod]) rfl) ≫
        dotE D Sc (l ++ [i, i] ++ (m ++ y :: x :: v)) l.length) (by
      rw [dotE_eq_cl D Sc (sChain_dotAny _ _), dotE_eq_cl D Sc (sChain_dotAny _ _), cl_comp,
        cl_comp]
      exact cl_interchange_gen D Sc l ([i] ++ m) v (.dot i) (.cross x y)
        (by simp [Shape.dom]) (by simp [Shape.cod]) rfl rfl (by simp [Shape.dom])
        (by simp [Shape.dom]) _ _)
    have hv := eq_zsign_smul_symm (k := k) (q := D.parity i * (D.parity x * D.parity y))
      (a := dotE D Sc (l ++ [i, i] ++ (m ++ x :: y :: v)) (l.length + 1) ≫
        cl D Sc (l ++ [i, i] ++ (m ++ x :: y :: v)) (l ++ [i, i] ++ (m ++ y :: x :: v))
          [.cross (l ++ [i, i] ++ m).length] (sChain_ofShape' (l ++ [i, i] ++ m) v (.cross x y)
            (by simp [Shape.dom]) (by simp [Shape.cod]) rfl))
      (b := cl D Sc (l ++ [i, i] ++ (m ++ x :: y :: v)) (l ++ [i, i] ++ (m ++ y :: x :: v))
          [.cross (l ++ [i, i] ++ m).length] (sChain_ofShape' (l ++ [i, i] ++ m) v (.cross x y)
            (by simp [Shape.dom]) (by simp [Shape.cod]) rfl) ≫
        dotE D Sc (l ++ [i, i] ++ (m ++ y :: x :: v)) (l.length + 1)) (by
      rw [dotE_eq_cl D Sc (sChain_dotAny _ _), dotE_eq_cl D Sc (sChain_dotAny _ _), cl_comp,
        cl_comp]
      exact cl_interchange_gen D Sc (l ++ [i]) m v (.dot i) (.cross x y)
        (by simp [Shape.dom]) (by simp [Shape.cod]) (by simp) (by simp)
        (by simp only [Shape.dom, List.length_append, List.length_cons, List.length_nil])
        (by simp only [Shape.dom, List.length_append, List.length_cons, List.length_nil])
        _ _)
    have hT := eq_zsign_smul_symm (k := k) (q := D.parity i * (D.parity x * D.parity y))
      (a := crossE D Sc (l ++ [i, i] ++ (m ++ x :: y :: v)) l.length ≫
        cl D Sc (l ++ [i, i] ++ (m ++ x :: y :: v)) (l ++ [i, i] ++ (m ++ y :: x :: v))
          [.cross (l ++ [i, i] ++ m).length] (sChain_ofShape' (l ++ [i, i] ++ m) v (.cross x y)
            (by simp [Shape.dom]) (by simp [Shape.cod]) rfl))
      (b := cl D Sc (l ++ [i, i] ++ (m ++ x :: y :: v)) (l ++ [i, i] ++ (m ++ y :: x :: v))
          [.cross (l ++ [i, i] ++ m).length] (sChain_ofShape' (l ++ [i, i] ++ m) v (.cross x y)
            (by simp [Shape.dom]) (by simp [Shape.cod]) rfl) ≫
        crossE D Sc (l ++ [i, i] ++ (m ++ y :: x :: v)) l.length) (by
      rw [crossE_eq_cl D Sc (sChain_crossAt l (m ++ x :: y :: v) i i),
        crossE_eq_cl D Sc (sChain_crossAt l (m ++ y :: x :: v) i i), cl_comp, cl_comp,
        ← parity_sq (D.parity i)]
      exact cl_interchange_gen D Sc l m v (.cross i i) (.cross x y)
        (by simp [Shape.dom]) (by simp [Shape.cod]) rfl rfl (by simp [Shape.dom])
        (by simp [Shape.dom]) _ _)
    have hS := variants_comp_of D Sc _ _ (comp_eq_zsign_of D Sc hu) (comp_eq_zsign_of D Sc hv)
      (comp_eq_zsign_of D Sc hT)
    rw [intertwinerHom_self, intertwinerHom_self, parity_sq]
    unfold sameIntertwiner
    split_ifs
    · exact zsign_swap D Sc hS.1
    · exact zsign_swap D Sc hS.2
  · rw [intertwinerHom_of_ne D Sc l _ h, intertwinerHom_of_ne D Sc l _ h, cl_comp, cl_comp]
    exact eq_zsign_smul_symm (cl_interchange_gen D Sc l m v (.cross i j) (.cross x y)
      (by simp [Shape.dom]) (by simp [Shape.cod]) rfl rfl (by simp [Shape.dom])
      (by simp [Shape.dom]) _ _)

/-- A crossing commutes with the identification of equal words on either side. -/
@[reassoc]
theorem cl_comp_eqToHom {t t' t'' : List I} {gs : List PG} (h : SChain t (pl t gs) t')
    (e : t' = t'') :
    cl D Sc t t' gs h ≫ eqToHom (congrArg (fun s => (pres D Sc).obj (ob D s)) e) =
      cl D Sc t t'' gs (e ▸ h) := by
  subst e
  simp

@[reassoc]
theorem eqToHom_comp_cl {t t' t'' : List I} {gs : List PG} (e : t = t')
    (h : SChain t' (pl t' gs) t'') :
    eqToHom (congrArg (fun s => (pres D Sc).obj (ob D s)) e) ≫ cl D Sc t' t'' gs h =
      cl D Sc t t'' gs (by subst e; exact h) := by
  subst e
  simp

theorem cl_eq_eqToHom_comp {t t₀ t' : List I} {gs : List PG} (e : t = t₀)
    (h : SChain t (pl t gs) t') :
    cl D Sc t t' gs h = eqToHom (congrArg (fun s => (pres D Sc).obj (ob D s)) e) ≫
      cl D Sc t₀ t' gs (by subst e; exact h) := by
  subst e
  simp

theorem sChain_cross_split {L L' l₁ l₂ s : List I} {x y : I} (hL : L = l₁ ++ [x, y] ++ l₂)
    (hL' : L' = l₁ ++ [y, x] ++ l₂) :
    SChain (L ++ s) (pl (L ++ s) [.cross l₁.length]) (L' ++ s) := by
  subst hL hL'
  exact sChain_ofShape' l₁ (l₂ ++ s) (.cross x y) (by simp [Shape.dom]) (by simp [Shape.cod]) rfl

/-- A crossing to the left of the moving strand passes through `g_n ⋯ g_1` with the sign
`(-1)^{p(x)p(y)p(i)p(ν)}`. -/
theorem cross_left_comp_moveHom (i x y : I) (l₁ : List I) (ν : List I) :
    ∀ (L L' l₂ : List I) (hL : L = l₁ ++ [x, y] ++ l₂) (hL' : L' = l₁ ++ [y, x] ++ l₂),
      cl D Sc (L ++ i :: ν) (L' ++ i :: ν) [.cross l₁.length] (sChain_cross_split hL hL') ≫
          moveHom D Sc i L' ν =
        zsign k (D.parity x * D.parity y * (D.parity i * wordSumParity D ν)) •
          (moveHom D Sc i L ν ≫
            cl D Sc (L ++ ν ++ [i]) (L' ++ ν ++ [i]) [.cross l₁.length]
              (by simpa only [List.append_assoc] using
                sChain_cross_split (s := ν ++ [i]) hL hL')) := by
  induction ν with
  | nil =>
    intro L L' l₂ hL hL'
    simp only [moveHom, wordSumParity, List.map_nil, List.sum_nil, mul_zero]
    rw [show zsign k (0 : ZMod 2) = 1 by simp [zsign], one_smul,
      cl_comp_eqToHom D Sc _ (show L' ++ [i] = L' ++ [] ++ [i] by simp),
      eqToHom_comp_cl D Sc (show L ++ [i] = L ++ [] ++ [i] by simp)]
  | cons j ν ih =>
    intro L L' l₂ hL hL'
    simp only [moveHom]
    rw [← Category.assoc, cl_comp_eqToHom D Sc _
        (show L' ++ i :: j :: ν = L' ++ [i, j] ++ ν by simp),
      cl_eq_eqToHom_comp D Sc (show L ++ i :: j :: ν = L ++ [i, j] ++ ν by simp),
      Category.assoc, ← Category.assoc (cl D Sc _ _ _ _)]
    subst hL hL'
    rw [cross_left_comp_intertwinerHom, Linear.smul_comp, Linear.comp_smul, Category.assoc,
      ← Category.assoc (cl D Sc _ _ _ _), cl_comp_eqToHom D Sc _
        (show l₁ ++ [y, x] ++ l₂ ++ [j, i] ++ ν = (l₁ ++ [y, x] ++ l₂ ++ [j]) ++ i :: ν by simp),
      cl_eq_eqToHom_comp D Sc
        (show l₁ ++ [x, y] ++ l₂ ++ [j, i] ++ ν = (l₁ ++ [x, y] ++ l₂ ++ [j]) ++ i :: ν by simp),
      Category.assoc, ← Category.assoc (cl D Sc _ _ _ _),
      ih (l₁ ++ [x, y] ++ l₂ ++ [j]) (l₁ ++ [y, x] ++ l₂ ++ [j]) (l₂ ++ [j]) (by simp)
        (by simp),
      Linear.smul_comp, Linear.comp_smul, Category.assoc, cl_comp_eqToHom]
    simp only [Category.assoc]
    rw [eqToHom_comp_cl]
    simp only [Linear.comp_smul, smul_smul, wordSumParity, List.map_cons, List.sum_cons, mul_add,
      zsign_add_eq]
    all_goals simp

theorem cl_comp_assoc {t t₁ t' : List I} (Q R : List PG) (h₁ : SChain t (pl t Q) t₁)
    (h₂ : SChain t₁ (pl t₁ R) t') {Z : H D Sc} (f : (pres D Sc).obj (ob D t') ⟶ Z) :
    cl D Sc t t₁ Q h₁ ≫ cl D Sc t₁ t' R h₂ ≫ f =
      cl D Sc t t' (Q ++ R) (sChain_append_of h₁ h₂) ≫ f := by
  rw [← Category.assoc, cl_comp]

/-- The braid relation `braid_ne` on words given up to equality. -/
theorem braid_ne_gen {t t' : List I} (l r : List I) (i j m : I) (hb : ¬(i = m ∧ i ≠ j))
    (ht : t = l ++ [i, j, m] ++ r) (ht' : t' = l ++ [m, j, i] ++ r) {L₁ L₂ : List PG}
    (e₁ : L₁ = [.cross (l.length + 1), .cross l.length, .cross (l.length + 1)])
    (e₂ : L₂ = [.cross l.length, .cross (l.length + 1), .cross l.length])
    (h₁ : SChain t (pl t L₁) t') (h₂ : SChain t (pl t L₂) t') :
    cl D Sc t t' L₁ h₁ = cl D Sc t t' L₂ h₂ := by
  subst ht ht' e₁ e₂
  exact (braid_ne D Sc l r i j m hb _ _).symm

theorem sChain_cross_succ (l v : List I) (i j k : I) :
    SChain (l ++ i :: j :: k :: v) (pl (l ++ i :: j :: k :: v) [.cross (l.length + 1)])
      (l ++ i :: k :: j :: v) :=
  sChain_ofShape' (l ++ [i]) v (.cross j k) (by simp [Shape.dom]) (by simp [Shape.cod])
    (by simp)

/-- The crossing of `j, k` followed by `g_a g_{a+1}`, moving `i` across `k, j`: the left side
of KKO's `τ_{a+1} g_a g_{a+1} = g_a g_{a+1} τ_a` on `l ++ i :: j :: k :: v`. -/
def meetLeft (l v : List I) (i j k : I) :
    (pres D Sc).obj (ob D (l ++ i :: j :: k :: v)) ⟶
      (pres D Sc).obj (ob D ((l ++ [k] ++ [j]) ++ i :: v)) :=
  cl D Sc (l ++ i :: j :: k :: v) (l ++ i :: k :: j :: v) [.cross (l.length + 1)]
      (sChain_cross_succ l v i j k) ≫
    eqToHom (congrArg (fun s => (pres D Sc).obj (ob D s))
      (show l ++ i :: k :: j :: v = l ++ [i, k] ++ (j :: v) by simp)) ≫
    intertwinerHom D Sc l (j :: v) i k ≫
    eqToHom (congrArg (fun s => (pres D Sc).obj (ob D s))
      (show l ++ [k, i] ++ (j :: v) = (l ++ [k]) ++ [i, j] ++ v by simp)) ≫
    intertwinerHom D Sc (l ++ [k]) v i j ≫
    eqToHom (congrArg (fun s => (pres D Sc).obj (ob D s))
      (show (l ++ [k]) ++ [j, i] ++ v = (l ++ [k] ++ [j]) ++ i :: v by simp))

/-- `g_a g_{a+1}`, moving `i` across `j, k`, followed by the crossing of `j, k`. -/
def meetRight (l v : List I) (i j k : I) :
    (pres D Sc).obj (ob D (l ++ i :: j :: k :: v)) ⟶
      (pres D Sc).obj (ob D ((l ++ [k] ++ [j]) ++ i :: v)) :=
  eqToHom (congrArg (fun s => (pres D Sc).obj (ob D s))
      (show l ++ i :: j :: k :: v = l ++ [i, j] ++ (k :: v) by simp)) ≫
    intertwinerHom D Sc l (k :: v) i j ≫
    eqToHom (congrArg (fun s => (pres D Sc).obj (ob D s))
      (show l ++ [j, i] ++ (k :: v) = (l ++ [j]) ++ [i, k] ++ v by simp)) ≫
    intertwinerHom D Sc (l ++ [j]) v i k ≫
    eqToHom (congrArg (fun s => (pres D Sc).obj (ob D s))
      (show (l ++ [j]) ++ [k, i] ++ v = (l ++ [j] ++ [k]) ++ i :: v by simp)) ≫
    cl D Sc ((l ++ [j] ++ [k]) ++ i :: v) ((l ++ [k] ++ [j]) ++ i :: v) [.cross l.length]
      (sChain_cross_split (l₁ := l) (l₂ := []) (x := j) (y := k) (by simp) (by simp))

/-- If the colours `j, k` both differ from `i`, the identity is the braid relation (1.9). -/
theorem meetLeft_eq_of_ne (l v : List I) {i j k : I} (hij : i ≠ j) (hik : i ≠ k) :
    meetLeft D Sc l v i j k = meetRight D Sc l v i j k := by
  unfold meetLeft meetRight
  rw [intertwinerHom_of_ne D Sc _ _ hik, intertwinerHom_of_ne D Sc _ _ hij,
    intertwinerHom_of_ne D Sc _ _ hij, intertwinerHom_of_ne D Sc _ _ hik]
  rw [cl_comp_eqToHom_assoc, cl_comp_assoc, cl_comp_eqToHom_assoc, cl_comp_assoc,
    cl_comp_eqToHom, eqToHom_comp_cl_assoc, cl_comp_eqToHom_assoc, cl_comp_assoc,
    cl_comp_eqToHom_assoc, cl_comp]
  · refine braid_ne_gen D Sc l v i j k (fun h => hik h.1) ?_ ?_ ?_ ?_ _ _ <;> simp
  all_goals simp

theorem sameIntertwiner_congr {w w' : List I} (e : w = w') {a a' : ℕ} (ha : a = a') (i : I) :
    sameIntertwiner D Sc w' a' i =
      eqToHom (congrArg (fun s => (pres D Sc).obj (ob D s)) e.symm) ≫
        sameIntertwiner D Sc w a i ≫ eqToHom (congrArg (fun s => (pres D Sc).obj (ob D s)) e) := by
  subst e ha
  simp

theorem cl_conj {t W : List I} {gs : List PG} (e : t = W) (h : SChain t (pl t gs) t) :
    cl D Sc t t gs h = eqToHom (congrArg (fun s => (pres D Sc).obj (ob D s)) e) ≫
      cl D Sc W W gs (by subst e; exact h) ≫
        eqToHom (congrArg (fun s => (pres D Sc).obj (ob D s)) e.symm) := by
  subst e
  simp

/-- On three strands of one colour the identity is the braid identity for the variants
(`braid_element`, `braid_gEven`). -/
theorem meetLeft_eq_self (l v : List I) (i : I) :
    meetLeft D Sc l v i i i = meetRight D Sc l v i i i := by
  unfold meetLeft meetRight
  rw [intertwinerHom_self, intertwinerHom_self,
    sameIntertwiner_congr D Sc (w := l ++ [i, i, i] ++ v)
      (show l ++ [i, i, i] ++ v = l ++ [i, i] ++ (i :: v) by simp) rfl,
    sameIntertwiner_congr D Sc (w := l ++ [i, i, i] ++ v)
      (show l ++ [i, i, i] ++ v = (l ++ [i]) ++ [i, i] ++ v by simp)
      (show l.length + 1 = (l ++ [i]).length by simp),
    cl_conj D Sc (show l ++ i :: i :: i :: v = l ++ [i, i, i] ++ v by simp),
    cl_conj D Sc (show (l ++ [i] ++ [i]) ++ i :: v = l ++ [i, i, i] ++ v by simp),
    ← crossE_eq_cl, ← crossE_eq_cl]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
  have hF : IsSignedNilHeckeFamily (zunit (D.parity i)) l.length 3
      (dotE D Sc (l ++ [i, i, i] ++ v)) (crossE D Sc (l ++ [i, i, i] ++ v)) :=
    isSignedNilHeckeFamily_block D Sc l v i 3
  have key : crossE D Sc (l ++ [i, i, i] ++ v) (l.length + 1) ≫
      sameIntertwiner D Sc (l ++ [i, i, i] ++ v) l.length i ≫
        sameIntertwiner D Sc (l ++ [i, i, i] ++ v) (l.length + 1) i =
      sameIntertwiner D Sc (l ++ [i, i, i] ++ v) l.length i ≫
        sameIntertwiner D Sc (l ++ [i, i, i] ++ v) (l.length + 1) i ≫
          crossE D Sc (l ++ [i, i, i] ++ v) l.length := by
    rw [← Category.assoc, ← Category.assoc, ← End.mul_def, ← End.mul_def, ← End.mul_def,
      ← End.mul_def]
    by_cases hp : D.parity i = 1
    · rw [hp, show zunit (1 : ZMod 2) = -1 by simp [zunit]] at hF
      simp only [sameIntertwiner, hp, ite_true]
      rw [← mul_assoc]
      exact (hF.braid_element (j := l.length) le_rfl (by omega)).symm
    · have hp0 := parity_eq_zero_of_ne_one hp
      rw [hp0, show zunit (0 : ZMod 2) = 1 by simp [zunit]] at hF
      simp only [sameIntertwiner, hp, ite_false]
      rw [← mul_assoc]
      exact (hF.braid_gEven (j := l.length) le_rfl (by omega)).symm
  rw [reassoc_of% key, eqToHom_trans]

theorem cl_eq_comp_eqToHom {t t₀ t' : List I} {gs : List PG} (e : t₀ = t')
    (h : SChain t (pl t gs) t') :
    cl D Sc t t' gs h = cl D Sc t t₀ gs (by subst e; exact h) ≫
      eqToHom (congrArg (fun s => (pres D Sc).obj (ob D s)) e) := by
  subst e
  simp

/-- The crossing `ψ` of `j, c` directly to the right of the moving strand `i` balances through
`g_n ⋯ g_1`, given the three-strand identity `meetLeft = meetRight`. -/
theorem cross_comp_moveHom_base (l v : List I) (i j c : I)
    (hmeet : meetLeft D Sc l v i j c = meetRight D Sc l v i j c)
    (h₁ : SChain (l ++ i :: j :: c :: v) (pl (l ++ i :: j :: c :: v) [.cross (l.length + 1)])
      (l ++ i :: c :: j :: v))
    (h₂ : SChain (l ++ j :: c :: v ++ [i]) (pl (l ++ j :: c :: v ++ [i]) [.cross l.length])
      (l ++ c :: j :: v ++ [i])) :
    cl D Sc _ _ [.cross (l.length + 1)] h₁ ≫ moveHom D Sc i l (c :: j :: v) =
      zsign k (D.parity j * D.parity c * (D.parity i * wordSumParity D v)) •
        (moveHom D Sc i l (j :: c :: v) ≫ cl D Sc _ _ [.cross l.length] h₂) := by
  have hL : cl D Sc _ _ [.cross (l.length + 1)] h₁ ≫ moveHom D Sc i l (c :: j :: v) =
      meetLeft D Sc l v i j c ≫ moveHom D Sc i (l ++ [c] ++ [j]) v ≫
        eqToHom (congrArg (fun s => (pres D Sc).obj (ob D s))
          (show l ++ [c] ++ [j] ++ v ++ [i] = l ++ c :: j :: v ++ [i] by simp)) := by
    simp only [moveHom, meetLeft, Category.assoc, eqToHom_trans_assoc, eqToHom_trans]
  have hc := eq_zsign_smul_symm (cross_left_comp_moveHom D Sc i j c l v (l ++ [j] ++ [c])
    (l ++ [c] ++ [j]) [] (by simp) (by simp))
  rw [hL, hmeet]
  simp only [moveHom, meetRight, Category.assoc, eqToHom_trans_assoc]
  rw [eqToHom_comp_cl, cl_eq_comp_eqToHom D Sc
    (show l ++ [c] ++ [j] ++ v ++ [i] = l ++ c :: j :: v ++ [i] by simp), reassoc_of% hc]
  · simp only [Linear.smul_comp, Linear.comp_smul, Category.assoc, smul_smul, zsign_mul_self,
      one_smul]
  · simp

theorem cl_cross_pos {t t' : List I} {p p' : ℕ} (hp : p = p') (h : SChain t (pl t [.cross p]) t') :
    cl D Sc t t' [.cross p] h = cl D Sc t t' [.cross p'] (hp ▸ h) := by
  subst hp
  rfl

theorem sChain_mid₁ (l m v : List I) (i j c : I) :
    SChain (l ++ i :: (m ++ j :: c :: v))
      (pl (l ++ i :: (m ++ j :: c :: v)) [.cross (l.length + 1 + m.length)])
      (l ++ i :: (m ++ c :: j :: v)) :=
  sChain_ofShape' (l ++ i :: m) v (.cross j c) (by simp [Shape.dom]) (by simp [Shape.cod])
    (by simp only [List.length_append, List.length_cons]; omega)

theorem sChain_mid₂ (l m v : List I) (i j c : I) :
    SChain (l ++ (m ++ j :: c :: v) ++ [i])
      (pl (l ++ (m ++ j :: c :: v) ++ [i]) [.cross (l.length + m.length)])
      (l ++ (m ++ c :: j :: v) ++ [i]) :=
  sChain_ofShape' (l ++ m) (v ++ [i]) (.cross j c) (by simp [Shape.dom]) (by simp [Shape.cod])
    (by simp)

/-- KKO (8.13), first identity, for an old crossing: the crossing `ψ` of `j, c` in the word
`ν = m ++ j :: c :: v` passes through `g_n ⋯ g_1` with the sign `(-1)^{p(j)p(c)p(i)p(ν)}`,
given the three-strand identity where it meets the moving strand `i`. -/
theorem cross_comp_moveHom (v : List I) (i j c : I)
    (hmeet : ∀ l', meetLeft D Sc l' v i j c = meetRight D Sc l' v i j c) (m : List I) :
    ∀ l : List I,
      cl D Sc _ _ [.cross (l.length + 1 + m.length)] (sChain_mid₁ l m v i j c) ≫
          moveHom D Sc i l (m ++ c :: j :: v) =
        zsign k (D.parity j * D.parity c * (D.parity i * (wordSumParity D m + wordSumParity D v))) •
          (moveHom D Sc i l (m ++ j :: c :: v) ≫
            cl D Sc _ _ [.cross (l.length + m.length)] (sChain_mid₂ l m v i j c)) := by
  induction m with
  | nil =>
    intro l
    have hw : wordSumParity D ([] : List I) = 0 := by simp [wordSumParity]
    rw [hw, zero_add]
    exact cross_comp_moveHom_base D Sc l v i j c (hmeet l) _ _
  | cons x m ih =>
    intro l
    simp only [List.cons_append, moveHom]
    rw [← Category.assoc, cl_comp_eqToHom D Sc _
        (show l ++ i :: x :: (m ++ c :: j :: v) = l ++ [i, x] ++ (m ++ c :: j :: v) by simp),
      cl_eq_eqToHom_comp D Sc
        (show l ++ i :: x :: (m ++ j :: c :: v) = l ++ [i, x] ++ (m ++ j :: c :: v) by simp),
      cl_cross_pos D Sc (p' := (l ++ [i, x] ++ m).length) (by simp; omega),
      Category.assoc, ← Category.assoc (cl D Sc _ _ _ _), cross_right_comp_intertwinerHom,
      Linear.smul_comp, Linear.comp_smul, Category.assoc, ← Category.assoc (cl D Sc _ _ _ _),
      cl_comp_eqToHom D Sc _
        (show l ++ [x, i] ++ (m ++ c :: j :: v) = (l ++ [x]) ++ i :: (m ++ c :: j :: v) by simp),
      cl_eq_eqToHom_comp D Sc
        (show l ++ [x, i] ++ (m ++ j :: c :: v) = (l ++ [x]) ++ i :: (m ++ j :: c :: v) by simp),
      cl_cross_pos D Sc (p' := (l ++ [x]).length + 1 + m.length) (by simp; omega),
      Category.assoc, ← Category.assoc (cl D Sc _ _ _ _), ih (l ++ [x]), Linear.smul_comp,
      Linear.comp_smul, Category.assoc, cl_comp_eqToHom]
    simp only [Category.assoc]
    rw [eqToHom_comp_cl, cl_cross_pos D Sc (p := l.length + (x :: m).length)
      (p' := (l ++ [x]).length + m.length) (by simp; omega)]
    · simp only [Linear.comp_smul, smul_smul, ← zsign_add_eq, wordSumParity, List.map_cons,
        List.sum_cons]
      exact congrArg (fun z => zsign k z • _) (by ring)
    all_goals simp

theorem slide_left_ne_gen {t t' : List I} (l r : List I) (i j : I) (hij : i ≠ j) {p : ℕ}
    (hp : l.length = p) (ht : t = l ++ [i, j] ++ r) (ht' : t' = l ++ [j, i] ++ r)
    (h₁ : SChain t (pl t [.dot p, .cross p]) t')
    (h₂ : SChain t (pl t [.cross p, .dot (p + 1)]) t') :
    cl D Sc t t' [.dot p, .cross p] h₁ =
      zsign k (D.parity i * D.parity j) • cl D Sc t t' [.cross p, .dot (p + 1)] h₂ := by
  subst hp ht ht'
  exact slide_left_ne D Sc l r i j hij h₁ h₂

theorem sChain_cross_left (l v : List I) (i c : I) :
    SChain (l ++ i :: c :: i :: v) (pl (l ++ i :: c :: i :: v) [.cross l.length])
      ((l ++ [c] ++ [i]) ++ i :: v) :=
  sChain_ofShape' l (i :: v) (.cross i c) (by simp [Shape.dom]) (by simp [Shape.cod]) rfl

/-- The crossings `ψ_a ψ_{a+1}` from `i, i, c` to `c, i, i` intertwine the variant `g` on the
first two strands with the variant on the last two. -/
theorem meet_core_eq_ne (l v : List I) {i c : I} (hic : i ≠ c) {L₁ L₂ : List PG}
    (hL₁ : L₁ = [.cross (l.length + 1), .cross l.length])
    (hL₂ : L₂ = [.cross (l.length + 1), .cross l.length])
    (h₁ : SChain (l ++ i :: i :: c :: v) (pl (l ++ i :: i :: c :: v) L₁)
      ((l ++ [c] ++ [i]) ++ i :: v))
    (h₂ : SChain (l ++ i :: i :: c :: v) (pl (l ++ i :: i :: c :: v) L₂)
      ((l ++ [c] ++ [i]) ++ i :: v)) :
    cl D Sc _ _ L₁ h₁ ≫ sameIntertwiner D Sc ((l ++ [c] ++ [i]) ++ i :: v) (l.length + 1) i =
      sameIntertwiner D Sc (l ++ i :: i :: c :: v) l.length i ≫ cl D Sc _ _ L₂ h₂ := by
  subst hL₁ hL₂
  have hΦ : ∀ h : SChain (l ++ i :: i :: c :: v)
      (pl (l ++ i :: i :: c :: v) [.cross (l.length + 1), .cross l.length])
      ((l ++ [c] ++ [i]) ++ i :: v),
      cl D Sc _ _ _ h = cl D Sc _ _ _ (sChain_cross_succ l v i i c) ≫
        cl D Sc _ _ _ (sChain_cross_left l v i c) := fun h => by
    rw [cl_comp]
    rfl
  have i₁ : cl D Sc (l ++ i :: i :: c :: v) (l ++ i :: c :: i :: v)
      ([.dot l.length] ++ [.cross (l.length + 1)])
      (sChain_append_of (sChain_dotAny _ _) (sChain_cross_succ l v i i c)) =
      zsign k (D.parity i * (D.parity i * D.parity c)) •
        (cl D Sc _ _ _ (sChain_cross_succ l v i i c) ≫
          cl D Sc (l ++ i :: c :: i :: v) _ [.dot l.length] (sChain_dotAny _ _)) := by
    rw [cl_comp]
    exact cl_interchange_gen D Sc l [] v (.dot i) (.cross i c) (by simp [Shape.dom])
      (by simp [Shape.cod]) rfl rfl (by simp [Shape.dom]) (by simp [Shape.dom]) _ _
  have s₁ : cl D Sc (l ++ i :: c :: i :: v) _ [.dot l.length] (sChain_dotAny _ _) ≫
      cl D Sc _ _ _ (sChain_cross_left l v i c) =
      zsign k (D.parity i * D.parity c) •
        (cl D Sc _ _ _ (sChain_cross_left l v i c) ≫
          cl D Sc ((l ++ [c] ++ [i]) ++ i :: v) _ [.dot (l.length + 1)] (sChain_dotAny _ _)) := by
    rw [cl_comp, cl_comp]
    exact slide_left_ne_gen D Sc l (i :: v) i c hic rfl (by simp) (by simp) _ _
  have s₂ : cl D Sc (l ++ i :: i :: c :: v) _ [.dot (l.length + 1)] (sChain_dotAny _ _) ≫
      cl D Sc _ _ _ (sChain_cross_succ l v i i c) =
      zsign k (D.parity i * D.parity c) •
        (cl D Sc _ _ _ (sChain_cross_succ l v i i c) ≫
          cl D Sc (l ++ i :: c :: i :: v) _ [.dot (l.length + 1 + 1)] (sChain_dotAny _ _)) := by
    rw [cl_comp, cl_comp]
    refine slide_left_ne_gen D Sc (l ++ [i]) v i c hic ?_ ?_ ?_ _ _ <;> simp
  have i₂ : cl D Sc (l ++ i :: c :: i :: v) _ [.dot (l.length + 1 + 1)] (sChain_dotAny _ _) ≫
      cl D Sc _ _ _ (sChain_cross_left l v i c) =
      zsign k (D.parity i * D.parity c * D.parity i) •
        (cl D Sc _ _ _ (sChain_cross_left l v i c) ≫
          cl D Sc ((l ++ [c] ++ [i]) ++ i :: v) _ [.dot (l.length + 1 + 1)]
            (sChain_dotAny _ _)) := by
    rw [cl_comp, cl_comp]
    exact eq_zsign_smul_symm (cl_interchange_gen D Sc l [] v (.cross i c) (.dot i)
      (by simp [Shape.dom]) (by simp [Shape.cod]) rfl rfl (by simp [Shape.dom])
      (by simp [Shape.dom]) _ _)
  have hsq : ∀ x y : ZMod 2, x * (x * y) = x * y := fun x y => by
    rw [← mul_assoc, parity_sq]
  have hsq' : ∀ x y : ZMod 2, x * y * x = x * y := fun x y => by
    rw [mul_comm, ← mul_assoc, parity_sq]
  have hu : dotE D Sc (l ++ i :: i :: c :: v) l.length ≫
      (cl D Sc _ _ _ (sChain_cross_succ l v i i c) ≫ cl D Sc _ _ _ (sChain_cross_left l v i c)) =
      zsign k 0 • ((cl D Sc _ _ _ (sChain_cross_succ l v i i c) ≫
        cl D Sc _ _ _ (sChain_cross_left l v i c)) ≫
          dotE D Sc ((l ++ [c] ++ [i]) ++ i :: v) (l.length + 1)) := by
    rw [dotE_eq_cl D Sc (sChain_dotAny _ _), dotE_eq_cl D Sc (sChain_dotAny _ _),
      ← Category.assoc, cl_comp, i₁, Linear.smul_comp, Category.assoc, s₁, Linear.comp_smul,
      smul_smul, hsq, zsign_mul_self, show zsign k (0 : ZMod 2) = 1 by simp [zsign],
      Category.assoc]
  have hv : dotE D Sc (l ++ i :: i :: c :: v) (l.length + 1) ≫
      (cl D Sc _ _ _ (sChain_cross_succ l v i i c) ≫ cl D Sc _ _ _ (sChain_cross_left l v i c)) =
      zsign k 0 • ((cl D Sc _ _ _ (sChain_cross_succ l v i i c) ≫
        cl D Sc _ _ _ (sChain_cross_left l v i c)) ≫
          dotE D Sc ((l ++ [c] ++ [i]) ++ i :: v) (l.length + 1 + 1)) := by
    rw [dotE_eq_cl D Sc (sChain_dotAny _ _), dotE_eq_cl D Sc (sChain_dotAny _ _),
      ← Category.assoc, s₂, Linear.smul_comp, Category.assoc, i₂, Linear.comp_smul,
      smul_smul, hsq', zsign_mul_self, show zsign k (0 : ZMod 2) = 1 by simp [zsign],
      Category.assoc]
  have hT : crossE D Sc (l ++ i :: i :: c :: v) l.length ≫
      (cl D Sc _ _ _ (sChain_cross_succ l v i i c) ≫ cl D Sc _ _ _ (sChain_cross_left l v i c)) =
      zsign k 0 • ((cl D Sc _ _ _ (sChain_cross_succ l v i i c) ≫
        cl D Sc _ _ _ (sChain_cross_left l v i c)) ≫
          crossE D Sc ((l ++ [c] ++ [i]) ++ i :: v) (l.length + 1)) := by
    rw [crossE_eq_cl D Sc (sChain_ofShape' l (c :: v) (.cross i i)
        (t := l ++ i :: i :: c :: v) (t' := l ++ i :: i :: c :: v) (by simp [Shape.dom])
        (by simp [Shape.cod]) rfl),
      crossE_eq_cl D Sc (sChain_ofShape' (l ++ [c]) v (.cross i i)
        (t := (l ++ [c] ++ [i]) ++ i :: v) (t' := (l ++ [c] ++ [i]) ++ i :: v)
        (by simp [Shape.dom]) (by simp [Shape.cod]) (by simp)),
      show zsign k (0 : ZMod 2) = 1 by simp [zsign], one_smul]
    simp only [cl_comp]
    refine (braid_ne_gen D Sc l v i i c (fun h => h.2 rfl) ?_ ?_ ?_ ?_ _ _).symm <;> simp
  have hS := variants_comp_of D Sc _ 0 hu hv hT
  rw [show zsign k (0 : ZMod 2) = 1 by simp [zsign], one_smul, one_smul] at hS
  rw [hΦ h₁]
  unfold sameIntertwiner
  split_ifs
  · exact hS.1.symm
  · exact hS.2.symm

/-- If `i = j ≠ c`, the identity follows from the exact braid relation on `i, i, c` and the
dot slides, through `variants_comp_of`. -/
theorem meetLeft_eq_of_eq_ne (l v : List I) {i c : I} (hic : i ≠ c) :
    meetLeft D Sc l v i i c = meetRight D Sc l v i i c := by
  unfold meetLeft meetRight
  rw [intertwinerHom_of_ne D Sc l (i :: v) hic, intertwinerHom_of_ne D Sc (l ++ [i]) v hic,
    intertwinerHom_self, intertwinerHom_self,
    sameIntertwiner_congr D Sc (w := l ++ i :: i :: c :: v)
      (show l ++ i :: i :: c :: v = l ++ [i, i] ++ (c :: v) by simp) rfl,
    sameIntertwiner_congr D Sc (w := (l ++ [c] ++ [i]) ++ i :: v)
      (show (l ++ [c] ++ [i]) ++ i :: v = (l ++ [c]) ++ [i, i] ++ v by simp)
      (show l.length + 1 = (l ++ [c]).length by simp)]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp, eqToHom_trans,
    Category.comp_id]
  rw [cl_comp_eqToHom_assoc, cl_comp_assoc, cl_comp_eqToHom_assoc, eqToHom_comp_cl_assoc,
    cl_comp_eqToHom_assoc, cl_comp]
  · exact meet_core_eq_ne D Sc l v hic (by simp) (by simp) _ _
  all_goals simp

/-- The three-strand identity holds unless the colours are `i, j, i` with `j ≠ i`. -/
theorem meetLeft_eq (l v : List I) {i j c : I} (hb : ¬(i = c ∧ i ≠ j)) :
    meetLeft D Sc l v i j c = meetRight D Sc l v i j c := by
  by_cases hij : i = j
  · subst hij
    by_cases hic : i = c
    · subst hic
      exact meetLeft_eq_self D Sc l v i
    · exact meetLeft_eq_of_eq_ne D Sc l v hic
  · exact meetLeft_eq_of_ne D Sc l v hij (fun h => hb ⟨h, hij⟩)

/-- KKO (8.13), first identity, for an old crossing of `j, c`, unless `c = i ≠ j`. -/
theorem cross_comp_moveHom_of (v : List I) {i j c : I} (hb : ¬(i = c ∧ i ≠ j)) (m l : List I) :
    cl D Sc _ _ [.cross (l.length + 1 + m.length)] (sChain_mid₁ l m v i j c) ≫
        moveHom D Sc i l (m ++ c :: j :: v) =
      zsign k (D.parity j * D.parity c * (D.parity i * (wordSumParity D m + wordSumParity D v))) •
        (moveHom D Sc i l (m ++ j :: c :: v) ≫
          cl D Sc _ _ [.cross (l.length + m.length)] (sChain_mid₂ l m v i j c)) :=
  cross_comp_moveHom D Sc v i j c (fun l' => meetLeft_eq D Sc l' v hb) m l

end OddMath.QuiverHecke
