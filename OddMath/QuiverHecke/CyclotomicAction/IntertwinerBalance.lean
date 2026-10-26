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

Not treated here: the three-strand identity where the moving strand meets the crossing, which
is the braid identity of Lemma 8.3 for mixed colours; on three strands of one colour it is
`IsSignedNilHeckeFamily.braid_element` and `braid_gEven`.
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
    cl D Sc (l ++ [i, j] ++ (m ++ [x, y] ++ v)) (l ++ [i, j] ++ (m ++ [y, x] ++ v))
        [.cross (l ++ [i, j] ++ m).length] (sChain_ofShape' (l ++ [i, j] ++ m) v (.cross x y)
          (by simp [Shape.dom]) (by simp [Shape.cod]) rfl) ≫
        intertwinerHom D Sc l (m ++ [y, x] ++ v) i j =
      zsign k (D.parity i * D.parity j * (D.parity x * D.parity y)) •
        (intertwinerHom D Sc l (m ++ [x, y] ++ v) i j ≫
          cl D Sc (l ++ [j, i] ++ (m ++ [x, y] ++ v)) (l ++ [j, i] ++ (m ++ [y, x] ++ v))
            [.cross (l ++ [j, i] ++ m).length] (sChain_ofShape' (l ++ [j, i] ++ m) v
              (.cross x y) (by simp [Shape.dom]) (by simp [Shape.cod]) rfl)) := by
  by_cases h : i = j
  · subst h
    have hu := eq_zsign_smul_symm (k := k) (q := D.parity i * (D.parity x * D.parity y))
      (a := dotE D Sc (l ++ [i, i] ++ (m ++ [x, y] ++ v)) l.length ≫
        cl D Sc (l ++ [i, i] ++ (m ++ [x, y] ++ v)) (l ++ [i, i] ++ (m ++ [y, x] ++ v))
          [.cross (l ++ [i, i] ++ m).length] (sChain_ofShape' (l ++ [i, i] ++ m) v (.cross x y)
            (by simp [Shape.dom]) (by simp [Shape.cod]) rfl))
      (b := cl D Sc (l ++ [i, i] ++ (m ++ [x, y] ++ v)) (l ++ [i, i] ++ (m ++ [y, x] ++ v))
          [.cross (l ++ [i, i] ++ m).length] (sChain_ofShape' (l ++ [i, i] ++ m) v (.cross x y)
            (by simp [Shape.dom]) (by simp [Shape.cod]) rfl) ≫
        dotE D Sc (l ++ [i, i] ++ (m ++ [y, x] ++ v)) l.length) (by
      rw [dotE_eq_cl D Sc (sChain_dotAny _ _), dotE_eq_cl D Sc (sChain_dotAny _ _), cl_comp,
        cl_comp]
      exact cl_interchange_gen D Sc l ([i] ++ m) v (.dot i) (.cross x y)
        (by simp [Shape.dom]) (by simp [Shape.cod]) rfl rfl (by simp [Shape.dom])
        (by simp [Shape.dom]) _ _)
    have hv := eq_zsign_smul_symm (k := k) (q := D.parity i * (D.parity x * D.parity y))
      (a := dotE D Sc (l ++ [i, i] ++ (m ++ [x, y] ++ v)) (l.length + 1) ≫
        cl D Sc (l ++ [i, i] ++ (m ++ [x, y] ++ v)) (l ++ [i, i] ++ (m ++ [y, x] ++ v))
          [.cross (l ++ [i, i] ++ m).length] (sChain_ofShape' (l ++ [i, i] ++ m) v (.cross x y)
            (by simp [Shape.dom]) (by simp [Shape.cod]) rfl))
      (b := cl D Sc (l ++ [i, i] ++ (m ++ [x, y] ++ v)) (l ++ [i, i] ++ (m ++ [y, x] ++ v))
          [.cross (l ++ [i, i] ++ m).length] (sChain_ofShape' (l ++ [i, i] ++ m) v (.cross x y)
            (by simp [Shape.dom]) (by simp [Shape.cod]) rfl) ≫
        dotE D Sc (l ++ [i, i] ++ (m ++ [y, x] ++ v)) (l.length + 1)) (by
      rw [dotE_eq_cl D Sc (sChain_dotAny _ _), dotE_eq_cl D Sc (sChain_dotAny _ _), cl_comp,
        cl_comp]
      exact cl_interchange_gen D Sc (l ++ [i]) m v (.dot i) (.cross x y)
        (by simp [Shape.dom]) (by simp [Shape.cod]) (by simp) (by simp)
        (by simp only [Shape.dom, List.length_append, List.length_cons, List.length_nil])
        (by simp only [Shape.dom, List.length_append, List.length_cons, List.length_nil])
        _ _)
    have hT := eq_zsign_smul_symm (k := k) (q := D.parity i * (D.parity x * D.parity y))
      (a := crossE D Sc (l ++ [i, i] ++ (m ++ [x, y] ++ v)) l.length ≫
        cl D Sc (l ++ [i, i] ++ (m ++ [x, y] ++ v)) (l ++ [i, i] ++ (m ++ [y, x] ++ v))
          [.cross (l ++ [i, i] ++ m).length] (sChain_ofShape' (l ++ [i, i] ++ m) v (.cross x y)
            (by simp [Shape.dom]) (by simp [Shape.cod]) rfl))
      (b := cl D Sc (l ++ [i, i] ++ (m ++ [x, y] ++ v)) (l ++ [i, i] ++ (m ++ [y, x] ++ v))
          [.cross (l ++ [i, i] ++ m).length] (sChain_ofShape' (l ++ [i, i] ++ m) v (.cross x y)
            (by simp [Shape.dom]) (by simp [Shape.cod]) rfl) ≫
        crossE D Sc (l ++ [i, i] ++ (m ++ [y, x] ++ v)) l.length) (by
      rw [crossE_eq_cl D Sc (sChain_crossAt l (m ++ [x, y] ++ v) i i),
        crossE_eq_cl D Sc (sChain_crossAt l (m ++ [y, x] ++ v) i i), cl_comp, cl_comp,
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
theorem cl_comp_eqToHom {t t' t'' : List I} {gs : List PG} (h : SChain t (pl t gs) t')
    (e : t' = t'') :
    cl D Sc t t' gs h ≫ eqToHom (congrArg (fun s => (pres D Sc).obj (ob D s)) e) =
      cl D Sc t t'' gs (e ▸ h) := by
  subst e
  simp

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

theorem sChain_cross_of {L L' l₁ l₂ s : List I} {x y : I} (hL : L = l₁ ++ [x, y] ++ l₂)
    (hL' : L' = l₁ ++ [y, x] ++ l₂) :
    SChain (L ++ s) (pl (L ++ s) [.cross l₁.length]) (L' ++ s) := by
  subst hL hL'
  exact sChain_ofShape' l₁ (l₂ ++ s) (.cross x y) (by simp [Shape.dom]) (by simp [Shape.cod]) rfl

/-- A crossing to the left of the moving strand passes through `g_n ⋯ g_1` with the sign
`(-1)^{p(x)p(y)p(i)p(ν)}`. -/
theorem cross_left_comp_moveHom (i x y : I) (l₁ : List I) (ν : List I) :
    ∀ (L L' l₂ : List I) (hL : L = l₁ ++ [x, y] ++ l₂) (hL' : L' = l₁ ++ [y, x] ++ l₂),
      cl D Sc (L ++ i :: ν) (L' ++ i :: ν) [.cross l₁.length] (sChain_cross_of hL hL') ≫
          moveHom D Sc i L' ν =
        zsign k (D.parity x * D.parity y * (D.parity i * wordParity D ν)) •
          (moveHom D Sc i L ν ≫
            cl D Sc (L ++ ν ++ [i]) (L' ++ ν ++ [i]) [.cross l₁.length]
              (by simpa only [List.append_assoc] using
                sChain_cross_of (s := ν ++ [i]) hL hL')) := by
  induction ν with
  | nil =>
    intro L L' l₂ hL hL'
    simp only [moveHom, wordParity, List.map_nil, List.sum_nil, mul_zero]
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
    simp only [Linear.comp_smul, smul_smul, wordParity, List.map_cons, List.sum_cons, mul_add,
      zsign_add_eq]
    all_goals simp

end OddMath.QuiverHecke
