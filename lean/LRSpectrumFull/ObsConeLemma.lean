/-
# Cone lemma (free repeat lines of a 2-torus): the counting core

Formalisation of the repeat-line count of the accompanying note (Theorem 2 there).

Forms are pairs `φ = (a, b) : ℤ × ℤ` (the linear form `a s + b t` of a 2-torus).  The projective line
`ker φ` is labelled by `lineOf φ : Option ℚ` (the slope `b / a`, `none` when `a = 0`); for nonzero
forms `lineOf φ = lineOf φ'` iff the forms are proportional (`lineOf_eq_iff`).

Normalised setting (after the choice of a generic direction `x` and of signs, as in the proof in the
accompanying note): all first coordinates are positive, the forms are pairwise distinct.  Then

* `ordered_sumset` (`acl`): the counting step `|XY| ≥ |X| + |Y| - 1` in an ordered group, here the
  Cauchy-Davenport theorem for linearly ordered cancellative semigroups of Mathlib, applied to logarithms
  of the ratios;
* `cone_lemma_normalised`: with `d` the number of slope classes (`2 ≤ d`), the number of free repeat
  lines `|ker(φ_p ± φ_q) \ {ker φ_r}|` is at least `2 n - d`, for forms with positive first coordinate;
* `cone_lemma`: the general statement (nonzero forms, pairwise distinct up to sign, `d ≥ 2`), by the
  shear `(a, b) ↦ (a + N b, b)` for a generic `N` and sign normalisation (`free_card_le`,
  `slope_card_eq`);
* `A2_free_card`, `A2_slope_card`: the bound is attained on the `A2` forms (`2 n - d = 3`).

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import Mathlib.Combinatorics.Additive.CauchyDavenport
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

set_option linter.unnecessarySeqFocus false

namespace LRSpectrumFull
namespace ObsConeLemma

open Finset
open scoped Pointwise

/-! ## Section 1: the ordered-group counting step -/

/-- **Counting core** `|AB| ≥ |A| + |B| - 1` (written additively on logarithms): if `lab a b` determines
the ratio `b / a` through `g`, then the set of labels has at least `|A| + |B| - 1` elements. -/
theorem acl {X : Type*} [DecidableEq X] (A B : Finset ℚ) (hA : ∀ a ∈ A, 0 < a)
    (hB : ∀ b ∈ B, 0 < b) (hAne : A.Nonempty) (hBne : B.Nonempty) (lab : ℚ → ℚ → X) (g : X → ℝ)
    (hg : ∀ a ∈ A, ∀ b ∈ B, g (lab a b) = Real.log (b : ℝ) - Real.log (a : ℝ)) :
    A.card + B.card ≤ ((A ×ˢ B).image (fun p => lab p.1 p.2)).card + 1 := by
  set Xs : Finset ℝ := B.image (fun b : ℚ => Real.log (b : ℝ)) with hXs
  set Ys : Finset ℝ := A.image (fun a : ℚ => - Real.log (a : ℝ)) with hYs
  have hXc : Xs.card = B.card := by
    apply Finset.card_image_of_injOn
    intro b hb b' hb' h
    have h1 : (0 : ℝ) < b := by exact_mod_cast hB b hb
    have h2 : (0 : ℝ) < b' := by exact_mod_cast hB b' hb'
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr h1) (Set.mem_Ioi.mpr h2) h
    exact_mod_cast this
  have hYc : Ys.card = A.card := by
    apply Finset.card_image_of_injOn
    intro a ha a' ha' h
    have h1 : (0 : ℝ) < a := by exact_mod_cast hA a ha
    have h2 : (0 : ℝ) < a' := by exact_mod_cast hA a' ha'
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr h1) (Set.mem_Ioi.mpr h2) (neg_inj.mp h)
    exact_mod_cast this
  have hXne : Xs.Nonempty := hBne.image _
  have hYne : Ys.Nonempty := hAne.image _
  have hcd := cauchy_davenport_add_of_linearOrder_isCancelAdd hXne hYne
  have hsub : Xs + Ys ⊆ ((A ×ˢ B).image (fun p => lab p.1 p.2)).image g := by
    intro z hz
    rw [Finset.mem_add] at hz
    obtain ⟨x, hx, y, hy, rfl⟩ := hz
    rw [hXs, Finset.mem_image] at hx
    rw [hYs, Finset.mem_image] at hy
    obtain ⟨b, hb, rfl⟩ := hx
    obtain ⟨a, ha, rfl⟩ := hy
    rw [Finset.mem_image]
    refine ⟨lab a b, Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨ha, hb⟩, rfl⟩, ?_⟩
    rw [hg a ha b hb]; ring
  have h2 := Finset.card_le_card hsub
  have h3 := Finset.card_image_le (s := (A ×ˢ B).image (fun p => lab p.1 p.2)) (f := g)
  rw [hXc, hYc] at hcd
  omega

/-! ## Section 2: the two label families -/

/-- Label (slope) of the sum of the forms of slopes `a < b` with first coordinates `x, y > 0`. -/
def sumLab (a b x y : ℚ) : Option ℚ := some ((a * x + b * y) / (x + y))

/-- Label of the difference of the forms of slope `b` (first coordinate `y`) and slope `a` (first
coordinate `x`); `none` is the vertical line (`y = x`). -/
def difLab (a b x y : ℚ) : Option ℚ := if y = x then none else some ((b * y - a * x) / (y - x))

/-- Recovery of the ratio `y / x` from a sum label. -/
noncomputable def sumRatio (a b : ℚ) : Option ℚ → ℝ
  | some σ => Real.log (((σ : ℝ) - a) / (b - σ))
  | none => 0

/-- Recovery of the ratio `y / x` from a difference label. -/
noncomputable def difRatio (a b : ℚ) : Option ℚ → ℝ
  | some σ => Real.log (((σ : ℝ) - a) / (σ - b))
  | none => 0

theorem sumRatio_sumLab (a b x y : ℚ) (hab : a < b) (hx : 0 < x) (hy : 0 < y) :
    sumRatio a b (sumLab a b x y) = Real.log (y : ℝ) - Real.log (x : ℝ) := by
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have habR : (a : ℝ) < b := by exact_mod_cast hab
  simp only [sumLab, sumRatio]
  rw [← Real.log_div hyR.ne' hxR.ne']
  congr 1
  push_cast
  have h1 : (x : ℝ) + y ≠ 0 := by positivity
  have h2 : (b : ℝ) - a ≠ 0 := by linarith
  rw [div_eq_div_iff]
  · field_simp
    ring
  · have : (b : ℝ) - ((a * x + b * y) / (x + y)) = (b - a) * x / (x + y) := by
      field_simp; ring
    rw [this]; positivity
  · exact hxR.ne'

theorem difRatio_difLab (a b x y : ℚ) (hab : a < b) (hx : 0 < x) (hy : 0 < y) :
    difRatio a b (difLab a b x y) = Real.log (y : ℝ) - Real.log (x : ℝ) := by
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have habR : (a : ℝ) < b := by exact_mod_cast hab
  by_cases hxy : y = x
  · subst hxy
    simp [difLab, difRatio]
  · simp only [difLab, hxy, if_false, difRatio]
    rw [← Real.log_div hyR.ne' hxR.ne']
    congr 1
    push_cast
    have hne : (y : ℝ) - x ≠ 0 := by
      intro h; apply hxy; exact_mod_cast (by linarith : (y : ℝ) = x)
    have h3 : ((b : ℝ) * y - a * x) / (y - x) - a = (b - a) * y / (y - x) := by
      field_simp; ring
    have h4 : ((b : ℝ) * y - a * x) / (y - x) - b = (b - a) * x / (y - x) := by
      field_simp; ring
    rw [h3, h4]
    have : (b - a : ℝ) ≠ 0 := by linarith
    field_simp

/-- Sum lines: `|A| + |B| - 1` distinct labels. -/
theorem sum_count (A B : Finset ℚ) (a b : ℚ) (hab : a < b) (hA : ∀ x ∈ A, 0 < x)
    (hB : ∀ y ∈ B, 0 < y) (hAne : A.Nonempty) (hBne : B.Nonempty) :
    A.card + B.card ≤ ((A ×ˢ B).image (fun p => sumLab a b p.1 p.2)).card + 1 :=
  acl A B hA hB hAne hBne (sumLab a b) (sumRatio a b)
    (fun x hx y hy => sumRatio_sumLab a b x y hab (hA x hx) (hB y hy))

/-- Difference lines: `|A| + |B| - 1` distinct labels. -/
theorem dif_count (A B : Finset ℚ) (a b : ℚ) (hab : a < b) (hA : ∀ x ∈ A, 0 < x)
    (hB : ∀ y ∈ B, 0 < y) (hAne : A.Nonempty) (hBne : B.Nonempty) :
    A.card + B.card ≤ ((A ×ˢ B).image (fun p => difLab a b p.1 p.2)).card + 1 :=
  acl A B hA hB hAne hBne (difLab a b) (difRatio a b)
    (fun x hx y hy => difRatio_difLab a b x y hab (hA x hx) (hB y hy))

/-! ## Section 3: forms, lines, free repeat lines -/

/-- A linear form `a s + b t` on the parameter plane of a 2-torus. -/
abbrev Form := ℤ × ℤ

/-- Label of the projective line `ker φ` (its slope; `none` for a vertical line). -/
def lineOf (φ : Form) : Option ℚ := if φ.1 = 0 then none else some ((φ.2 : ℚ) / (φ.1 : ℚ))

/-- The cross product; `cr u v = 0` iff the forms `u`, `v` are proportional. -/
def cr (u v : Form) : ℤ := u.1 * v.2 - u.2 * v.1

/-- For nonzero forms, equal labels are exactly proportionality (equal kernels). -/
theorem lineOf_eq_iff {u v : Form} (hu : u ≠ 0) (hv : v ≠ 0) :
    lineOf u = lineOf v ↔ cr u v = 0 := by
  obtain ⟨u1, u2⟩ := u
  obtain ⟨v1, v2⟩ := v
  unfold lineOf cr
  simp only
  by_cases h1 : u1 = 0 <;> by_cases h2 : v1 = 0
  · subst h1; subst h2; simp
  · subst h1
    have hu2 : u2 ≠ 0 := by
      intro h; apply hu; simp [h]
    simp only [if_true, h2, if_false, zero_mul, zero_sub]
    constructor
    · intro h; cases h
    · intro h
      exfalso
      have : u2 * v1 = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact hu2 h
      · exact h2 h
  · subst h2
    have hv2 : v2 ≠ 0 := by
      intro h; apply hv; simp [h]
    simp only [if_true, h1, if_false, mul_zero, sub_zero]
    constructor
    · intro h; cases h
    · intro h
      exfalso
      rcases mul_eq_zero.mp h with h | h
      · exact h1 h
      · exact hv2 h
  · simp only [h1, h2, if_false, Option.some.injEq]
    have h1' : (u1 : ℚ) ≠ 0 := by exact_mod_cast h1
    have h2' : (v1 : ℚ) ≠ 0 := by exact_mod_cast h2
    rw [div_eq_div_iff h1' h2']
    constructor
    · intro h
      have : ((u2 * v1 : ℤ) : ℚ) = ((v2 * u1 : ℤ) : ℚ) := by push_cast; linarith
      have := Int.cast_injective this
      linarith
    · intro h
      have : u2 * v1 = v2 * u1 := by linarith
      have h' : ((u2 * v1 : ℤ) : ℚ) = ((v2 * u1 : ℤ) : ℚ) := by rw [this]
      push_cast at h'
      linarith

section Normalised

variable {n : ℕ}

/-- The label (slope) set of the forms: their proportionality classes. -/
def slopeLabels (φ : Fin n → Form) : Finset (Option ℚ) :=
  Finset.univ.image (fun r => lineOf (φ r))

/-- The repeat lines: the lines `ker (φ_p + φ_q)` and `ker (φ_p - φ_q)`, `p ≠ q`. -/
def repeatLines (φ : Fin n → Form) : Finset (Option ℚ) :=
  ((Finset.univ.filter (fun pq : Fin n × Fin n => pq.1 ≠ pq.2)).image
      (fun pq => lineOf (φ pq.1 + φ pq.2))) ∪
  ((Finset.univ.filter (fun pq : Fin n × Fin n => pq.1 ≠ pq.2)).image
      (fun pq => lineOf (φ pq.1 - φ pq.2)))

/-- The free repeat lines: repeat lines that are no `ker φ_r`. -/
def freeRepeatLines (φ : Fin n → Form) : Finset (Option ℚ) := repeatLines φ \ slopeLabels φ

/-- The slope of the `r`-th form (normalised case, `a > 0`). -/
def sl (φ : Fin n → Form) (r : Fin n) : ℚ := ((φ r).2 : ℚ) / ((φ r).1 : ℚ)

/-- The first coordinate of the `r`-th form, as a rational. -/
def al (φ : Fin n → Form) (r : Fin n) : ℚ := ((φ r).1 : ℚ)

variable {φ : Fin n → Form}

theorem al_pos (hα : ∀ r, 0 < (φ r).1) (r : Fin n) : 0 < al φ r := by
  unfold al; exact_mod_cast hα r

theorem beta_eq (hα : ∀ r, 0 < (φ r).1) (r : Fin n) : ((φ r).2 : ℚ) = sl φ r * al φ r := by
  have : ((φ r).1 : ℚ) ≠ 0 := by exact_mod_cast (hα r).ne'
  unfold sl al
  field_simp

theorem lineOf_self (hα : ∀ r, 0 < (φ r).1) (r : Fin n) : lineOf (φ r) = some (sl φ r) := by
  have : (φ r).1 ≠ 0 := (hα r).ne'
  simp [lineOf, sl, this]

theorem lineOf_add (hα : ∀ r, 0 < (φ r).1) (p q : Fin n) :
    lineOf (φ p + φ q) = sumLab (sl φ p) (sl φ q) (al φ p) (al φ q) := by
  have hpos : 0 < (φ p + φ q).1 := by
    have := hα p; have := hα q; simp only [Prod.fst_add]; omega
  have hne : (φ p + φ q).1 ≠ 0 := hpos.ne'
  simp only [lineOf, hne, if_false, sumLab]
  congr 1
  have e1 : (((φ p + φ q).1 : ℤ) : ℚ) = al φ p + al φ q := by simp [al]
  have e2 : (((φ p + φ q).2 : ℤ) : ℚ) = sl φ p * al φ p + sl φ q * al φ q := by
    simp only [Prod.snd_add]; push_cast; rw [beta_eq hα p, beta_eq hα q]
  rw [e1, e2]

theorem lineOf_sub (hα : ∀ r, 0 < (φ r).1) (p q : Fin n) :
    lineOf (φ p - φ q) = difLab (sl φ q) (sl φ p) (al φ q) (al φ p) := by
  unfold difLab
  by_cases h : al φ p = al φ q
  · have : (φ p - φ q).1 = 0 := by
      have : ((φ p).1 : ℚ) = (φ q).1 := h
      have := Int.cast_injective this
      simp only [Prod.fst_sub]; omega
    simp [lineOf, this, h]
  · have hne : (φ p - φ q).1 ≠ 0 := by
      intro h0
      apply h
      simp only [Prod.fst_sub] at h0
      unfold al
      have : (φ p).1 = (φ q).1 := by omega
      rw [this]
    simp only [lineOf, hne, if_false, h]
    congr 1
    have e1 : (((φ p - φ q).1 : ℤ) : ℚ) = al φ p - al φ q := by simp [al]
    have e2 : (((φ p - φ q).2 : ℤ) : ℚ) = sl φ p * al φ p - sl φ q * al φ q := by
      simp only [Prod.snd_sub]; push_cast; rw [beta_eq hα p, beta_eq hα q]
    rw [e1, e2]

/-- Within a slope class the first coordinate separates the (pairwise distinct) forms. -/
theorem al_injOn (hα : ∀ r, 0 < (φ r).1) (hinj : Function.Injective φ) (P : Finset (Fin n))
    (c : ℚ) (hP : ∀ r ∈ P, sl φ r = c) : Set.InjOn (al φ) (P : Set (Fin n)) := by
  intro p hp q hq h
  apply hinj
  have hp' := hP p hp
  have hq' := hP q hq
  have h1 : (φ p).1 = (φ q).1 := by
    have : ((φ p).1 : ℚ) = (φ q).1 := h
    exact Int.cast_injective this
  have h2 : (φ p).2 = (φ q).2 := by
    have := beta_eq hα p
    have := beta_eq hα q
    have e : ((φ p).2 : ℚ) = (φ q).2 := by
      rw [beta_eq hα p, beta_eq hα q, hp', hq']
      unfold al at h
      rw [show al φ p = al φ q from h]
    exact Int.cast_injective e
  exact Prod.ext h1 h2

end Normalised

/-! ## Section 4: the cone lemma (normalised) -/

theorem sumLab_mem_Ioo (a b x y : ℚ) (hab : a < b) (hx : 0 < x) (hy : 0 < y) :
    ∃ σ, sumLab a b x y = some σ ∧ a < σ ∧ σ < b := by
  refine ⟨(a * x + b * y) / (x + y), rfl, ?_, ?_⟩
  · rw [lt_div_iff₀ (by positivity)]; nlinarith [mul_pos (sub_pos.mpr hab) hy]
  · rw [div_lt_iff₀ (by positivity)]; nlinarith [mul_pos (sub_pos.mpr hab) hx]

theorem difLab_out (a b x y : ℚ) (hab : a < b) (hx : 0 < x) (hy : 0 < y) :
    difLab a b x y = none ∨ ∃ σ, difLab a b x y = some σ ∧ (σ < a ∨ b < σ) := by
  unfold difLab
  by_cases h : y = x
  · left; simp [h]
  · right
    refine ⟨(b * y - a * x) / (y - x), by simp [h], ?_⟩
    rcases lt_or_gt_of_ne h with h' | h'
    · left
      rw [div_lt_iff_of_neg (by linarith)]
      nlinarith [mul_pos (sub_pos.mpr hab) hy]
    · right
      rw [lt_div_iff₀ (by linarith)]
      nlinarith [mul_pos (sub_pos.mpr hab) hx]

section Main

variable {n : ℕ} {φ : Fin n → Form}

/-- **Cone lemma, normalised form.**  Let `φ_1, ..., φ_n` be pairwise distinct forms with positive first
coordinates, falling in `d ≥ 2` proportionality classes.  Then the number of free repeat lines is at
least `2 n - d` (stated without subtraction: `2 n ≤ #free + d`). -/
theorem cone_lemma_normalised (hα : ∀ r, 0 < (φ r).1) (hinj : Function.Injective φ)
    (hd : 2 ≤ (slopeLabels φ).card) :
    2 * n ≤ (freeRepeatLines φ).card + (slopeLabels φ).card := by
  classical
  set Sset : Finset ℚ := Finset.univ.image (sl φ) with hSset
  have hlab : slopeLabels φ = Sset.image some := by
    ext l
    simp only [slopeLabels, hSset, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨r, rfl⟩; exact ⟨sl φ r, ⟨r, rfl⟩, (lineOf_self hα r).symm⟩
    · rintro ⟨σ, ⟨r, rfl⟩, rfl⟩; exact ⟨r, lineOf_self hα r⟩
  have hcard : (slopeLabels φ).card = Sset.card := by
    rw [hlab]; exact Finset.card_image_of_injective _ (Option.some_injective _)
  rw [hcard] at hd ⊢
  obtain ⟨d', hd'⟩ : ∃ d', Sset.card = d' + 1 := ⟨Sset.card - 1, by omega⟩
  have hd1 : 1 ≤ d' := by omega
  set e : Fin (d' + 1) ↪o ℚ := Sset.orderEmbOfFin hd' with he
  have he_mem : ∀ i, e i ∈ Sset := fun i => Finset.orderEmbOfFin_mem Sset hd' i
  have he_range : ∀ σ ∈ Sset, ∃ i, e i = σ := by
    intro σ hσ
    have : σ ∈ Set.range e := by
      rw [he, Finset.range_orderEmbOfFin]; exact hσ
    exact this
  have hSmem : ∀ r, sl φ r ∈ Sset := fun r => Finset.mem_image_of_mem _ (Finset.mem_univ r)
  -- the classes
  set P : Fin (d' + 1) → Finset (Fin n) :=
    fun i => Finset.univ.filter (fun r => sl φ r = e i) with hP
  have hPsl : ∀ i, ∀ r ∈ P i, sl φ r = e i := by
    intro i r hr; simpa [hP] using hr
  have hPne : ∀ i, (P i).Nonempty := by
    intro i
    have h := he_mem i
    rw [hSset, Finset.mem_image] at h
    obtain ⟨r, _, hr⟩ := h
    exact ⟨r, by simp [hP, hr]⟩
  have hPsum : ∑ i, (P i).card = n := by
    have hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j) := by
      intro i j hij
      rw [Finset.disjoint_left]
      intro r hri hrj
      apply hij
      apply e.injective
      rw [← hPsl i r hri, ← hPsl j r hrj]
    have hcov : Finset.univ.biUnion P = Finset.univ := by
      ext r
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, iff_true]
      obtain ⟨i, hi⟩ := he_range (sl φ r) (hSmem r)
      exact ⟨i, by simp [hP, hi]⟩
    rw [← Finset.card_biUnion (fun i _ j _ hij => hdisj i j hij), hcov]
    simp
  -- sum lines between consecutive classes, difference lines between the last and the first class
  set S : Fin d' → Finset (Option ℚ) := fun i =>
    ((P i.castSucc) ×ˢ (P i.succ)).image (fun pq => lineOf (φ pq.1 + φ pq.2)) with hS
  set W : Finset (Option ℚ) :=
    ((P (Fin.last d')) ×ˢ (P 0)).image (fun pq => lineOf (φ pq.1 - φ pq.2)) with hW
  have hlt : ∀ i : Fin d', e i.castSucc < e i.succ := fun i => e.strictMono (Fin.castSucc_lt_succ)
  have hlt0 : e 0 < e (Fin.last d') := e.strictMono (by
    rw [Fin.lt_def]; simp; omega)
  have hScard : ∀ i : Fin d', (P i.castSucc).card + (P i.succ).card ≤ (S i).card + 1 := by
    intro i
    have hA := al_injOn hα hinj (P i.castSucc) _ (hPsl i.castSucc)
    have hB := al_injOn hα hinj (P i.succ) _ (hPsl i.succ)
    have key := sum_count ((P i.castSucc).image (al φ)) ((P i.succ).image (al φ))
      (e i.castSucc) (e i.succ) (hlt i)
      (by intro x hx; obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hx; exact al_pos hα r)
      (by intro x hx; obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hx; exact al_pos hα r)
      ((hPne _).image _) ((hPne _).image _)
    rw [Finset.card_image_of_injOn hA, Finset.card_image_of_injOn hB] at key
    refine key.trans ?_
    have hsub : (((P i.castSucc).image (al φ) ×ˢ (P i.succ).image (al φ)).image
        (fun p => sumLab (e i.castSucc) (e i.succ) p.1 p.2)) ⊆ S i := by
      intro l hl
      obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hl
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
      refine Finset.mem_image.mpr ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, ?_⟩
      have h1 := hPsl i.castSucc p hp
      have h2 := hPsl i.succ q hq
      show lineOf (φ p + φ q) = _
      rw [lineOf_add hα, h1, h2]
    have := Finset.card_le_card hsub
    omega
  have hWcard : (P 0).card + (P (Fin.last d')).card ≤ W.card + 1 := by
    have hA := al_injOn hα hinj (P 0) _ (hPsl 0)
    have hB := al_injOn hα hinj (P (Fin.last d')) _ (hPsl (Fin.last d'))
    have key := dif_count ((P 0).image (al φ)) ((P (Fin.last d')).image (al φ))
      (e 0) (e (Fin.last d')) hlt0
      (by intro x hx; obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hx; exact al_pos hα r)
      (by intro x hx; obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hx; exact al_pos hα r)
      ((hPne _).image _) ((hPne _).image _)
    rw [Finset.card_image_of_injOn hA, Finset.card_image_of_injOn hB] at key
    refine key.trans ?_
    have hsub : (((P 0).image (al φ) ×ˢ (P (Fin.last d')).image (al φ)).image
        (fun p => difLab (e 0) (e (Fin.last d')) p.1 p.2)) ⊆ W := by
      intro l hl
      obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hl
      obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
      obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hy
      refine Finset.mem_image.mpr ⟨(p, q), Finset.mem_product.mpr ⟨hp, hq⟩, ?_⟩
      have h1 := hPsl (Fin.last d') p hp
      have h2 := hPsl 0 q hq
      show lineOf (φ p - φ q) = _
      rw [lineOf_sub hα, h1, h2]
    have := Finset.card_le_card hsub
    omega
  -- shapes of the labels
  have hSshape : ∀ i : Fin d', ∀ l ∈ S i, ∃ σ, l = some σ ∧ e i.castSucc < σ ∧ σ < e i.succ := by
    intro i l hl
    obtain ⟨⟨p, q⟩, hpq, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpq
    have h1 := hPsl i.castSucc p hp
    have h2 := hPsl i.succ q hq
    show ∃ σ, lineOf (φ p + φ q) = some σ ∧ _
    rw [lineOf_add hα, h1, h2]
    exact sumLab_mem_Ioo _ _ _ _ (hlt i) (al_pos hα p) (al_pos hα q)
  have hWshape : ∀ l ∈ W, l = none ∨ ∃ σ, l = some σ ∧ (σ < e 0 ∨ e (Fin.last d') < σ) := by
    intro l hl
    obtain ⟨⟨p, q⟩, hpq, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpq
    have h1 := hPsl (Fin.last d') p hp
    have h2 := hPsl 0 q hq
    show lineOf (φ p - φ q) = none ∨ ∃ σ, lineOf (φ p - φ q) = some σ ∧ _
    rw [lineOf_sub hα, h1, h2]
    exact difLab_out _ _ _ _ hlt0 (al_pos hα q) (al_pos hα p)
  -- the labels are repeat lines
  have hSrep : ∀ i : Fin d', S i ⊆ repeatLines φ := by
    intro i l hl
    obtain ⟨⟨p, q⟩, hpq, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpq
    have hne : p ≠ q := by
      intro h
      have h1 := hPsl i.castSucc p hp
      have h2 := hPsl i.succ q hq
      rw [h] at h1
      have := h1.symm.trans h2
      exact absurd (e.injective this) (Fin.castSucc_lt_succ.ne)
    exact Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨(p, q), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩, rfl⟩)
  have hWrep : W ⊆ repeatLines φ := by
    intro l hl
    obtain ⟨⟨p, q⟩, hpq, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpq
    have hne : p ≠ q := by
      intro h
      have h1 := hPsl (Fin.last d') p hp
      have h2 := hPsl 0 q hq
      rw [h] at h1
      have := h1.symm.trans h2
      have h3 := e.injective this
      have : (0 : Fin (d' + 1)) ≠ Fin.last d' := by
        intro h4
        have := congrArg Fin.val h4
        simp at this; omega
      exact this h3.symm
    exact Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨(p, q), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩, rfl⟩)
  -- the labels are not slopes of forms
  have hnotslope : ∀ l : Option ℚ, (∀ j, l ≠ some (e j)) → l ∉ slopeLabels φ := by
    intro l hl hmem
    rw [hlab, Finset.mem_image] at hmem
    obtain ⟨τ, hτ, rfl⟩ := hmem
    obtain ⟨j, hj⟩ := he_range τ hτ
    exact hl j (by rw [hj])
  have hSfree : ∀ i : Fin d', ∀ l ∈ S i, l ∉ slopeLabels φ := by
    intro i l hl
    obtain ⟨σ, rfl, h1, h2⟩ := hSshape i l hl
    apply hnotslope
    intro j hj
    have hσ : σ = e j := Option.some.inj hj
    rcases le_or_gt j i.castSucc with hle | hgt
    · have := e.monotone hle; linarith
    · have hle : i.succ ≤ j := Fin.castSucc_lt_iff_succ_le.mp hgt
      have := e.monotone hle; linarith
  have hWfree : ∀ l ∈ W, l ∉ slopeLabels φ := by
    intro l hl
    rcases hWshape l hl with rfl | ⟨σ, rfl, h⟩
    · apply hnotslope; intro j hj; exact absurd hj (by simp)
    · apply hnotslope
      intro j hj
      have hσ : σ = e j := Option.some.inj hj
      have h0 := e.monotone (Fin.zero_le j)
      have hl' := e.monotone (Fin.le_last j)
      rcases h with h | h <;> linarith
  -- disjointness
  have hdisjS : ∀ i ∈ (Finset.univ : Finset (Fin d')), ∀ j ∈ (Finset.univ : Finset (Fin d')),
      i ≠ j → Disjoint (S i) (S j) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro l hli hlj
    obtain ⟨σ, rfl, a1, a2⟩ := hSshape i l hli
    obtain ⟨σ', hσ', b1, b2⟩ := hSshape j _ hlj
    have : σ' = σ := (Option.some.inj hσ').symm
    subst this
    rcases lt_or_gt_of_ne hij with h | h
    · have h1 : i.succ ≤ j.castSucc := Fin.succ_le_castSucc_iff.mpr h
      have := e.monotone h1; linarith
    · have h1 : j.succ ≤ i.castSucc := Fin.succ_le_castSucc_iff.mpr h
      have := e.monotone h1; linarith
  have hdisjSW : Disjoint (Finset.univ.biUnion S) W := by
    rw [Finset.disjoint_left]
    intro l hl hlW
    rw [Finset.mem_biUnion] at hl
    obtain ⟨i, _, hli⟩ := hl
    obtain ⟨σ, rfl, a1, a2⟩ := hSshape i l hli
    have h0 := e.monotone (Fin.zero_le i.castSucc)
    have hl' := e.monotone (Fin.le_last i.succ)
    rcases hWshape _ hlW with h | ⟨σ', hσ', h⟩
    · exact absurd h (by simp)
    · have : σ' = σ := (Option.some.inj hσ').symm
      subst this
      rcases h with h | h <;> linarith
  have hT : (Finset.univ.biUnion S) ∪ W ⊆ freeRepeatLines φ := by
    intro l hl
    rw [Finset.mem_union] at hl
    unfold freeRepeatLines
    rw [Finset.mem_sdiff]
    rcases hl with hl | hl
    · rw [Finset.mem_biUnion] at hl
      obtain ⟨i, _, hli⟩ := hl
      exact ⟨hSrep i hli, hSfree i l hli⟩
    · exact ⟨hWrep hl, hWfree l hl⟩
  have hTcard : ((Finset.univ.biUnion S) ∪ W).card = ∑ i, (S i).card + W.card := by
    rw [Finset.card_union_of_disjoint hdisjSW, Finset.card_biUnion hdisjS]
  have hTle := Finset.card_le_card hT
  -- arithmetic
  have hcs : ∑ i : Fin d', (P i.castSucc).card + (P (Fin.last d')).card = n := by
    have h := hPsum
    rw [Fin.sum_univ_castSucc] at h
    exact h
  have hsc : (P 0).card + ∑ i : Fin d', (P i.succ).card = n := by
    have h := hPsum
    rw [Fin.sum_univ_succ] at h
    exact h
  have hsumS : ∑ i : Fin d', ((P i.castSucc).card + (P i.succ).card) ≤
      ∑ i : Fin d', ((S i).card + 1) := Finset.sum_le_sum (fun i _ => hScard i)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, mul_one] at hsumS
  rw [hd']
  omega

end Main

/-! ## Section 5: the general statement (reduction to the normalised form) -/

section General

variable {n : ℕ}

/-- The shear `(a, b) ↦ (a + N b, b)`: the form seen in the basis `(x, z)` with `x = (1, N)`. -/
def shear (N : ℤ) (v : Form) : Form := (v.1 + N * v.2, v.2)

/-- Its inverse. -/
def unshear (N : ℤ) (v : Form) : Form := (v.1 - N * v.2, v.2)

theorem unshear_shear (N : ℤ) (v : Form) : unshear N (shear N v) = v := by
  simp [unshear, shear]

theorem shear_unshear (N : ℤ) (v : Form) : shear N (unshear N v) = v := by
  simp [unshear, shear]

theorem cr_shear (N : ℤ) (u v : Form) : cr (shear N u) (shear N v) = cr u v := by
  simp only [cr, shear]; ring

theorem cr_unshear (N : ℤ) (u v : Form) : cr (unshear N u) (unshear N v) = cr u v := by
  simp only [cr, unshear]; ring

theorem lineOf_neg (v : Form) : lineOf (-v) = lineOf v := by
  unfold lineOf
  by_cases h : v.1 = 0
  · simp [h]
  · simp [h, neg_div_neg_eq]

theorem lineOf_ne_zero_of_cr {u v : Form} (h : cr u v ≠ 0) : u ≠ 0 := by
  intro hu; apply h; subst hu; simp [cr]

/-- The sign making the first coordinate of the sheared form positive. -/
def sgnOf (φ : Fin n → Form) (N : ℤ) (r : Fin n) : ℤ :=
  if 0 < (φ r).1 + N * (φ r).2 then 1 else -1

/-- The normalised forms `ε_r · shear φ_r`. -/
def normForms (φ : Fin n → Form) (N : ℤ) (r : Fin n) : Form :=
  (sgnOf φ N r * ((φ r).1 + N * (φ r).2), sgnOf φ N r * (φ r).2)

theorem sgnOf_cases (φ : Fin n → Form) (N : ℤ) (r : Fin n) :
    sgnOf φ N r = 1 ∨ sgnOf φ N r = -1 := by
  unfold sgnOf; split_ifs <;> simp

theorem normForms_pos (φ : Fin n → Form) (N : ℤ) (hN : ∀ r, (φ r).1 + N * (φ r).2 ≠ 0) (r : Fin n) :
    0 < (normForms φ N r).1 := by
  unfold normForms sgnOf
  simp only
  split_ifs with h
  · simpa using h
  · have := hN r
    have : (φ r).1 + N * (φ r).2 < 0 := by omega
    linarith

theorem unshear_normForms (φ : Fin n → Form) (N : ℤ) (r : Fin n) :
    unshear N (normForms φ N r) = (sgnOf φ N r * (φ r).1, sgnOf φ N r * (φ r).2) := by
  simp only [unshear, normForms]
  ext <;> simp <;> ring

theorem cr_normForms (φ : Fin n → Form) (N : ℤ) (r s : Fin n) :
    cr (normForms φ N r) (normForms φ N s) = sgnOf φ N r * sgnOf φ N s * cr (φ r) (φ s) := by
  simp only [cr, normForms]; ring

/-- The exact number of proportionality classes, via fibres. -/
theorem card_image_eq_fibres {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (f : α → β) :
    (Finset.univ.image f).card = (Finset.univ.image (fun a => Finset.univ.filter (fun b => f b = f a))).card := by
  have himg : Finset.univ.image (fun a => Finset.univ.filter (fun b => f b = f a)) =
      (Finset.univ.image f).image (fun l => Finset.univ.filter (fun b => f b = l)) := by
    rw [Finset.image_image]; rfl
  rw [himg]
  symm
  apply Finset.card_image_of_injOn
  intro l hl l' hl' h
  obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hl
  have : a ∈ (fun l => Finset.univ.filter (fun b => f b = l)) l' := by rw [← h]; simp
  simpa using this

/-- Number of classes is the same in original and normalised coordinates. -/
theorem slope_card_eq (φ : Fin n → Form) (N : ℤ) (hN : ∀ r, (φ r).1 + N * (φ r).2 ≠ 0)
    (hnz : ∀ r, φ r ≠ 0) :
    (slopeLabels (normForms φ N)).card = (slopeLabels φ).card := by
  have hnz' : ∀ r, normForms φ N r ≠ 0 := by
    intro r h
    have := normForms_pos φ N hN r
    rw [h] at this; simp at this
  have key : ∀ (ψ : Fin n → Form), (∀ r, ψ r ≠ 0) →
      (slopeLabels ψ).card = (Finset.univ.image (fun r => Finset.univ.filter (fun s => cr (ψ r) (ψ s) = 0))).card := by
    intro ψ hψ
    unfold slopeLabels
    rw [card_image_eq_fibres (fun r => lineOf (ψ r))]
    congr 1
    apply Finset.image_congr
    intro r _
    apply Finset.filter_congr
    intro s _
    exact eq_comm.trans (lineOf_eq_iff (hψ r) (hψ s))
  rw [key _ hnz', key _ hnz]
  congr 1
  apply Finset.image_congr
  intro r _
  apply Finset.filter_congr
  intro s _
  rw [cr_normForms]
  have h1 : sgnOf φ N r * sgnOf φ N s ≠ 0 := by
    rcases sgnOf_cases φ N r with h | h <;> rcases sgnOf_cases φ N s with h' | h' <;> simp [h, h']
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h h1
    · exact h
  · intro h; rw [h]; simp

end General

section General2

variable {n : ℕ}

theorem unshear_add (N : ℤ) (u v : Form) : unshear N (u + v) = unshear N u + unshear N v := by
  ext <;> simp [unshear] <;> ring

theorem unshear_sub (N : ℤ) (u v : Form) : unshear N (u - v) = unshear N u - unshear N v := by
  ext <;> simp [unshear] <;> ring

theorem unshear_eq_zero {N : ℤ} {w : Form} (h : unshear N w = 0) : w = 0 := by
  have := congrArg (shear N) h
  rw [shear_unshear] at this
  simpa [shear] using this

/-- A generic direction exists. -/
theorem exists_generic (φ : Fin n → Form) (hnz : ∀ r, φ r ≠ 0) :
    ∃ N : ℤ, ∀ r, (φ r).1 + N * (φ r).2 ≠ 0 := by
  classical
  obtain ⟨N, hN⟩ := Infinite.exists_notMem_finset
    (Finset.univ.image (fun r : Fin n => -(φ r).1 / (φ r).2))
  refine ⟨N, fun r h => ?_⟩
  by_cases hb : (φ r).2 = 0
  · apply hnz r
    have ha : (φ r).1 = 0 := by rw [hb] at h; simpa using h
    exact Prod.ext ha hb
  · apply hN
    rw [Finset.mem_image]
    refine ⟨r, Finset.mem_univ _, ?_⟩
    exact Int.ediv_eq_of_eq_mul_left hb (by linarith)

theorem normForms_injective (φ : Fin n → Form) (N : ℤ)
    (hdist : ∀ p q, p ≠ q → φ p ≠ φ q ∧ φ p ≠ -φ q) : Function.Injective (normForms φ N) := by
  intro p q h
  by_contra hpq
  have h' := congrArg (unshear N) h
  rw [unshear_normForms, unshear_normForms] at h'
  obtain ⟨hne1, hne2⟩ := hdist p q hpq
  rcases sgnOf_cases φ N p with hp | hp <;> rcases sgnOf_cases φ N q with hq | hq <;>
    rw [hp, hq] at h' <;>
    (have e1 := congrArg Prod.fst h'
     have e2 := congrArg Prod.snd h'
     dsimp only at e1 e2
     first
     | exact hne1 (Prod.ext (by linarith) (by linarith))
     | exact hne2 (Prod.ext (by simp only [Prod.fst_neg]; linarith)
         (by simp only [Prod.snd_neg]; linarith)))

/-- Membership of the sign-twisted combinations among the repeat lines. -/
theorem lineOf_mem_repeat (φ : Fin n → Form) (p q : Fin n) (hpq : p ≠ q) (e1 e2 : ℤ)
    (h1 : e1 = 1 ∨ e1 = -1) (h2 : e2 = 1 ∨ e2 = -1) :
    lineOf (e1 * (φ p).1 + e2 * (φ q).1, e1 * (φ p).2 + e2 * (φ q).2) ∈ repeatLines φ := by
  classical
  have hA : lineOf (φ p + φ q) ∈ repeatLines φ :=
    Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨(p, q), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpq⟩, rfl⟩)
  have hS : lineOf (φ p - φ q) ∈ repeatLines φ :=
    Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨(p, q), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpq⟩, rfl⟩)
  rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
  · have : ((1 : ℤ) * (φ p).1 + 1 * (φ q).1, 1 * (φ p).2 + 1 * (φ q).2) = φ p + φ q := by
      ext <;> simp
    rw [this]; exact hA
  · have : ((1 : ℤ) * (φ p).1 + -1 * (φ q).1, 1 * (φ p).2 + -1 * (φ q).2) = φ p - φ q := by
      ext <;> simp <;> ring
    rw [this]; exact hS
  · have : ((-1 : ℤ) * (φ p).1 + 1 * (φ q).1, -1 * (φ p).2 + 1 * (φ q).2) = -(φ p - φ q) := by
      ext <;> simp <;> ring
    rw [this, lineOf_neg]; exact hS
  · have : ((-1 : ℤ) * (φ p).1 + -1 * (φ q).1, -1 * (φ p).2 + -1 * (φ q).2) = -(φ p + φ q) := by
      ext <;> simp <;> ring
    rw [this, lineOf_neg]; exact hA

/-- The vectors whose lines are the repeat lines of `ψ`. -/
def Good (ψ : Fin n → Form) (w : Form) : Prop :=
  ∃ p q, p ≠ q ∧ (w = ψ p + ψ q ∨ w = ψ p - ψ q)

theorem repeat_shape (ψ : Fin n → Form) (ℓ : Option ℚ) (h : ℓ ∈ repeatLines ψ) :
    ∃ w, Good ψ w ∧ lineOf w = ℓ := by
  unfold repeatLines at h
  rcases Finset.mem_union.mp h with h | h
  · obtain ⟨⟨p, q⟩, hpq, rfl⟩ := Finset.mem_image.mp h
    exact ⟨ψ p + ψ q, ⟨p, q, (Finset.mem_filter.mp hpq).2, Or.inl rfl⟩, rfl⟩
  · obtain ⟨⟨p, q⟩, hpq, rfl⟩ := Finset.mem_image.mp h
    exact ⟨ψ p - ψ q, ⟨p, q, (Finset.mem_filter.mp hpq).2, Or.inr rfl⟩, rfl⟩

theorem good_ne_zero (φ : Fin n → Form) (N : ℤ) (hN : ∀ r, (φ r).1 + N * (φ r).2 ≠ 0)
    (hdist : ∀ p q, p ≠ q → φ p ≠ φ q ∧ φ p ≠ -φ q) {w : Form}
    (hw : Good (normForms φ N) w) : w ≠ 0 := by
  obtain ⟨p, q, hpq, h | h⟩ := hw
  · intro h0
    have h1 := normForms_pos φ N hN p
    have h2 := normForms_pos φ N hN q
    rw [h] at h0
    have := congrArg Prod.fst h0
    simp at this
    omega
  · intro h0
    rw [h] at h0
    exact hpq (normForms_injective φ N hdist (sub_eq_zero.mp h0))

theorem unshear_good (φ : Fin n → Form) (N : ℤ) {w : Form} (hw : Good (normForms φ N) w) :
    ∃ p q, p ≠ q ∧ ∃ e1 e2 : ℤ, (e1 = 1 ∨ e1 = -1) ∧ (e2 = 1 ∨ e2 = -1) ∧
      unshear N w = (e1 * (φ p).1 + e2 * (φ q).1, e1 * (φ p).2 + e2 * (φ q).2) := by
  obtain ⟨p, q, hpq, h | h⟩ := hw
  · refine ⟨p, q, hpq, sgnOf φ N p, sgnOf φ N q, sgnOf_cases φ N p, sgnOf_cases φ N q, ?_⟩
    rw [h, unshear_add, unshear_normForms, unshear_normForms]
    ext <;> simp
  · refine ⟨p, q, hpq, sgnOf φ N p, -sgnOf φ N q, sgnOf_cases φ N p, ?_, ?_⟩
    · rcases sgnOf_cases φ N q with h' | h' <;> simp [h']
    · rw [h, unshear_sub, unshear_normForms, unshear_normForms]
      ext <;> simp <;> ring

/-- Free repeat lines of the normalised forms inject into those of the original forms. -/
theorem free_card_le (φ : Fin n → Form) (hnz : ∀ r, φ r ≠ 0)
    (hdist : ∀ p q, p ≠ q → φ p ≠ φ q ∧ φ p ≠ -φ q) (N : ℤ)
    (hN : ∀ r, (φ r).1 + N * (φ r).2 ≠ 0) :
    (freeRepeatLines (normForms φ N)).card ≤ (freeRepeatLines φ).card := by
  classical
  set ψ := normForms φ N with hψ
  have hex : ∀ ℓ ∈ freeRepeatLines ψ, ∃ w, Good ψ w ∧ lineOf w = ℓ := by
    intro ℓ hℓ
    exact repeat_shape ψ ℓ (Finset.mem_sdiff.mp hℓ).1
  let G : Option ℚ → Option ℚ := fun ℓ =>
    if h : ∃ w, Good ψ w ∧ lineOf w = ℓ then lineOf (unshear N h.choose) else none
  have hG : ∀ ℓ ∈ freeRepeatLines ψ, ∃ w, Good ψ w ∧ lineOf w = ℓ ∧ G ℓ = lineOf (unshear N w) := by
    intro ℓ hℓ
    have h := hex ℓ hℓ
    refine ⟨h.choose, h.choose_spec.1, h.choose_spec.2, ?_⟩
    simp only [G, dif_pos h]
  have hψnz : ∀ w, Good ψ w → w ≠ 0 := fun w hw => good_ne_zero φ N hN hdist hw
  have hush : ∀ w, Good ψ w → unshear N w ≠ 0 := fun w hw h => hψnz w hw (unshear_eq_zero h)
  have hψr : ∀ r, ψ r ≠ 0 := by
    intro r h
    have := normForms_pos φ N hN r
    rw [← hψ] at this; rw [h] at this; simp at this
  refine Finset.card_le_card_of_injOn G ?_ ?_
  · intro ℓ hℓ
    obtain ⟨w, hw, hwl, hGl⟩ := hG ℓ hℓ
    rw [hGl]
    obtain ⟨p, q, hpq, e1, e2, h1, h2, hu⟩ := unshear_good φ N hw
    rw [Finset.mem_coe] at hℓ ⊢
    unfold freeRepeatLines
    rw [Finset.mem_sdiff]
    refine ⟨?_, ?_⟩
    · rw [hu]; exact lineOf_mem_repeat φ p q hpq e1 e2 h1 h2
    · intro hmem
      obtain ⟨r, _, hr⟩ := Finset.mem_image.mp hmem
      have hcr : cr (unshear N w) (φ r) = 0 :=
        (lineOf_eq_iff (hush w hw) (hnz r)).mp hr.symm
      have h3 : cr w (ψ r) = 0 := by
        have h4 : cr w (shear N (φ r)) = 0 := by
          have := cr_unshear N w (shear N (φ r))
          rw [unshear_shear] at this
          rw [← this]; exact hcr
        have : cr w (ψ r) = sgnOf φ N r * cr w (shear N (φ r)) := by
          simp only [cr, hψ, normForms, shear]; ring
        rw [this, h4]; simp
      have h5 : lineOf w = lineOf (ψ r) := (lineOf_eq_iff (hψnz w hw) (hψr r)).mpr h3
      apply (Finset.mem_sdiff.mp hℓ).2
      unfold slopeLabels
      exact Finset.mem_image.mpr ⟨r, Finset.mem_univ _, by rw [← h5, hwl]⟩
  · intro ℓ hℓ ℓ' hℓ' hGG
    obtain ⟨w, hw, hwl, hGl⟩ := hG ℓ hℓ
    obtain ⟨w', hw', hwl', hGl'⟩ := hG ℓ' hℓ'
    rw [hGl, hGl'] at hGG
    have h1 : cr (unshear N w) (unshear N w') = 0 :=
      (lineOf_eq_iff (hush w hw) (hush w' hw')).mp hGG
    rw [cr_unshear] at h1
    rw [← hwl, ← hwl']
    exact (lineOf_eq_iff (hψnz w hw) (hψnz w' hw')).mpr h1

/-- **Cone lemma (free repeat lines of a 2-torus).**  Let `φ_1, ..., φ_n` be nonzero integer forms,
pairwise distinct up to sign, falling in `d ≥ 2` proportionality classes (equivalently, the lines
`ker φ_r`).  Then the number of free repeat lines `ker (φ_p ± φ_q) ∖ {ker φ_r}` is at least `2 n - d`
(stated as `2 n ≤ #free + d`). -/
theorem cone_lemma (φ : Fin n → Form) (hnz : ∀ r, φ r ≠ 0)
    (hdist : ∀ p q, p ≠ q → φ p ≠ φ q ∧ φ p ≠ -φ q) (hd : 2 ≤ (slopeLabels φ).card) :
    2 * n ≤ (freeRepeatLines φ).card + (slopeLabels φ).card := by
  obtain ⟨N, hN⟩ := exists_generic φ hnz
  have h1 := slope_card_eq φ N hN hnz
  have h2 := cone_lemma_normalised (φ := normForms φ N) (normForms_pos φ N hN)
    (normForms_injective φ N hdist) (by rw [h1]; exact hd)
  have h3 := free_card_le φ hnz hdist N hN
  rw [h1] at h2
  omega

end General2

/-! ## Section 6: sharpness on `A2` -/

/-- The forms `A, B, A+B` of the `A2` torus: `n = 3`, `d = 3`, exactly `2 n - d = 3` free repeat lines. -/
def A2forms : Fin 3 → Form := ![(1, 0), (0, 1), (1, 1)]

theorem A2_free_card : (freeRepeatLines A2forms).card = 3 := by
  decide +kernel

theorem A2_slope_card : (slopeLabels A2forms).card = 3 := by
  decide +kernel

end ObsConeLemma
end LRSpectrumFull
