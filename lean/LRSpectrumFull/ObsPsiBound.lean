/-
# Theorem PSI: torsion points of a 2-torus with primitive characters

Formalisation of Theorem PSI (Theorem 4 of the accompanying note) and its corollaries, over the 2-torus loneliness function `torusML` of `ObsRootTorus`.

Setting: `n = k+1` integer forms `φ_r = (g1 r, g2 r)` and a level `N ≥ 1`.  A form has *content coprime
to `N`* if `gcd (gcd (g1 r) (g2 r)) N = 1`.

Core mechanism (torsion points of order `N`): a form with content coprime to `N` has a cyclic kernel of
order `N` in `(ℤ/N)²`, so it kills at most one point of the projective line `P¹(ℤ/N)`.  Two integer
vectors `c, c'` killed by the same such form satisfy `N ∣ det(c, c')` (`det_dvd_of_both_kill`).  Hence a
family of vectors with pairwise `N ∤ det` and with more members than there are forms contains a vector
killed by no form (`exists_unkilled`), and at that vector `c`, the point `c / N` of the parameter plane
has every form value at distance `≥ 1/N` from `ℤ` (`torusGap_ge_of_unkilled`).

Results:

* `torusML_ge_inv_of_projReps`   : `n < |projReps N|`  ⟹  `1/N ≤ torusML`, where `projReps N` is a set of
  representatives of the points of the projective line over `ℤ/N` (the cyclic subgroups of order `N`);
  its cardinality is the Dedekind psi function `ψ(N)` (checked by `decide` against a divisor-sum formula
  for `N ≤ 12`, see `card_projReps_eq_psiDed_*`); the identification for all `N` is NOT proved here.
* `torusML_ge_inv_of_two_mul_sub_totient` : `n < 2N − φ(N)`  ⟹  `1/N ≤ torusML`   (all `N`, explicit set).
* `torusML_gt_inv_of_primitive`  : primitive, `n ≥ 5`, `n ≠ 6`  ⟹  `1/n < torusML`   (all `n`).
* `primitive_critical_card`      : primitive and `torusML = 1/n`  ⟹  `n ∈ {2,3,4,6}`.
* `primitive_totient_two`        : primitive, `n ≥ 3`, loneliness `≤ 1/n` everywhere ⟹ `φ(n) = 2`.
* `torusML_A2_primitive` etc.     : A2, B2, G2 are primitive with `torusML = 1/n`, so the bound is sharp.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.ObsRootTorus
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace LRSpectrumFull
namespace ObsPsiBound

open ObsRootTorus

/-! ## Section 1: residues, and the gap at a torsion point -/

/-- A nonzero residue mod `N` puts `c / N` at distance at least `1/N` from the integers. -/
theorem nd_div_ge (c : ℤ) (N : ℕ) (hN : 0 < N) (h : ¬ (N : ℤ) ∣ c) :
    1 / (N : ℝ) ≤ nearestIntDist ((c : ℝ) / N) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hdiv := Int.emod_add_mul_ediv c N
  have hlt : c % (N : ℤ) < N := Int.emod_lt_of_pos c (by exact_mod_cast hN)
  have hne : c % (N : ℤ) ≠ 0 := fun h0 => h (Int.dvd_of_emod_eq_zero h0)
  have hge : 0 ≤ c % (N : ℤ) := Int.emod_nonneg c (by exact_mod_cast hN.ne')
  have h1 : 1 ≤ c % (N : ℤ) := by omega
  have e : (c : ℝ) / N = ((c % (N : ℤ) : ℤ) : ℝ) / N + ((c / (N : ℤ) : ℤ) : ℝ) := by
    have : (c : ℝ) = ((c % (N : ℤ) : ℤ) : ℝ) + N * ((c / (N : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast hdiv.symm
    rw [this]; field_simp
  rw [e, nearestIntDist_add_int]
  have h1R : (1 : ℝ) ≤ ((c % (N : ℤ) : ℤ) : ℝ) := by exact_mod_cast h1
  have hltR : ((c % (N : ℤ) : ℤ) : ℝ) < (N : ℝ) := by exact_mod_cast hlt
  apply nearestIntDist_ge
  · positivity
  · rw [div_lt_one hNR]; exact hltR
  · exact div_le_div_of_nonneg_right h1R hNR.le
  · rw [le_sub_iff_add_le, ← add_div, div_le_one hNR]
    have : ((c % (N : ℤ) : ℤ) : ℝ) ≤ (N : ℝ) - 1 := by
      have : c % (N : ℤ) ≤ (N : ℤ) - 1 := by omega
      exact_mod_cast this
    linarith

/-- If no form value `g1 r * x + g2 r * y` is divisible by `N`, the point `(x/N, y/N)` has gap `≥ 1/N`. -/
theorem torusGap_ge_of_unkilled {k : ℕ} (g1 g2 : Fin (k + 1) → ℤ) (N : ℕ) (hN : 0 < N) (x y : ℤ)
    (h : ∀ r, ¬ (N : ℤ) ∣ g1 r * x + g2 r * y) :
    1 / (N : ℝ) ≤ torusGap g1 g2 ((x : ℝ) / N) ((y : ℝ) / N) := by
  apply le_torusGap
  intro i
  have e : (g1 i : ℝ) * ((x : ℝ) / N) + (g2 i : ℝ) * ((y : ℝ) / N) =
      ((g1 i * x + g2 i * y : ℤ) : ℝ) / N := by push_cast; ring
  rw [e]
  exact nd_div_ge _ N hN (h i)

theorem torusML_ge_of_unkilled {k : ℕ} (g1 g2 : Fin (k + 1) → ℤ) (N : ℕ) (hN : 0 < N) (x y : ℤ)
    (h : ∀ r, ¬ (N : ℤ) ∣ g1 r * x + g2 r * y) : 1 / (N : ℝ) ≤ torusML g1 g2 :=
  (torusGap_ge_of_unkilled g1 g2 N hN x y h).trans
    (le_csSup (bddAbove_range_torusGap g1 g2) ⟨((x : ℝ) / N, (y : ℝ) / N), rfl⟩)

/-! ## Section 2: forms with content coprime to `N` kill at most one point of `P¹(ℤ/N)` -/

/-- The content `gcd (a, b)` is coprime to `N`. -/
def ContentCoprime (a b : ℤ) (N : ℕ) : Prop := Nat.Coprime (Int.gcd a b) N

/-- Primitive characters: every content is `1`. -/
def Primitive {k : ℕ} (g1 g2 : Fin (k + 1) → ℤ) : Prop := ∀ r, Int.gcd (g1 r) (g2 r) = 1

theorem contentCoprime_of_primitive {a b : ℤ} (h : Int.gcd a b = 1) (N : ℕ) : ContentCoprime a b N := by
  unfold ContentCoprime; rw [h]; exact Nat.coprime_one_left N

/-- Bezout for the pair `(a, b)` modulo `N`. -/
theorem bezout_of_contentCoprime {a b : ℤ} {N : ℕ} (h : ContentCoprime a b N) :
    ∃ u v z : ℤ, u * a + v * b + (N : ℤ) * z = 1 := by
  have hc : IsCoprime ((Int.gcd a b : ℕ) : ℤ) (N : ℤ) := Nat.isCoprime_iff_coprime.mpr h
  obtain ⟨w, z, hwz⟩ := hc
  refine ⟨w * Int.gcdA a b, w * Int.gcdB a b, z, ?_⟩
  have h0 := Int.gcd_eq_gcd_ab a b
  rw [h0] at hwz
  linear_combination hwz

/-- **Torsion-point lemma.**  Two integer vectors killed (mod `N`) by the same form of content coprime to
`N` have determinant divisible by `N`: they lie on the same cyclic subgroup. -/
theorem det_dvd_of_both_kill {N : ℕ} {a b x1 y1 x2 y2 : ℤ} (hc : ContentCoprime a b N)
    (h1 : (N : ℤ) ∣ a * x1 + b * y1) (h2 : (N : ℤ) ∣ a * x2 + b * y2) :
    (N : ℤ) ∣ x1 * y2 - x2 * y1 := by
  obtain ⟨u, v, z, huv⟩ := bezout_of_contentCoprime hc
  set D := x1 * y2 - x2 * y1 with hD
  have haD : (N : ℤ) ∣ a * D := by
    have e : a * D = y2 * (a * x1 + b * y1) - y1 * (a * x2 + b * y2) := by rw [hD]; ring
    rw [e]; exact dvd_sub (dvd_mul_of_dvd_right h1 _) (dvd_mul_of_dvd_right h2 _)
  have hbD : (N : ℤ) ∣ b * D := by
    have e : b * D = x1 * (a * x2 + b * y2) - x2 * (a * x1 + b * y1) := by rw [hD]; ring
    rw [e]; exact dvd_sub (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_right h1 _)
  have e : D = u * (a * D) + v * (b * D) + (N : ℤ) * (z * D) := by
    linear_combination (-D) * huv
  rw [e]
  exact dvd_add (dvd_add (dvd_mul_of_dvd_right haD _) (dvd_mul_of_dvd_right hbD _))
    (dvd_mul_right _ _)

/-- Pigeonhole: a family of more than `n` pairwise independent vectors (`N ∤ det`) contains a vector
killed by none of `n` forms of content coprime to `N`. -/
theorem exists_unkilled {ι : Type*} {n : ℕ} (N : ℕ) (a b : Fin n → ℤ)
    (hc : ∀ r, ContentCoprime (a r) (b r) N) (C : Finset ι) (vec : ι → ℤ × ℤ)
    (hC : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' →
      ¬ (N : ℤ) ∣ (vec c).1 * (vec c').2 - (vec c').1 * (vec c).2)
    (hn : n < C.card) : ∃ c ∈ C, ∀ r, ¬ (N : ℤ) ∣ a r * (vec c).1 + b r * (vec c).2 := by
  by_contra hcon
  push Not at hcon
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · obtain ⟨c, hc'⟩ := Finset.card_pos.mp (by omega : 0 < C.card)
    obtain ⟨r, _⟩ := hcon c hc'
    exact r.elim0
  · haveI : Nonempty (Fin n) := ⟨⟨0, hpos⟩⟩
    choose! f hf using hcon
    obtain ⟨c, hc1, c', hc2, hne, heq⟩ :=
      Finset.exists_ne_map_eq_of_card_lt_of_maps_to (s := C) (t := (Finset.univ : Finset (Fin n)))
        (by simpa using hn) (f := f) (fun c _ => Finset.mem_univ _)
    apply hC c hc1 c' hc2 hne
    have h1 := hf c hc1
    have h2 := hf c' hc2
    rw [heq] at h1
    exact det_dvd_of_both_kill (hc (f c')) h1 h2

/-- **Master bound.** A pairwise independent family `C` with more members than forms gives
`1/N ≤ torusML`. -/
theorem torusML_ge_inv_of_indep {ι : Type*} {k : ℕ} (g1 g2 : Fin (k + 1) → ℤ) (N : ℕ) (hN : 0 < N)
    (hc : ∀ r, ContentCoprime (g1 r) (g2 r) N) (C : Finset ι) (vec : ι → ℤ × ℤ)
    (hC : ∀ c ∈ C, ∀ c' ∈ C, c ≠ c' →
      ¬ (N : ℤ) ∣ (vec c).1 * (vec c').2 - (vec c').1 * (vec c).2)
    (hn : k + 1 < C.card) : 1 / (N : ℝ) ≤ torusML g1 g2 := by
  obtain ⟨c, _, hc2⟩ := exists_unkilled N g1 g2 hc C vec hC hn
  exact torusML_ge_of_unkilled g1 g2 N hN (vec c).1 (vec c).2 hc2

/-! ## Section 3: the explicit family of size `2N - φ(N)` -/

/-- The points `(1, j)`, `j ∈ [0,N)`, and `(a, 1)`, `a ∈ [0,N)` a non-unit mod `N`. -/
def candC (N : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range N).image (fun j : ℕ => ((1 : ℤ), (j : ℤ))) ∪
  ((Finset.range N).filter (fun a => ¬ Nat.Coprime N a)).image (fun a : ℕ => ((a : ℤ), (1 : ℤ)))

theorem card_candC (N : ℕ) : (candC N).card = 2 * N - Nat.totient N := by
  have hinj1 : Function.Injective (fun j : ℕ => ((1 : ℤ), (j : ℤ))) := by
    intro j j' h; simpa using h
  have hinj2 : Function.Injective (fun a : ℕ => ((a : ℤ), (1 : ℤ))) := by
    intro j j' h; simpa using h
  unfold candC
  rw [Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective _ hinj1, Finset.card_image_of_injective _ hinj2,
      Finset.card_range]
    have h2 := Finset.card_filter_add_card_filter_not (s := Finset.range N)
      (fun a => Nat.Coprime N a)
    rw [Finset.card_range] at h2
    rw [Nat.totient_eq_card_coprime]
    omega
  · rw [Finset.disjoint_left]
    intro p hp1 hp2
    simp only [Finset.mem_image, Finset.mem_range, Finset.mem_filter] at hp1 hp2
    obtain ⟨j, _, rfl⟩ := hp1
    obtain ⟨a, ⟨_, hna⟩, hpa⟩ := hp2
    have h1 : (a : ℤ) = 1 := by simpa using congrArg Prod.fst hpa
    have : a = 1 := by exact_mod_cast h1
    exact hna (by rw [this]; exact Nat.coprime_one_right N)

theorem candC_indep (N : ℕ) (hN : 0 < N) :
    ∀ c ∈ candC N, ∀ c' ∈ candC N, c ≠ c' → ¬ (N : ℤ) ∣ c.1 * c'.2 - c'.1 * c.2 := by
  intro c hc c' hc' hne hdvd
  unfold candC at hc hc'
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_range] at hc hc'
  have key : ∀ x : ℤ, (N : ℤ) ∣ x → |x| < N → x = 0 := fun x h1 h2 => Int.eq_zero_of_abs_lt_dvd h1 h2
  have unit_of : ∀ (a j : ℕ), (N : ℤ) ∣ 1 - (a : ℤ) * j → Nat.Coprime N a := by
    intro a j h
    obtain ⟨q, hq⟩ := h
    have hic : IsCoprime (a : ℤ) (N : ℤ) := ⟨j, q, by linarith⟩
    exact (Nat.isCoprime_iff_coprime.mp hic).symm
  rcases hc with ⟨j, hj, rfl⟩ | ⟨a, ⟨ha, hna⟩, rfl⟩ <;>
    rcases hc' with ⟨j', hj', rfl⟩ | ⟨a', ⟨ha', hna'⟩, rfl⟩
  · -- (1,j), (1,j')
    have h0 := key (((j' : ℤ)) - j) (by simpa using hdvd) (abs_lt.mpr ⟨by omega, by omega⟩)
    apply hne
    have : j' = j := by omega
    rw [this]
  · -- (1,j), (a',1)
    apply hna' (unit_of a' j (by simpa using hdvd))
  · -- (a,1), (1,j')
    apply hna (unit_of a j' (by
      have : (N : ℤ) ∣ -((a : ℤ) * j' - 1) := (dvd_neg).mpr (by simpa using hdvd)
      simpa using this))
  · -- (a,1), (a',1)
    have h0 := key (((a : ℤ)) - a') (by simpa using hdvd) (abs_lt.mpr ⟨by omega, by omega⟩)
    apply hne
    have : a = a' := by omega
    rw [this]

/-- **Theorem PSI, explicit form.**  `n < 2N - φ(N)` forms with content coprime to `N` leave a torsion
point of level `N`: `1/N ≤ torusML`. -/
theorem torusML_ge_inv_of_two_mul_sub_totient {k : ℕ} (g1 g2 : Fin (k + 1) → ℤ) (N : ℕ) (hN : 0 < N)
    (hc : ∀ r, ContentCoprime (g1 r) (g2 r) N) (hn : k + 1 < 2 * N - Nat.totient N) :
    1 / (N : ℝ) ≤ torusML g1 g2 := by
  refine torusML_ge_inv_of_indep g1 g2 N hN hc (candC N) id ?_ (by rw [card_candC]; exact hn)
  intro c hc0 c' hc1 hne
  exact candC_indep N hN c hc0 c' hc1 hne

/-! ## Section 4: arithmetic of `φ` and the existence of a level below `n` -/

theorem totient_add_le (N : ℕ) (S : Finset ℕ) (hS : S ⊆ Finset.range N)
    (hbad : ∀ s ∈ S, ¬ Nat.Coprime N s) : Nat.totient N + S.card ≤ N := by
  have hdisj : Disjoint ((Finset.range N).filter (fun a => Nat.Coprime N a)) S := by
    rw [Finset.disjoint_left]
    intro a ha hS'
    exact hbad a hS' (Finset.mem_filter.mp ha).2
  have h1 := Finset.card_union_of_disjoint hdisj
  have hsub : (Finset.range N).filter (fun a => Nat.Coprime N a) ∪ S ⊆ Finset.range N :=
    Finset.union_subset (Finset.filter_subset _ _) hS
  have h2 := Finset.card_le_card hsub
  rw [Finset.card_range] at h2
  rw [Nat.totient_eq_card_coprime]
  omega

/-- For composite `N`, `φ(N) + 2 ≤ N` (the non-units include `0` and a proper divisor). -/
theorem totient_add_two_le (N : ℕ) (h2 : 2 ≤ N) (hnp : ¬ N.Prime) : Nat.totient N + 2 ≤ N := by
  obtain ⟨m, hm, hm2, hmlt⟩ := Nat.exists_dvd_of_not_prime2 h2 hnp
  have h := totient_add_le N {0, m}
    (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> simp only [Finset.mem_range] <;> omega)
    (by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl
      · intro hcop
        have : N = 1 := by have h0 : Nat.gcd N 0 = 1 := hcop; rwa [Nat.gcd_zero_right] at h0
        omega
      · intro hcop
        have := Nat.Coprime.eq_one_of_dvd hcop.symm hm
        omega)
  rw [Finset.card_pair (by omega : (0 : ℕ) ≠ m)] at h
  exact h

/-- For even `N ≥ 6`, `φ(N) + 3 ≤ N` (the non-units include `0, 2, 4`). -/
theorem totient_add_three_le (N : ℕ) (h6 : 6 ≤ N) (hev : 2 ∣ N) : Nat.totient N + 3 ≤ N := by
  have h := totient_add_le N {0, 2, 4}
    (by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> simp only [Finset.mem_range] <;> omega)
    (by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl | rfl
      · intro hcop
        have : N = 1 := by have h0 : Nat.gcd N 0 = 1 := hcop; rwa [Nat.gcd_zero_right] at h0
        omega
      · intro hcop
        have := Nat.Coprime.eq_one_of_dvd hcop.symm hev
        omega
      · intro hcop
        have h2 : Nat.Coprime N 2 := Nat.Coprime.coprime_dvd_right (by norm_num) hcop
        have := Nat.Coprime.eq_one_of_dvd h2.symm hev
        omega)
  have hc : ({0, 2, 4} : Finset ℕ).card = 3 := by decide
  rw [hc] at h
  exact h

/-- For `n ≥ 5`, `n ≠ 6` there is a level `N < n` with `n < 2N - φ(N)`. -/
theorem exists_level (n : ℕ) (h5 : 5 ≤ n) (h6 : n ≠ 6) :
    ∃ N, 0 < N ∧ N < n ∧ n < 2 * N - Nat.totient N := by
  by_cases hp : (n - 1).Prime
  · have hn5 : n ≠ 5 := by
      rintro rfl; exact absurd hp (by decide)
    have hn7 : n ≠ 7 := by
      rintro rfl; exact absurd hp (by decide)
    have hodd : (n - 1) % 2 = 1 := by
      rcases hp.eq_two_or_odd with h | h
      · omega
      · exact h
    have hev : 2 ∣ n - 2 := by omega
    have h3 := totient_add_three_le (n - 2) (by omega) hev
    exact ⟨n - 2, by omega, by omega, by omega⟩
  · have h2 := totient_add_two_le (n - 1) (by omega) hp
    exact ⟨n - 1, by omega, by omega, by omega⟩

/-! ## Section 5: consequences for primitive tori, all `n` -/

/-- **Corollary 2 (all `n`).**  A 2-torus with primitive characters and `n ≥ 5`, `n ≠ 6` forms has
`1/n < torusML`. -/
theorem torusML_gt_inv_of_primitive {k : ℕ} (g1 g2 : Fin (k + 1) → ℤ) (hp : Primitive g1 g2)
    (h5 : 5 ≤ k + 1) (h6 : k + 1 ≠ 6) : 1 / ((k + 1 : ℕ) : ℝ) < torusML g1 g2 := by
  obtain ⟨N, hN0, hNn, hlt⟩ := exists_level (k + 1) h5 h6
  have h := torusML_ge_inv_of_two_mul_sub_totient g1 g2 N hN0
    (fun r => contentCoprime_of_primitive (hp r) N) hlt
  have h2 : 1 / ((k + 1 : ℕ) : ℝ) < 1 / (N : ℝ) :=
    one_div_lt_one_div_of_lt (by exact_mod_cast hN0) (by exact_mod_cast hNn)
  linarith

theorem torusML_le_half {k : ℕ} (g1 g2 : Fin (k + 1) → ℤ) : torusML g1 g2 ≤ 1 / 2 := by
  unfold torusML
  exact csSup_le ⟨_, ⟨(0, 0), rfl⟩⟩ (by rintro y ⟨p, rfl⟩; exact torusGap_le_half g1 g2 p.1 p.2)

/-- **Critical primitive tori exist only for `n ∈ {2,3,4,6}`.** -/
theorem primitive_critical_card {k : ℕ} (g1 g2 : Fin (k + 1) → ℤ) (hp : Primitive g1 g2)
    (hM : torusML g1 g2 = 1 / ((k + 1 : ℕ) : ℝ)) :
    k + 1 = 2 ∨ k + 1 = 3 ∨ k + 1 = 4 ∨ k + 1 = 6 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h2, h3, h4, h6⟩ := hcon
  rcases Nat.lt_or_ge (k + 1) 5 with hlt | hge
  · have hk1 : k + 1 = 1 := by omega
    have := torusML_le_half g1 g2
    rw [hM, hk1] at this
    norm_num at this
  · have := torusML_gt_inv_of_primitive g1 g2 hp hge h6
    rw [hM] at this
    exact lt_irrefl _ this

/-- **Composition with the crystallographic lemma.**  A primitive torus with `n ≥ 3` forms whose
loneliness never exceeds `1/n` has `φ(n) = 2`, with no special vector `w` and no non-proportionality
hypothesis (compare `ObsCrystallographic.crystallographic_lemma`). -/
theorem primitive_totient_two {k : ℕ} (g1 g2 : Fin (k + 1) → ℤ) (hp : Primitive g1 g2)
    (h3 : 3 ≤ k + 1) (hM : ∀ s t, torusGap g1 g2 s t ≤ 1 / ((k + 1 : ℕ) : ℝ)) :
    Nat.totient (k + 1) = 2 := by
  have hle : torusML g1 g2 ≤ 1 / ((k + 1 : ℕ) : ℝ) := by
    unfold torusML
    exact csSup_le ⟨_, ⟨(0, 0), rfl⟩⟩ (by rintro y ⟨p, rfl⟩; exact hM p.1 p.2)
  by_cases hbad : 5 ≤ k + 1 ∧ k + 1 ≠ 6
  · have := torusML_gt_inv_of_primitive g1 g2 hp hbad.1 hbad.2
    linarith
  · have : k + 1 = 3 ∨ k + 1 = 4 ∨ k + 1 = 6 := by omega
    rcases this with h | h | h <;> rw [h] <;> decide

/-! ## Section 6: sharpness, A2, B2, G2 are primitive and attain `1/n` -/

theorem A2_primitive : Primitive A2g1 A2g2 := by intro r; fin_cases r <;> decide
theorem B2_primitive : Primitive B2g1 B2g2 := by intro r; fin_cases r <;> decide
theorem G2_primitive : Primitive G2g1 G2g2 := by intro r; fin_cases r <;> decide

theorem torusML_A2_primitive : Primitive A2g1 A2g2 ∧ torusML A2g1 A2g2 = 1 / ((3 : ℕ) : ℝ) := by
  refine ⟨A2_primitive, ?_⟩; rw [torusML_A2]; norm_num
theorem torusML_B2_primitive : Primitive B2g1 B2g2 ∧ torusML B2g1 B2g2 = 1 / ((4 : ℕ) : ℝ) := by
  refine ⟨B2_primitive, ?_⟩; rw [torusML_B2]; norm_num
theorem torusML_G2_primitive : Primitive G2g1 G2g2 ∧ torusML G2g1 G2g2 = 1 / ((6 : ℕ) : ℝ) := by
  refine ⟨G2_primitive, ?_⟩; rw [torusML_G2]; norm_num

/-! ## Section 7: the full projective line, `|P¹(ℤ/N)| = ψ(N)` -/

/-- Representatives of the points of the projective line over `ℤ/N`: unimodular pairs `(x,y)` in
`[0,N)²` that are lexicographically least in their class (no earlier unimodular `c'` with
`N ∣ det(c', c)`).  Its cardinality is the number of cyclic subgroups of order `N` of `(ℤ/N)²`. -/
def projReps (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range N ×ˢ Finset.range N).filter (fun c =>
    Nat.gcd (Nat.gcd c.1 c.2) N = 1 ∧
    ∀ c' ∈ Finset.range N ×ˢ Finset.range N,
      (c'.1 < c.1 ∨ (c'.1 = c.1 ∧ c'.2 < c.2)) →
        Nat.gcd (Nat.gcd c'.1 c'.2) N = 1 → ¬ (c'.1 * c.2 % N = c.1 * c'.2 % N))

/-- The Dedekind psi function as a divisor sum over square-free divisors:
`ψ(N) = Σ_{d ∣ N, d squarefree} N / d = N ∏_{p ∣ N} (1 + 1/p)`. -/
def psiDed (N : ℕ) : ℕ :=
  ∑ d ∈ N.divisors, if (∀ e ∈ d.divisors, e * e ∣ d → e = 1) then N / d else 0

theorem det_dvd_iff (N : ℕ) (c c' : ℕ × ℕ) :
    (N : ℤ) ∣ (c.1 : ℤ) * c'.2 - (c'.1 : ℤ) * c.2 ↔ c'.1 * c.2 % N = c.1 * c'.2 % N := by
  have h := @Nat.modEq_iff_dvd N (c'.1 * c.2) (c.1 * c'.2)
  push_cast at h
  exact h.symm

theorem projReps_indep (N : ℕ) :
    ∀ c ∈ projReps N, ∀ c' ∈ projReps N, c ≠ c' →
      ¬ (N : ℤ) ∣ ((c.1 : ℤ), (c.2 : ℤ)).1 * ((c'.1 : ℤ), (c'.2 : ℤ)).2 -
        ((c'.1 : ℤ), (c'.2 : ℤ)).1 * ((c.1 : ℤ), (c.2 : ℤ)).2 := by
  intro c hc c' hc' hne
  simp only [det_dvd_iff]
  unfold projReps at hc hc'
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hc hc'
  obtain ⟨⟨hc1, hc2⟩, hcu, hcmin⟩ := hc
  obtain ⟨⟨hc1', hc2'⟩, hcu', hcmin'⟩ := hc'
  have hne' : c.1 ≠ c'.1 ∨ c.2 ≠ c'.2 := by
    by_contra h
    push Not at h
    exact hne (Prod.ext h.1 h.2)
  rcases lt_trichotomy c.1 c'.1 with h | h | h
  · -- c lex-less than c'
    exact fun heq => hcmin' c ⟨hc1, hc2⟩ (Or.inl h) hcu heq.symm
  · have h2 : c.2 ≠ c'.2 := by rcases hne' with h' | h' <;> omega
    rcases lt_or_gt_of_ne h2 with h3 | h3
    · exact fun heq => hcmin' c ⟨hc1, hc2⟩ (Or.inr ⟨h, h3⟩) hcu heq.symm
    · intro heq
      exact hcmin c' ⟨hc1', hc2'⟩ (Or.inr ⟨h.symm, h3⟩) hcu' heq
  · intro heq
    exact hcmin c' ⟨hc1', hc2'⟩ (Or.inl h) hcu' heq

/-- **Theorem PSI (torsion points, full projective line).**  If `n < |P¹(ℤ/N)| = ψ(N)` forms have
content coprime to `N`, then `1/N ≤ torusML`. -/
theorem torusML_ge_inv_of_projReps {k : ℕ} (g1 g2 : Fin (k + 1) → ℤ) (N : ℕ) (hN : 0 < N)
    (hc : ∀ r, ContentCoprime (g1 r) (g2 r) N) (hn : k + 1 < (projReps N).card) :
    1 / (N : ℝ) ≤ torusML g1 g2 :=
  torusML_ge_inv_of_indep g1 g2 N hN hc (projReps N) (fun c => ((c.1 : ℤ), (c.2 : ℤ)))
    (projReps_indep N) hn

/-! ### Cardinalities (`decide +kernel`, no `native_decide`) -/

theorem card_projReps_2 : (projReps 2).card = 3 := by decide +kernel
theorem card_projReps_3 : (projReps 3).card = 4 := by decide +kernel
theorem card_projReps_4 : (projReps 4).card = 6 := by decide +kernel
theorem card_projReps_5 : (projReps 5).card = 6 := by decide +kernel
theorem card_projReps_6 : (projReps 6).card = 12 := by decide +kernel
theorem card_projReps_7 : (projReps 7).card = 8 := by decide +kernel
theorem card_projReps_8 : (projReps 8).card = 12 := by decide +kernel
theorem card_projReps_9 : (projReps 9).card = 12 := by decide +kernel
theorem card_projReps_10 : (projReps 10).card = 18 := by decide +kernel
theorem card_projReps_11 : (projReps 11).card = 12 := by decide +kernel
theorem card_projReps_12 : (projReps 12).card = 24 := by decide +kernel

theorem card_projReps_eq_psiDed_le_12 :
    ∀ N ∈ Finset.Icc 1 12, (projReps N).card = psiDed N := by decide +kernel

/-- Primitive tori with `n ≤ 11` forms: `torusML ≥ 1/6` (psi(6) = 12). -/
theorem torusML_ge_one_sixth_of_primitive {k : ℕ} (g1 g2 : Fin (k + 1) → ℤ) (hp : Primitive g1 g2)
    (hk : k + 1 ≤ 11) : 1 / ((6 : ℕ) : ℝ) ≤ torusML g1 g2 :=
  torusML_ge_inv_of_projReps g1 g2 6 (by norm_num)
    (fun r => contentCoprime_of_primitive (hp r) 6) (by rw [card_projReps_6]; omega)

end ObsPsiBound
end LRSpectrumFull
