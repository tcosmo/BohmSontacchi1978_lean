/-
  Bohm-Sontacchi 1978 -- Proposition 6

  PROPOSITION 6. For all x in Z with u^n(x) = x we have |x| < 3^n.

  Proof sketch: From Proposition 5, |x| <= sum_{k=0}^{m-1} 3^{m-k-1} * 2^{v_k}
  where the v_i satisfy v_{i-1} < v_i and v_{m-1} < n, and m <= n.
  The worst case is v_k = n - m + k, giving:
    |x| <= sum_{k=0}^{m-1} 3^{m-k-1} * 2^{n-m+k}
         = 2^{n-m} * sum_{k=0}^{m-1} 3^{m-k-1} * 2^k
         = 2^{n-m} * (3^m - 2^m)
         < 2^{n-m} * 3^m
         <= 3^n.
-/
import BohmSontacchi.Defs
import BohmSontacchi.Prop4

namespace BohmSontacchi

/-! ## The numerator sum used in the cycle formula

For a cycle of period n with m odd steps at positions v_0 < v_1 < ... < v_{m-1}
(all < n), the cycle element satisfies:
  x * (2^n - 3^m) = sum_{k=0}^{m-1} 3^{m-k-1} * 2^{v_k}

We define the sum directly and prove it is bounded by 3^n. -/

/-- The sum S(m, n, v) = sum_{k=0}^{m-1} 3^{m-k-1} * 2^{v_k} for a given
    list of positions v of length m. -/
def cycleNumeratorSum (v : List ℕ) : ℤ :=
  let m := v.length
  (List.range m).foldl
    (fun acc k => acc + 3 ^ (m - k - 1) * 2 ^ (v.getD k 0)) 0

/-- Helper: foldl with addition and initial value 0 equals Finset.sum. -/
lemma foldl_add_eq_finset_sum (m : ℕ) (f : ℕ → ℤ) :
    (List.range m).foldl (fun acc k => acc + f k) 0 =
    ∑ k ∈ Finset.range m, f k := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    conv_lhs =>
      rw [show (List.range n).foldl (fun acc k => acc + f k) 0 + f n =
            (∑ k ∈ Finset.range n, f k) + f n from by rw [← ih]]
    rw [Finset.sum_range_succ]

/-- The geometric sum identity over Finset.range:
    sum_{k=0}^{m-1} 3^{m-k-1} * 2^k = 3^m - 2^m. -/
private lemma geom_sum_finset (m : ℕ) :
    ∑ k ∈ Finset.range m, (3 : ℤ) ^ (m - k - 1) * 2 ^ k = 3 ^ m - 2 ^ m := by
  induction m with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hlast : (3 : ℤ) ^ (n + 1 - n - 1) * 2 ^ n = 2 ^ n := by simp
    rw [hlast]
    have hfactor : ∑ k ∈ Finset.range n, (3 : ℤ) ^ (n + 1 - k - 1) * 2 ^ k =
                   3 * ∑ k ∈ Finset.range n, (3 : ℤ) ^ (n - k - 1) * 2 ^ k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range] at hk
      have : n + 1 - k - 1 = (n - k - 1) + 1 := by omega
      rw [this, pow_succ]
      ring
    rw [hfactor, ih]
    ring

/-- The geometric sum identity:
    sum_{k=0}^{m-1} 3^{m-k-1} * 2^k = 3^m - 2^m.
    This is because sum_{k=0}^{m-1} 3^{m-k-1} * 2^k = (3^m - 2^m) / (3 - 2) = 3^m - 2^m. -/
theorem geom_sum_three_two (m : ℕ) :
    (List.range m).foldl
      (fun acc k => acc + (3 : ℤ) ^ (m - k - 1) * 2 ^ k) 0
    = 3 ^ m - 2 ^ m := by
  rw [foldl_add_eq_finset_sum]
  exact geom_sum_finset m

/-- Key inequality: for 1 <= m <= n, 2^{n-m} * (3^m - 2^m) < 3^n.
    Proof: 2^{n-m} * 3^m = (2^{n-m} * 3^m) and by AM-GM inequality on
    (n-m) copies of 2 and m copies of 3, we get 2^{n-m} * 3^m <= 3^n
    (since 2 < 3). Actually: 2^{n-m} * 3^m < 3^{n-m} * 3^m = 3^n. -/
theorem pow2_mul_diff_lt_pow3 {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    (2 : ℤ) ^ (n - m) * (3 ^ m - 2 ^ m) < 3 ^ n := by
  have h2m : (2 : ℤ) ^ m < 3 ^ m := by
    exact_mod_cast Nat.pow_lt_pow_left (by omega : 2 < 3) (by omega : m ≠ 0)
  have h2nm : (2 : ℤ) ^ (n - m) ≤ 3 ^ (n - m) := by
    exact_mod_cast Nat.pow_le_pow_left (by omega : 2 ≤ 3) (n - m)
  have h2pos : (0 : ℤ) < 2 ^ (n - m) := by positivity
  have hdiff_pos : (0 : ℤ) < 3 ^ m - 2 ^ m := by linarith
  have h2m_pos : (0 : ℤ) < 2 ^ m := by positivity
  calc (2 : ℤ) ^ (n - m) * (3 ^ m - 2 ^ m)
      < 2 ^ (n - m) * 3 ^ m := by
        have : (3 : ℤ) ^ m - 2 ^ m < 3 ^ m := by linarith
        exact mul_lt_mul_of_pos_left this h2pos
    _ ≤ 3 ^ (n - m) * 3 ^ m := by
        apply mul_le_mul_of_nonneg_right h2nm (by positivity)
    _ = 3 ^ n := by rw [← pow_add, Nat.sub_add_cancel hmn]

/-- In a strictly increasing list of length m with all elements < n,
    the k-th element satisfies v[k] + m <= n + k. -/
private lemma strict_mono_list_elem_bound (v : List ℕ) (n : ℕ)
    (hv_mono : v.Pairwise (· < ·))
    (hv_bound : ∀ i, i ∈ v → i < n)
    (k : ℕ) (hk : k < v.length) :
    v[k] + v.length ≤ n + k := by
  have hvmono' := List.pairwise_iff_getElem.mp hv_mono
  have hchain : ∀ j (hj : j < v.length), k ≤ j → v[k] + j ≤ v[j]'hj + k := by
    intro j hj hkj
    induction j with
    | zero =>
      have hk0 : k = 0 := by omega
      subst hk0
      omega
    | succ j' ihj =>
      by_cases hkj' : k ≤ j'
      · have hj' : j' < v.length := by omega
        have ih := ihj hj' hkj'
        have hlt := hvmono' j' (j' + 1) hj' hj (by omega)
        omega
      · have hk_eq : k = j' + 1 := by omega
        subst hk_eq
        omega
  have hm1 : v.length - 1 < v.length := by omega
  have hvm1 := hchain (v.length - 1) hm1 (by omega)
  have hvm1_lt : v[v.length - 1] < n := hv_bound _ (List.getElem_mem hm1)
  omega

/-- If v is a strictly increasing list of naturals with all elements < n,
    then cycleNumeratorSum v < 3^n. This is the core bound for Prop 6.

    The idea: each v_k <= n - m + k (since v_0 >= 0, v_1 >= 1, ..., v_{m-1} >= m-1
    and all v_k < n forces v_k <= n - m + k at worst). So:
    S <= sum_{k=0}^{m-1} 3^{m-k-1} * 2^{n-m+k} = 2^{n-m} * (3^m - 2^m) < 3^n. -/
theorem cycleNumeratorSum_lt_pow3 (v : List ℕ) (n : ℕ)
    (hv_nonempty : v ≠ [])
    (hv_mono : v.Pairwise (· < ·))
    (hv_bound : ∀ i, i ∈ v → i < n) :
    cycleNumeratorSum v < 3 ^ n := by
  have hm_pos : 1 ≤ v.length := by
    have := List.length_pos_iff_ne_nil.mpr hv_nonempty; omega
  have hmn : v.length ≤ n := by
    have := strict_mono_list_elem_bound v n hv_mono hv_bound 0 (by omega); omega
  unfold cycleNumeratorSum
  rw [foldl_add_eq_finset_sum]
  have hstep1 : ∑ k ∈ Finset.range v.length, (3 : ℤ) ^ (v.length - k - 1) * 2 ^ (v.getD k 0)
      ≤ ∑ k ∈ Finset.range v.length, (3 : ℤ) ^ (v.length - k - 1) * 2 ^ (n - v.length + k) := by
    apply Finset.sum_le_sum
    intro k hk
    rw [Finset.mem_range] at hk
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hgetD : v.getD k 0 = v[k] := (List.getElem_eq_getD (h := hk) 0).symm
    rw [hgetD]
    exact_mod_cast Nat.pow_le_pow_right (by omega : 0 < 2)
      (by have := strict_mono_list_elem_bound v n hv_mono hv_bound k hk; omega)
  have hstep2 : ∑ k ∈ Finset.range v.length, (3 : ℤ) ^ (v.length - k - 1) * 2 ^ (n - v.length + k)
      = 2 ^ (n - v.length) * (3 ^ v.length - 2 ^ v.length) := by
    have hcongr : ∀ k ∈ Finset.range v.length,
        (3 : ℤ) ^ (v.length - k - 1) * 2 ^ (n - v.length + k) =
        2 ^ (n - v.length) * ((3 : ℤ) ^ (v.length - k - 1) * 2 ^ k) := by
      intro k hk
      rw [Finset.mem_range] at hk
      rw [show (2 : ℤ) ^ (n - v.length + k) = 2 ^ (n - v.length) * 2 ^ k from pow_add 2 _ _]
      ring
    rw [Finset.sum_congr rfl hcongr, ← Finset.mul_sum, geom_sum_finset]
  linarith [pow2_mul_diff_lt_pow3 hm_pos hmn]

/-- Nonneg: the numerator sum is nonneg when all v_k are natural numbers. -/
theorem cycleNumeratorSum_nonneg (v : List ℕ) :
    0 ≤ cycleNumeratorSum v := by
  unfold cycleNumeratorSum
  rw [foldl_add_eq_finset_sum]
  apply Finset.sum_nonneg
  intro k _
  apply mul_nonneg <;> positivity

/-! ## Bridging listNumSum and cycleNumeratorSum -/

/-- listNumSum converts to a Finset.sum. -/
private theorem listNumSum_eq_finset_sum (v : List ℕ) :
    listNumSum v = ∑ k ∈ Finset.range v.length,
      (3 : ℤ) ^ (v.length - k - 1) * 2 ^ (v.getD k 0) := by
  induction v with
  | nil => simp [listNumSum]
  | cons a rest ih =>
    simp only [listNumSum, List.length_cons]
    rw [Finset.sum_range_succ']
    simp only [List.getD_cons_zero]
    have hrw : ∀ k ∈ Finset.range rest.length,
        (3 : ℤ) ^ (rest.length + 1 - (k + 1) - 1) * 2 ^ ((a :: rest).getD (k + 1) 0) =
        (3 : ℤ) ^ (rest.length - k - 1) * 2 ^ (rest.getD k 0) := by
      intro k hk
      rw [Finset.mem_range] at hk
      have h1 : rest.length + 1 - (k + 1) - 1 = rest.length - k - 1 := by omega
      have h2 : (a :: rest).getD (k + 1) 0 = rest.getD k 0 := by
        simp
      rw [h1, h2]
    rw [Finset.sum_congr rfl hrw, ← ih]
    have : rest.length + 1 - 0 - 1 = rest.length := by omega
    rw [this]; ring

/-- listNumSum and cycleNumeratorSum compute the same thing. -/
theorem listNumSum_eq_cycleNumeratorSum (v : List ℕ) :
    listNumSum v = cycleNumeratorSum v := by
  rw [listNumSum_eq_finset_sum]
  unfold cycleNumeratorSum
  rw [foldl_add_eq_finset_sum]

/-- The listNumSum is nonneg for any list of natural numbers. -/
theorem listNumSum_nonneg (v : List ℕ) : 0 ≤ listNumSum v := by
  rw [listNumSum_eq_cycleNumeratorSum]
  exact cycleNumeratorSum_nonneg v

/-- The listNumSum is < 3^n for strictly increasing v with all elements < n. -/
theorem listNumSum_lt_pow3 (v : List ℕ) (n : ℕ)
    (hv_nonempty : v ≠ [])
    (hv_mono : v.Pairwise (· < ·))
    (hv_bound : ∀ i, i ∈ v → i < n) :
    listNumSum v < 3 ^ n := by
  rw [listNumSum_eq_cycleNumeratorSum]
  exact cycleNumeratorSum_lt_pow3 v n hv_nonempty hv_mono hv_bound

/-- Extract the list of odd-step positions from the trajectory of x under u
  over n steps. -/
private def oddSteps' (x : ℤ) (n : ℕ) : List ℕ :=
  (List.range n).filter (fun i => decide (collatzU_iterate i x % 2 = 1))

/-- The odd steps list is strictly increasing. -/
private lemma oddSteps'_strictMono (x : ℤ) (n : ℕ) :
    (oddSteps' x n).Pairwise (· < ·) := by
  unfold oddSteps'
  exact List.Pairwise.filter _ List.pairwise_lt_range

/-- Odd steps elements are all < n. -/
private lemma oddSteps'_bound (x : ℤ) (n : ℕ) :
    ∀ i, i ∈ oddSteps' x n → i < n := by
  intro i hi
  unfold oddSteps' at hi
  simp only [List.mem_filter, List.mem_range] at hi
  exact hi.1

/-- Odd steps membership is equivalent to the iterate being odd. -/
private lemma oddSteps'_compat (x : ℤ) (n : ℕ) :
    ∀ i, i < n → (i ∈ oddSteps' x n ↔ collatzU_iterate i x % 2 = 1) := by
  intro i hi
  unfold oddSteps'
  simp only [List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun h => ⟨hi, h⟩⟩

/-- 2^n ≠ 3^m in ℤ when n > 0, for any m. -/
private lemma pow2_ne_pow3 {n m : ℕ} (hn : 0 < n) : (2 : ℤ) ^ n ≠ (3 : ℤ) ^ m := by
  intro h
  by_cases hm : m = 0
  · subst hm
    simp at h
    have : (2 : ℤ) ^ n ≥ 2 := by
      have : (2 : ℤ) ^ n ≥ 2 ^ 1 := by
        exact_mod_cast Nat.pow_le_pow_right (by omega) hn
      linarith [show (2 : ℤ) ^ (1 : ℕ) = 2 from by ring]
    omega
  · -- m > 0: 3^m is odd, 2^n is even
    have h_nat : (2 : ℕ) ^ n = (3 : ℕ) ^ m := by exact_mod_cast h
    have h2_even : 2 ∣ (2 : ℕ) ^ n := dvd_pow_self 2 (by omega : n ≠ 0)
    have h3_odd : ¬ 2 ∣ (3 : ℕ) ^ m := by
      rw [(Nat.prime_iff.mp Nat.prime_two).dvd_pow_iff_dvd (by omega)]
      omega
    exact h3_odd (h_nat ▸ h2_even)

/-! ## Main theorem: Proposition 6 -/

/-- PROPOSITION 6 (main statement): If x is a fixed point of u^n
    (i.e., isCycleOfU n x), then |x| < 3^n.

    The proof relies on Proposition 4 which gives the integer formula
    2^n * u^n(x) = 3^m * x + listNumSum v, and the bound listNumSum v < 3^n. -/
theorem prop6_cycle_bound (n : ℕ) (x : ℤ) (hcycle : isCycleOfU n x) :
    |x| < (3 : ℤ) ^ n := by
  obtain ⟨hn, hcycle_eq⟩ := hcycle
  -- Let v be the list of odd steps
  set v := oddSteps' x n with hv_def
  have hv_sorted : v.Pairwise (· < ·) := oddSteps'_strictMono x n
  have hv_bound : ∀ i, i ∈ v → i < n := oddSteps'_bound x n
  have hv_compat : ∀ i, i < n → (i ∈ v ↔ collatzU_iterate i x % 2 = 1) :=
    oddSteps'_compat x n
  -- Apply the integer formula
  have hformula := collatzU_iterate_int_formula x n v hv_sorted hv_bound hv_compat
  -- hformula : 2^n * collatzU_iterate n x = 3^v.length * x + listNumSum v
  -- Since collatzU_iterate n x = x:
  rw [hcycle_eq] at hformula
  -- hformula : 2^n * x = 3^v.length * x + listNumSum v
  -- So x * (2^n - 3^v.length) = listNumSum v
  have hkey : x * ((2 : ℤ) ^ n - 3 ^ v.length) = listNumSum v := by linarith
  -- Case split on whether v is empty
  by_cases hv_empty : v = []
  · -- v = []: listNumSum [] = 0, so x * (2^n - 1) = 0
    have hlen : v.length = 0 := by rw [hv_empty]; simp
    rw [hlen] at hkey
    simp only [pow_zero] at hkey
    rw [hv_empty, listNumSum] at hkey
    -- hkey : x * (2^n - 1) = 0
    -- 2^n - 1 ≠ 0 since n > 0
    have h2n_gt1 : (2 : ℤ) ^ n > 1 := by
      have : (2 : ℤ) ^ n ≥ 2 ^ 1 := by
        exact_mod_cast Nat.pow_le_pow_right (by omega) hn
      linarith [show (2 : ℤ) ^ (1 : ℕ) = 2 from by norm_num]
    have hx_zero : x = 0 := by
      rcases mul_eq_zero.mp hkey with h | h
      · exact h
      · omega
    rw [hx_zero, abs_zero]
    positivity
  · -- v ≠ []: use the bounds
    have hS_nonneg : 0 ≤ listNumSum v := listNumSum_nonneg v
    have hS_lt : listNumSum v < 3 ^ n := listNumSum_lt_pow3 v n hv_empty hv_sorted hv_bound
    -- 2^n ≠ 3^v.length
    have hne : (2 : ℤ) ^ n ≠ (3 : ℤ) ^ v.length := pow2_ne_pow3 hn
    -- So |2^n - 3^v.length| ≥ 1
    have hdiff_ne : (2 : ℤ) ^ n - 3 ^ v.length ≠ 0 := sub_ne_zero.mpr hne
    have hdiff_abs_ge1 : 1 ≤ |((2 : ℤ) ^ n - 3 ^ v.length)| := by
      exact Int.one_le_abs (sub_ne_zero.mpr hne)
    -- |x| * |2^n - 3^m| = |listNumSum v| = listNumSum v (since nonneg)
    have habs_eq : |x| * |((2 : ℤ) ^ n - 3 ^ v.length)| = listNumSum v := by
      rw [← abs_mul, hkey, abs_of_nonneg hS_nonneg]
    -- |x| ≤ listNumSum v (since |2^n - 3^m| ≥ 1)
    have habs_le : |x| ≤ listNumSum v := by
      calc |x| = |x| * 1 := by ring
        _ ≤ |x| * |((2 : ℤ) ^ n - 3 ^ v.length)| := by
          apply mul_le_mul_of_nonneg_left hdiff_abs_ge1 (abs_nonneg x)
        _ = listNumSum v := habs_eq
    linarith

/-- Equivalent formulation: cycle elements lie in the open interval (-3^n, 3^n). -/
theorem prop6_cycle_bound' (n : ℕ) (x : ℤ) (hcycle : isCycleOfU n x) :
    -(3 : ℤ) ^ n < x ∧ x < (3 : ℤ) ^ n := by
  have h := prop6_cycle_bound n x hcycle
  constructor
  · have := neg_abs_le x  -- -|x| ≤ x
    have := abs_nonneg x
    linarith
  · have := le_abs_self x
    linarith

/-- Corollary: The number of cycle points of period n is finite,
    since they all lie in a bounded interval. -/
theorem prop6_finite_cycles (n : ℕ) (_hn : 0 < n) :
    Set.Finite {x : ℤ | isCycleOfU n x} := by
  apply Set.Finite.subset (Set.finite_Ioo (-(3 : ℤ) ^ n) (3 ^ n))
  intro x hx
  simp only [Set.mem_setOf_eq] at hx
  simp only [Set.mem_Ioo]
  exact prop6_cycle_bound' n x hx

end BohmSontacchi
