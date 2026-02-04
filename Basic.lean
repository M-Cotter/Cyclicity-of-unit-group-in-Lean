import Mathlib

-- It may not be computable since we use choice implicitly in some library functions

noncomputable section

/- Bound on the number of solutions to i ^ d = 1 in
   The first step is to bound the number of solutions to (ℤ/pℤ)ˣ by rewriting to
   a corresponding polynomial over GF(p), which can have at most d solutions. So,
   our initial set also must have at most d solutions. -/

theorem ZMod_bound_solns (p : ℕ) (d : ℕ) (dpos : d > 0) [Fact p.Prime] :
  Nat.card {i : (ZMod p)ˣ | i ^ d = 1} ≤ d := by
    calc
      Nat.card {i : (ZMod p)ˣ | i ^ d = 1} ≤
      Nat.card {i : ZMod p | i ^ d = 1} := by
        classical
        refine Nat.card_le_card_of_injective
          (fun i ↦ ⟨(i.1 : ZMod p),
          by rcases i with ⟨val, h⟩; simp? at h; exact (mem_rootsOfUnity' d val).mp h⟩)
          ?_
        intro i j h
        ext
        simpa using congrArg Subtype.val h
      Nat.card {i : ZMod p | i ^ d = 1} =
      Nat.card {i : ZMod p | i ^ d - 1 = 0} := by
        congr
        ext x
        rw [sub_eq_add_neg, add_eq_zero_iff_eq_neg, neg_neg]
      _ = Nat.card (Polynomial.rootSet (Polynomial.X ^ d - 1 : Polynomial (ZMod p)) (ZMod p)) := by
        congr
        ext x
        constructor
        intro xd
        · apply Multiset.mem_toFinset.mp
          · simp
            constructor
            · rw [sub_eq_add_neg, add_eq_zero_iff_eq_neg, neg_neg]
              refine (Polynomial.Monic.natDegree_pos ?_).mp ?_
              · exact Polynomial.monic_X_pow d
              · simp
                exact dpos
            · exact xd
        · intro xd
          apply Multiset.mem_toFinset.mpr at xd
          simp at xd
          exact xd.right
      _ ≤ (Polynomial.X ^ d - 1 : Polynomial (ZMod p)).natDegree := by
        apply Polynomial.ncard_rootSet_le
      _ = (Polynomial.X ^ d).natDegree := by
        apply Polynomial.natDegree_sub_eq_left_of_natDegree_lt
        simp
        exact dpos
      _ = d := by
        exact Polynomial.natDegree_X_pow d

/- Unit group of a prime is cyclic.
   Most of the work has already been done, now we need only show by contradiction using the
   bound in the previous step. Every element must be in the set previously shown since
   d is the exponent of the abelian group. However, the polynomial associated with the
   relation can have at most d solutions. So d = |(ℤ/pℤ)ˣ|, meaning our group is cyclic.-/
theorem cyclic_prime_unit {p : ℕ} [Fact p.Prime] : IsCyclic (ZMod p)ˣ := by
  apply IsCyclic.of_exponent_eq_card
  apply le_antisymm
  apply Nat.le_of_dvd
  · apply Nat.card_pos
  · apply Group.exponent_dvd_nat_card
  by_contra
  simp at this
  let d := Monoid.exponent (ZMod p)ˣ
  have : Nat.card (ZMod p)ˣ ≤ d := by
    calc
      Nat.card (ZMod p)ˣ = Nat.card {i : (ZMod p)ˣ | i ^ d = 1} := by
        rw [Nat.card_eq_fintype_card, ← Fintype.card_setUniv, ← Nat.card_eq_fintype_card]
        congr
        ext x
        simp only [Set.mem_univ, Set.mem_setOf_eq, true_iff]
        exact Monoid.pow_exponent_eq_one x
      Nat.card {i : (ZMod p)ˣ | i ^ d = 1} ≤ d := by
        apply ZMod_bound_solns
        apply Monoid.exponent_pos.mpr Monoid.ExponentExists.of_finite
  simp at *
  linarith

set_option linter.style.induction false

/- Unit group of an odd prime power is cyclic.
   Relies on bashing the orders of several elements, using the inductive hypothesis
   to fix a generator of the previous group. We use that to find an element i of order
   φ(p ^ (k + 1)), which we can then use with (1 + p) to find an element of
   order the order of our unit group, hence it is cyclic. -/

#check ZMod.orderOf_one_add_prime

theorem cyclic_prime_power_unit
    (p : ℕ) (n : ℕ) (pneqtwo : p ≠ 2) (npos : n > 0) [Fact p.Prime] :
    IsCyclic (ZMod (p ^ n))ˣ := by
  cases n with
  | zero =>
    linarith
  | succ n =>
    induction' n with k hk
    · rw [pow_one]
      exact cyclic_prime_unit
    rcases (isCyclic_iff_exists_orderOf_eq_natCard.mp (hk (by linarith))) with ⟨g, gord⟩
    simp only [Nat.card_eq_fintype_card, ZMod.card_units_eq_totient] at gord
    -- Compute the order of h
    let h : (ZMod (p ^ (k + 1 + 1))) := ZMod.cast g.val
    have dvdsucc : (p ^ (k + 1)) ∣ (p ^ (k + 1 + 1)) := by exact Dvd.intro p rfl
    have heq : ZMod.castHom dvdsucc (ZMod (p ^ (k + 1))) h = g.val := by
      exact ZMod.ringHom_map_cast (ZMod.castHom dvdsucc (ZMod (p ^ (k + 1)))) ↑g
    have orderOfh : (p ^ (k + 1)).totient ∣ orderOf (h) := by
      rw [← gord, ← orderOf_units, ← heq]
      apply orderOf_dvd_iff_pow_eq_one.mpr
      rw [← map_pow, pow_orderOf_eq_one, map_one]
    rcases orderOfh with ⟨n, orderOfh⟩
    have hvalegval : ((ZMod.cast g.val : ZMod (p ^ (k + 1 + 1))).val : ℕ) = (g.1.val : ℕ) := by
      apply ZMod.val_cast_eq_val_of_lt
      apply lt_trans
      · apply ZMod.val_lt
      apply Nat.pow_lt_pow_of_lt
      · apply Nat.Prime.one_lt Fact.out
      exact lt_add_one (k + 1)
    have : g.1.val.Coprime p := by
      rw [← Nat.coprime_pow_right_iff (by change k + 1 > 0; norm_num), ← ZMod.isUnit_iff_coprime]
      simp
    have hUnit : IsUnit (h.val : ZMod (p ^ (k + 1 + 1))) := by
      rw [ZMod.isUnit_iff_coprime, Nat.coprime_pow_right_iff, hvalegval]
      · apply this
      exact Nat.lt_add_of_pos_left npos
    -- Compute the order of i
    let i := h ^ n
    have : orderOf h > 0 := by
      have : (h.val : ZMod (p ^ (k + 1 + 1))) = h := by simp
      rw [← this]
      apply orderOf_pos_iff.mpr
      apply isOfFinOrder_iff_isUnit.mpr hUnit
    have npos : n > 0 := by
      apply (Nat.mul_pos_iff_of_pos_left (Nat.pos_of_neZero (p ^ (k + 1)).totient)).mp
      rw [← orderOfh]
      exact this
    have orderOfi : orderOf i = (p ^ (k + 1)).totient := by
      rw [orderOf_pow', orderOfh]
      simp only [Nat.gcd_mul_left_left]
      rw [Nat.mul_div_cancel]
      exact npos
      exact Nat.ne_zero_of_lt npos
    -- Compute the order of i ^ (p ^ k)
    have orderOfipow : orderOf (i ^ (p ^ k)) = p - 1 := by
      rw [orderOf_pow']
      rw [orderOfi, Nat.totient_prime_pow]
      simp
      rw [Nat.mul_div_cancel_left]
      apply pow_pos
      exact Nat.pos_of_neZero p
      exact Fact.out
      exact Nat.zero_lt_succ k
      exact Ne.symm (NeZero.ne' (p ^ k))
    -- Compute the order of 1 + p
    let onep := ((1 + p) : ZMod (p ^ (k + 1 + 1)))
    have orderOfmulipow : orderOf (i ^ (p ^ k) * onep : ZMod (p ^ (k + 1 + 1)))
        = p ^ (k + 1) * (p - 1) := by
        symm
        calc
          p ^ (k + 1) * (p - 1) = p ^ (k + 1 + 1 - 1) * (p - 1) := by simp
          _ = (orderOf (i ^ (p ^ k))) * orderOf onep := by
            rw [← orderOfipow]
            rw [ZMod.orderOf_one_add_prime Fact.out pneqtwo]
            rw [mul_comm]
            simp
          _ = orderOf (i ^ (p ^ k) * onep : ZMod (p ^ (k + 1 + 1))) := by
            symm
            apply Commute.orderOf_mul_eq_mul_orderOf_of_coprime
            apply Commute.all
            rw [orderOfipow, ZMod.orderOf_one_add_prime Fact.out pneqtwo]
            simp
            rw [Nat.coprime_comm]
            apply Nat.coprime_of_lt_prime
            apply ne_of_gt
            rw [Nat.lt_sub_iff_add_lt, zero_add]
            apply Nat.Prime.one_lt Fact.out
            simp
            apply lt_trans
            show 0 < 1; norm_num
            apply Nat.Prime.one_lt Fact.out
            exact Fact.out
    -- Compute the order of i ^ (p ^ k) * onep
    let ipowmul := i ^ (p ^ k) * onep
    have ipowmul_unit : IsUnit ipowmul := by
      apply isUnit_iff_exists_inv.mpr
      use (ipowmul ^ (p ^ (k + 1) * (p - 1) - 1))
      nth_rw 1 [← pow_one ipowmul]
      have : 1 ≤ p ^ (k + 1) * (p - 1) := by
        apply Nat.le_iff_lt_add_one.mpr
        simp
        constructor
        apply pow_pos (Nat.Prime.pos Fact.out)
        apply Nat.Prime.one_lt Fact.out
      rw [← pow_add, ← Nat.add_sub_assoc this, add_comm 1, Nat.add_sub_assoc (by simp)]
      simp only [tsub_self, add_zero]
      rw [← orderOfmulipow, pow_orderOf_eq_one]
    -- Since  i ^ (p ^ k) * onep has the desired order we are done
    apply isCyclic_of_orderOf_eq_card ipowmul_unit.unit
    rw [← orderOf_units]
    simp only [IsUnit.unit_spec, Nat.card_eq_fintype_card, ZMod.card_units_eq_totient]
    rw [orderOfmulipow, Nat.totient_prime_pow, Nat.add_sub_assoc (le_refl _)]
    exact Fact.out
    exact Nat.lt_add_of_pos_left (by expose_names; exact Nat.lt_add_of_pos_left npos_1)

-- Unit group of an odd natural cross the unit group of two and its double are isomorphic
-- Simple application of CRT
def two_times_odd_unit_iso (n : ℕ) (nodd : Odd n) :
  (ZMod (2 * n))ˣ  ≃* ((ZMod 2) × (ZMod n))ˣ := by
  apply Units.mapEquiv
  apply RingEquiv.toMulEquiv
  apply ZMod.chineseRemainder
  exact Nat.coprime_two_left.mpr nodd

-- Unit group of an odd natural and its double are isomorphic
def unit_two_times_odd_unit_iso (n : ℕ) (nodd : Odd n) :
  (ZMod (2 * n))ˣ ≃* (ZMod n)ˣ := by
  apply MulEquiv.trans (two_times_odd_unit_iso n nodd)
  apply MulEquiv.trans MulEquiv.prodUnits
  have : (ZMod 2)ˣ ≃* PUnit := by apply mulEquivOfCyclicCardEq ?_; simp
  apply MulEquiv.trans (MulEquiv.prodCongr this (MulEquiv.refl (ZMod n)ˣ))
  apply MulEquiv.uniqueProd

-- Unit group of two times a prime power is cyclic, uses isomorphism shown previously
theorem cyclic_two_prime_power_unit
    (p : ℕ) (n : ℕ) [Fact p.Prime] (podd : Odd p) (npos : n > 0) :
  IsCyclic (ZMod (2 * (p ^ n)))ˣ := by
  have : (ZMod (2 * (p ^ n)))ˣ ≃* (ZMod (p ^ n))ˣ := by
    apply unit_two_times_odd_unit_iso
    apply (Nat.odd_pow_iff (Nat.ne_zero_of_lt npos)).mpr podd
  apply (MulEquiv.isCyclic this).mpr
  apply cyclic_prime_power_unit
  intro p2
  apply Nat.not_even_iff_odd.mpr podd; use 1; apply npos

/- Auxiliary theorem stating that if a divides b then either a divides 2b or a + b
divides b ℤ/2ℤ. Classical application of modular arithmetic.
-/
theorem aux (n k : ℤ) (kpos : 0 < k) (nmodk : n % k = 0) : n % (2 * k) = 0 ∨ n % (2 * k) = k := by
  rcases (Int.dvd_of_emod_eq_zero nmodk) with ⟨x, hx⟩
  by_cases xodd : Odd x
  rcases xodd with ⟨y, hy⟩
  right
  rw [hx, hy, mul_add, ← mul_assoc, mul_comm 2]
  simp
  rw [Int.emod_eq_of_lt]
  exact Int.le_of_lt kpos
  nth_rw 1 [← mul_one k]
  apply Int.mul_lt_mul' (le_refl _) (by norm_num) (by norm_num) kpos
  rw [Int.not_odd_iff_even] at xodd
  left
  rcases xodd with ⟨y, hy⟩
  simp
  use y
  rw [mul_comm 2, mul_assoc, two_mul, ← hy, hx]


-- Any group with two elements that square of equal 1 is not cyclic
theorem two_not_cyclic {G : Type} [Group G] [Finite G] (x y : G)
  (xorder : orderOf x = 2) (yorder : orderOf y = 2)
  (xney : x ≠ y): ¬(IsCyclic G) := by
  intro GCyc
  -- Some easy haves for cleanliness
  have xneo : x ≠ 1 := by
    intro hx
    have : orderOf x = 1 := orderOf_eq_one_iff.mpr hx
    linarith
  have yneo : y ≠ 1 := by
    intro hy
    have : orderOf y = 1 := orderOf_eq_one_iff.mpr hy
    linarith
  have yinv : y⁻¹ = y := inv_eq_self_of_orderOf_eq_two yorder
  have xinv : x⁻¹ = x := inv_eq_self_of_orderOf_eq_two xorder
  have xsq : x ^ (2 : ℤ) = 1 := by rw [zpow_ofNat, ← xorder, pow_orderOf_eq_one]
  have ysq : y ^ (2 : ℤ) = 1 := by rw [zpow_ofNat, ← yorder, pow_orderOf_eq_one]
  rcases GCyc with ⟨g, hg⟩
  simp [Function.Surjective] at hg
  rcases hg x with ⟨xn, hx⟩
  rcases hg y with ⟨yn, hy⟩
  have : orderOf g = Nat.card G := by
    exact orderOf_eq_card_of_forall_mem_zpowers hg
  let k := orderOf g
  -- Split by cases on whether the order of g is odd
  by_cases kOdd : Odd (k : ℤ)
  have xn_eq_o_mod_k : xn % k = 0 := by
    apply Int.emod_eq_zero_of_dvd
    apply Int.dvd_of_dvd_mul_right_of_gcd_one
    apply orderOf_dvd_iff_zpow_eq_one.mpr
    rw [mul_comm, zpow_mul, hx, xsq]
    rw [Int.odd_iff] at kOdd
    rw [← Int.gcd_emod, kOdd]
    simp
  apply xneo
  rw [← hx, ← zpow_mod_orderOf, xn_eq_o_mod_k, zpow_zero]
  rw [Int.not_odd_iff] at kOdd
  have half_k_pos : 0 < (k : ℤ) / 2 := by
    rw [← Int.even_iff] at kOdd
    rcases kOdd with ⟨y, hy⟩
    rw [hy, ← Int.two_mul, Int.mul_ediv_cancel_left]
    apply (mul_pos_iff_of_pos_left (by change 0 < 2; norm_num)).mp
    rw [two_mul, ← hy]
    simp
    apply orderOf_pos
    norm_num
  -- We use the auxiliary lemma to get a condition on x and y to operate on later
  have x_cond : xn % k = 0 ∨ xn % k = k / 2 := by
    nth_rw 1 [← Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero kOdd)]
    nth_rw 2 [← Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero kOdd)]
    rw [mul_comm _ 2]
    apply aux
    apply half_k_pos
    simp
    rw [← Int.mul_dvd_mul_iff_left (by show 2 ≠ 0; norm_num)]
    rw [mul_comm, Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero kOdd)]
    apply orderOf_dvd_iff_zpow_eq_one.mpr
    rw [mul_comm, zpow_mul, hx, xsq]
  have y_cond : yn % k = 0 ∨ yn % k = k / 2 := by
    nth_rw 1 [← Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero kOdd)]
    nth_rw 2 [← Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero kOdd)]
    rw [mul_comm _ 2]
    apply aux
    apply half_k_pos
    simp
    rw [← Int.mul_dvd_mul_iff_left (by show 2 ≠ 0; norm_num)]
    rw [mul_comm, Int.ediv_mul_cancel (Int.dvd_of_emod_eq_zero kOdd)]
    apply orderOf_dvd_iff_zpow_eq_one.mpr
    rw [mul_comm, zpow_mul, hy, ysq]
  -- Final stretch where we arrive at contradictions, by cases on the previous conditions
  cases x_cond with
  | inl x_z =>
    apply xneo
    rw [← hx, ← zpow_mod_orderOf, x_z, zpow_zero]
  | inr x_h =>
    cases y_cond with
    | inl y_z =>
      apply yneo
      rw [← hy, ← zpow_mod_orderOf, y_z, zpow_zero]
    | inr y_h =>
      apply xney
      rw [← hx, ← hy, ← zpow_mod_orderOf, ← zpow_mod_orderOf _ yn, x_h, y_h]
