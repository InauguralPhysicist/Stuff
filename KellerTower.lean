/-
  Tower layer, phase 1: the third level opened at y* = F(z*).

  yStar — the rational point y* = F(z*), z* = (-1643/50, 3289/100, -71/200)
    the certified n₂ = 9 point of comp_nine.
  certificate_star — first story of the n₃ ≥ 11 certificate (report §IV.2,
    --exact3): the fiber cubic of F at y* has exactly three real roots,
    z*₁ = -1643/50 exactly and the two conjugate siblings isolated in tight
    rational intervals.
  tower_nine — n₃(y*) ≥ 9 machine-checked: the nine comp_nine points are
    F³-preimages of y*, packaged as a Finset of cardinality nine.
  cubic_real_root — a depressed cubic with nonzero leading coefficient has
    a real root: the workhorse of the sibling +1 + 1 in the next phase
    (n₂(z') ≥ 1 and n₂(z'') ≥ 1, raising the floor from 9 to 11).
-/
import KellerComp

namespace KellerTower
open KellerCerts KellerBridge KellerComp

/-! ### y* = F(z*) -/

noncomputable def yStar1 : ℝ := (105734024991746346407793 : ℝ)/25000000000000
noncomputable def yStar2 : ℝ := (96532645623979569811 : ℝ)/250000000000
noncomputable def yStar3 : ℝ := ((-2980088152497 : ℝ)/25000000)

lemma yStar_eq1 : F1 ((-1643 : ℝ)/50) ((3289 : ℝ)/100) ((-71 : ℝ)/200) = yStar1 := by
  simp only [F1, yStar1]; norm_num

lemma yStar_eq2 : F2 ((-1643 : ℝ)/50) ((3289 : ℝ)/100) ((-71 : ℝ)/200) = yStar2 := by
  simp only [F2, yStar2]; norm_num

lemma yStar_eq3 : F3 ((-1643 : ℝ)/50) ((3289 : ℝ)/100) ((-71 : ℝ)/200) = yStar3 := by
  simp only [F3, yStar3]; norm_num

/-! ### The fiber cubic of F at y* -/

noncomputable def CStar (x : ℝ) : ℝ := ((2980088152497 : ℝ)/12500000) + ((863027380659663663876807476404201 : ℝ)/6250000000000000000) * x + ((-319705014102625550400028849 : ℝ)/2500000000000000) * x^3

/-- CStar is the fiber cubic L(y*)x³ + B(y*)x − 2y*₃. -/
lemma cStarEval : ∀ x : ℝ,
    CStar x = Lpoly yStar1 yStar2 yStar3 * x^3 + Bpoly yStar2 yStar3 * x - 2 * yStar3 := by
  intro x
  simp only [CStar, Lpoly, Bpoly, yStar1, yStar2, yStar3]
  norm_num

/-- K(y*) ≠ 0: the shape-lemma chart is available at y*. -/
lemma kStarNe : Kpoly yStar1 yStar2 yStar3 ≠ 0 := by
  simp only [Kpoly, yStar1, yStar2, yStar3]
  norm_num

lemma contCStar : Continuous CStar := by
  unfold CStar; fun_prop

/-- z*₁ is an exact rational root of the fiber cubic at y* — z* itself is
one of the three F-preimages of y*. -/
lemma rootStarZ : CStar ((-1643 : ℝ)/50) = 0 := by
  unfold CStar; norm_num

lemma rootStar2 : ∃ x, ((-9 : ℝ)/5000000000) < x ∧ x < ((-17 : ℝ)/10000000000) ∧ CStar x = 0 := by
  obtain ⟨x, h1, h2, h3⟩ := root_of_sign_change (f := fun x => -CStar x)
    (by unfold CStar; fun_prop) (a := ((-9 : ℝ)/5000000000)) (b := ((-17 : ℝ)/10000000000))
    (by norm_num) (by unfold CStar; norm_num) (by unfold CStar; norm_num)
  exact ⟨x, h1, h2, by simpa using h3⟩

lemma rootStar3 : ∃ x, ((328600000017 : ℝ)/10000000000) < x ∧ x < ((164300000009 : ℝ)/5000000000) ∧ CStar x = 0 := by
  exact root_of_sign_change contCStar (by norm_num)
    (by unfold CStar; norm_num) (by unfold CStar; norm_num)

/-- **Certificate** (first story of n₃ ≥ 11): the fiber cubic of F at y*
has exactly three real roots — z*₁ = -1643/50 exactly, and the two
conjugate siblings of the exact3 certificate, isolated in tight rational
intervals. -/
theorem certificate_star :
    ∃ s2 s3 : ℝ, ((-1643 : ℝ)/50) < s2 ∧ s2 < s3 ∧
      CStar s2 = 0 ∧ CStar s3 = 0 ∧
      ((-9 : ℝ)/5000000000) < s2 ∧ s2 < ((-17 : ℝ)/10000000000) ∧
      ((328600000017 : ℝ)/10000000000) < s3 ∧ s3 < ((164300000009 : ℝ)/5000000000) ∧
      (∀ x : ℝ, CStar x = 0 → x = ((-1643 : ℝ)/50) ∨ x = s2 ∨ x = s3) := by
  obtain ⟨s2, h2a, h2b, h2z⟩ := rootStar2
  obtain ⟨s3, h3a, h3b, h3z⟩ := rootStar3
  have h12 : ((-1643 : ℝ)/50) < s2 := by
    have : ((-1643 : ℝ)/50) ≤ ((-9 : ℝ)/5000000000) := by norm_num
    linarith
  have h23 : s2 < s3 := by
    have : ((-17 : ℝ)/10000000000) ≤ ((328600000017 : ℝ)/10000000000) := by norm_num
    linarith
  refine ⟨s2, s3, h12, h23, h2z, h3z, h2a, h2b, h3a, h3b, ?_⟩
  intro x hx
  refine cubic_localize ((-319705014102625550400028849 : ℝ)/2500000000000000)
      ((863027380659663663876807476404201 : ℝ)/6250000000000000000)
      ((2980088152497 : ℝ)/12500000)
      ((-1643 : ℝ)/50) s2 s3 (by norm_num) h12 h23 ?_ ?_ ?_ x ?_
  · have hz := rootStarZ; unfold CStar at hz; linarith
  · unfold CStar at h2z; linarith
  · unfold CStar at h3z; linarith
  · unfold CStar at hx; linarith

/-! ### n₃(y*) ≥ 9 -/

/-- **The nine-point floor**: the comp_nine points are F³-preimages of y*,
so n₃(y*) ≥ 9.  The remaining +1 + 1 (one F²-preimage over each sibling of
certificate_star) is the next phase. -/
theorem tower_nine :
    ∃ S : Finset (ℝ × ℝ × ℝ), S.card = 9 ∧
      ∀ a b c : ℝ, (a, b, c) ∈ S →
        F1 (F1 (F1 a b c) (F2 a b c) (F3 a b c))
           (F2 (F1 a b c) (F2 a b c) (F3 a b c))
           (F3 (F1 a b c) (F2 a b c) (F3 a b c)) = yStar1 ∧
        F2 (F1 (F1 a b c) (F2 a b c) (F3 a b c))
           (F2 (F1 a b c) (F2 a b c) (F3 a b c))
           (F3 (F1 a b c) (F2 a b c) (F3 a b c)) = yStar2 ∧
        F3 (F1 (F1 a b c) (F2 a b c) (F3 a b c))
           (F2 (F1 a b c) (F2 a b c) (F3 a b c))
           (F3 (F1 a b c) (F2 a b c) (F3 a b c)) = yStar3 := by
  obtain ⟨S, hcard, hiff⟩ := comp_nine_count
  refine ⟨S, hcard, fun a b c hmem => ?_⟩
  obtain ⟨h1, h2, h3⟩ := (hiff a b c).mpr hmem
  rw [h1, h2, h3]
  exact ⟨yStar_eq1, yStar_eq2, yStar_eq3⟩

/-! ### The cubic root workhorse for the sibling stories -/

private lemma cubic_real_root_pos (a b c : ℝ) (ha : 0 < a) :
    ∃ x : ℝ, a*x^3 + b*x + c = 0 := by
  set T : ℝ := (|b| + |c|)/a + 1 with hTdef
  have hT1 : 1 ≤ T := by
    have h0 : 0 ≤ (|b| + |c|)/a := div_nonneg (by positivity) ha.le
    simp only [hTdef]; linarith
  have hTpos : 0 < T := lt_of_lt_of_le one_pos hT1
  have haT : |b| + |c| < a*T := by
    have hcanc : (|b| + |c|)/a * a = |b| + |c| := div_mul_cancel₀ _ ha.ne'
    have h : a*T = |b| + |c| + a := by
      calc a*T = (|b| + |c|)/a * a + a := by rw [hTdef]; ring
        _ = |b| + |c| + a := by rw [hcanc]
    linarith
  have e1 : (|b| + |c|)*T < (a*T)*T := mul_lt_mul_of_pos_right haT hTpos
  have e2 : (a*T)*T ≤ ((a*T)*T)*T :=
    le_mul_of_one_le_right (mul_pos (mul_pos ha hTpos) hTpos).le hT1
  have e3 : (-|b|)*T ≤ b*T := mul_le_mul_of_nonneg_right (neg_abs_le b) hTpos.le
  have e3' : b*(-T) ≤ |b|*T := by
    nlinarith [mul_nonneg (by linarith [neg_abs_le b] : (0:ℝ) ≤ |b| + b) hTpos.le]
  have e4 : |c| ≤ |c|*T := le_mul_of_one_le_right (abs_nonneg c) hT1
  have hfT : 0 < a*T^3 + b*T + c := by
    nlinarith [le_abs_self c, neg_abs_le c]
  have hfnT : a*(-T)^3 + b*(-T) + c < 0 := by
    nlinarith [le_abs_self c, neg_abs_le c]
  obtain ⟨x, _, _, hx⟩ := root_of_sign_change
    (f := fun x => -(a*x^3 + b*x + c)) (by fun_prop)
    (show -T < T by linarith)
    (by simpa using neg_pos.mpr hfnT)
    (by simpa using neg_lt_zero.mpr hfT)
  exact ⟨x, by simpa using neg_eq_zero.mp (by simpa using hx)⟩

/-- A depressed cubic with nonzero leading coefficient has a real root. -/
lemma cubic_real_root (a b c : ℝ) (ha : a ≠ 0) :
    ∃ x : ℝ, a*x^3 + b*x + c = 0 := by
  rcases ha.lt_or_lt with hneg | hpos
  · obtain ⟨x, hx⟩ := cubic_real_root_pos (-a) (-b) (-c) (by linarith)
    exact ⟨x, by linarith⟩
  · exact cubic_real_root_pos a b c hpos

end KellerTower
