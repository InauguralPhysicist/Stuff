/-
  Composition layer: the second story assembled.

  comp_nine — F ∘ F has exactly nine real preimages over
  yNine = (-1643/50, 3289/100, -71/200): three fiber-cubic roots
  r1 < r2 < r3 upstairs (certificate_nine), and over each first-story
  preimage zᵢ = (rᵢ, P2Nine rᵢ, P3Nine rᵢ) exactly three more roots
  t_{i1} < t_{i2} < t_{i3} (story2_nine_i), each lifted to a genuine
  preimage by the global existence lemmas (exists_glob1/2/3) through the
  shape chart b = G2side/(2K), c = G3side/(8K).  comp_nine_count packages
  the count: a Finset of cardinality nine containing precisely the
  solutions of F(F x) = yNine.

  This machine-checks the full tower step n₂(yNine) = 9 = 3 × 3 quoted in
  report §IV.2: fiber determination at both stories plus existence and
  distinctness of all nine second-story points.
-/
import KellerDepth
import KellerExist

namespace KellerComp
open KellerCerts KellerBridge KellerDepth KellerExist

/-- The x₂ shape-chart value over the story point (r, P2Nine r, P3Nine r). -/
noncomputable def bStory (t r : ℝ) : ℝ :=
  G2side t r (P2Nine r) (P3Nine r) / (2 * Kpoly r (P2Nine r) (P3Nine r))

/-- The x₃ shape-chart value over the story point (r, P2Nine r, P3Nine r). -/
noncomputable def cStory (t r : ℝ) : ℝ :=
  G3side t r (P2Nine r) (P3Nine r) / (8 * Kpoly r (P2Nine r) (P3Nine r))

lemma bStory_spec (t r : ℝ) (hK : Kpoly r (P2Nine r) (P3Nine r) ≠ 0) :
    2 * Kpoly r (P2Nine r) (P3Nine r) * bStory t r
      = G2side t r (P2Nine r) (P3Nine r) := by
  have h2K : (2 : ℝ) * Kpoly r (P2Nine r) (P3Nine r) ≠ 0 :=
    mul_ne_zero two_ne_zero hK
  simp only [bStory]
  rw [mul_comm, div_mul_cancel₀ _ h2K]

lemma cStory_spec (t r : ℝ) (hK : Kpoly r (P2Nine r) (P3Nine r) ≠ 0) :
    8 * Kpoly r (P2Nine r) (P3Nine r) * cStory t r
      = G3side t r (P2Nine r) (P3Nine r) := by
  have h8K : (8 : ℝ) * Kpoly r (P2Nine r) (P3Nine r) ≠ 0 :=
    mul_ne_zero (by norm_num) hK
  simp only [cStory]
  rw [mul_comm, div_mul_cancel₀ _ h8K]

/-- Fiber determination over a story point: if the fiber cubic at
(r, P2Nine r, P3Nine r) has exactly the roots t1, t2, t3 and K ≠ 0 there,
then F⁻¹ of the story point is exactly the three chart lifts. -/
lemma fiber_at (r t1 t2 t3 : ℝ)
    (hK : Kpoly r (P2Nine r) (P3Nine r) ≠ 0)
    (hiff : ∀ t : ℝ, (Lpoly r (P2Nine r) (P3Nine r) * t^3
        + Bpoly (P2Nine r) (P3Nine r) * t - 2 * P3Nine r = 0
      ↔ (t = t1 ∨ t = t2 ∨ t = t3))) :
    ∀ a b c : ℝ,
      (F1 a b c = r ∧ F2 a b c = P2Nine r ∧ F3 a b c = P3Nine r) ↔
      ((a = t1 ∧ b = bStory t1 r ∧ c = cStory t1 r) ∨
       (a = t2 ∧ b = bStory t2 r ∧ c = cStory t2 r) ∨
       (a = t3 ∧ b = bStory t3 r ∧ c = cStory t3 r)) := by
  have h2K : (2 : ℝ) * Kpoly r (P2Nine r) (P3Nine r) ≠ 0 :=
    mul_ne_zero two_ne_zero hK
  have h8K : (8 : ℝ) * Kpoly r (P2Nine r) (P3Nine r) ≠ 0 :=
    mul_ne_zero (by norm_num) hK
  intro a b c
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hcube := cubic_identity a b c
    rw [h1, h2, h3] at hcube
    have hb : b = bStory a r := by
      have hs := shape2_identity a b c
      rw [h1, h2, h3] at hs
      simp only [bStory]
      rw [eq_div_iff h2K]
      linear_combination hs
    have hc : c = cStory a r := by
      have hs := shape3_identity a b c
      rw [h1, h2, h3] at hs
      simp only [cStory]
      rw [eq_div_iff h8K]
      linear_combination hs
    rcases (hiff a).mp hcube with ha | ha | ha
    · exact Or.inl ⟨ha, by rw [← ha]; exact hb, by rw [← ha]; exact hc⟩
    · exact Or.inr (Or.inl ⟨ha, by rw [← ha]; exact hb, by rw [← ha]; exact hc⟩)
    · exact Or.inr (Or.inr ⟨ha, by rw [← ha]; exact hb, by rw [← ha]; exact hc⟩)
  · have key : ∀ t : ℝ, (t = t1 ∨ t = t2 ∨ t = t3) →
        F1 t (bStory t r) (cStory t r) = r ∧
        F2 t (bStory t r) (cStory t r) = P2Nine r ∧
        F3 t (bStory t r) (cStory t r) = P3Nine r := by
      intro t ht
      have hC := (hiff t).mpr ht
      exact ⟨exists_glob1 t r (P2Nine r) (P3Nine r) (bStory t r) (cStory t r)
               (bStory_spec t r hK) (cStory_spec t r hK) hC hK,
             exists_glob2 t r (P2Nine r) (P3Nine r) (bStory t r) (cStory t r)
               (bStory_spec t r hK) (cStory_spec t r hK) hC hK,
             exists_glob3 t r (P2Nine r) (P3Nine r) (bStory t r) (cStory t r)
               (bStory_spec t r hK) (cStory_spec t r hK) hC hK⟩
    rintro (⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩)
    · rw [ha, hb, hc]; exact key t1 (Or.inl rfl)
    · rw [ha, hb, hc]; exact key t2 (Or.inr (Or.inl rfl))
    · rw [ha, hb, hc]; exact key t3 (Or.inr (Or.inr rfl))

/-- Fiber determination at yNine, phrased for a given certified root
triple (the analogue of fiber_nine with the roots exposed). -/
lemma fiber_nine_at (r1 r2 r3 : ℝ)
    (hz1 : CNine r1 = 0) (hz2 : CNine r2 = 0) (hz3 : CNine r3 = 0)
    (hloc : ∀ x : ℝ, CNine x = 0 → x = r1 ∨ x = r2 ∨ x = r3) :
    ∀ a b c : ℝ,
      (F1 a b c = ((-1643 : ℝ)/50) ∧ F2 a b c = ((3289 : ℝ)/100) ∧
       F3 a b c = ((-71 : ℝ)/200)) ↔
      ((a = r1 ∧ b = P2Nine r1 ∧ c = P3Nine r1) ∨
       (a = r2 ∧ b = P2Nine r2 ∧ c = P3Nine r2) ∨
       (a = r3 ∧ b = P2Nine r3 ∧ c = P3Nine r3)) := by
  intro a b c
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hcube := cubic_identity a b c
    rw [h1, h2, h3, cNineEval] at hcube
    have hb : b = P2Nine a := by
      have hs := shape2_identity a b c
      rw [h1, h2, h3, g2Nine, kNineEval] at hs
      exact mul_left_cancel₀
        (by norm_num : (2 * ((2543299 : ℝ)/2000000) : ℝ) ≠ 0) hs
    have hc : c = P3Nine a := by
      have hs := shape3_identity a b c
      rw [h1, h2, h3, g3Nine, kNineEval] at hs
      exact mul_left_cancel₀
        (by norm_num : (8 * ((2543299 : ℝ)/2000000) : ℝ) ≠ 0) hs
    rcases hloc a hcube with ha | ha | ha
    · exact Or.inl ⟨ha, by rw [← ha]; exact hb, by rw [← ha]; exact hc⟩
    · exact Or.inr (Or.inl ⟨ha, by rw [← ha]; exact hb, by rw [← ha]; exact hc⟩)
    · exact Or.inr (Or.inr ⟨ha, by rw [← ha]; exact hb, by rw [← ha]; exact hc⟩)
  · have hback : ∀ r : ℝ, CNine r = 0 →
        F1 r (P2Nine r) (P3Nine r) = ((-1643 : ℝ)/50) ∧
        F2 r (P2Nine r) (P3Nine r) = ((3289 : ℝ)/100) ∧
        F3 r (P2Nine r) (P3Nine r) = ((-71 : ℝ)/200) := by
      intro r hr
      have e1 := existsNine1 r
      have e2 := existsNine2 r
      have e3 := existsNine3 r
      rw [hr, mul_zero] at e1 e2 e3
      exact ⟨by linarith, by linarith, by linarith⟩
    rintro (⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩)
    · rw [ha, hb, hc]; exact hback r1 hz1
    · rw [ha, hb, hc]; exact hback r2 hz2
    · rw [ha, hb, hc]; exact hback r3 hz3

/-- Three ordered roots hit three ordered disjoint intervals in order. -/
lemma triple_order {r1 r2 r3 s1 s2 s3 a1 b1 a2 b2 a3 b3 : ℝ}
    (h12 : r1 < r2) (h23 : r2 < r3)
    (hs1a : a1 < s1) (hs1b : s1 < b1)
    (hs2a : a2 < s2) (hs2b : s2 < b2)
    (hs3a : a3 < s3) (hs3b : s3 < b3)
    (hd1 : b1 ≤ a2) (hd2 : b2 ≤ a3)
    (e1 : s1 = r1 ∨ s1 = r2 ∨ s1 = r3)
    (e2 : s2 = r1 ∨ s2 = r2 ∨ s2 = r3)
    (e3 : s3 = r1 ∨ s3 = r2 ∨ s3 = r3) :
    (a1 < r1 ∧ r1 < b1) ∧ (a2 < r2 ∧ r2 < b2) ∧ (a3 < r3 ∧ r3 < b3) := by
  rcases e1 with h1 | h1 | h1 <;> rcases e2 with h2 | h2 | h2 <;>
    rcases e3 with h3 | h3 | h3 <;>
    exact ⟨⟨by linarith, by linarith⟩, ⟨by linarith, by linarith⟩,
           ⟨by linarith, by linarith⟩⟩

/-- **The second story of the nine-certificate.**  F ∘ F has exactly nine
real preimages over yNine: three fiber-cubic roots r1 < r2 < r3 upstairs,
and over each story point exactly three chart lifts, all distinct (the
three F1-image clauses separate the groups). -/
theorem comp_nine :
    ∃ r1 r2 r3 t11 t12 t13 t21 t22 t23 t31 t32 t33 : ℝ,
      r1 < r2 ∧ r2 < r3 ∧
      (t11 < t12 ∧ t12 < t13) ∧ (t21 < t22 ∧ t22 < t23) ∧
      (t31 < t32 ∧ t32 < t33) ∧
      F1 t11 (bStory t11 r1) (cStory t11 r1) = r1 ∧
      F1 t12 (bStory t12 r1) (cStory t12 r1) = r1 ∧
      F1 t13 (bStory t13 r1) (cStory t13 r1) = r1 ∧
      F1 t21 (bStory t21 r2) (cStory t21 r2) = r2 ∧
      F1 t22 (bStory t22 r2) (cStory t22 r2) = r2 ∧
      F1 t23 (bStory t23 r2) (cStory t23 r2) = r2 ∧
      F1 t31 (bStory t31 r3) (cStory t31 r3) = r3 ∧
      F1 t32 (bStory t32 r3) (cStory t32 r3) = r3 ∧
      F1 t33 (bStory t33 r3) (cStory t33 r3) = r3 ∧
      (∀ a b c : ℝ,
        (F1 (F1 a b c) (F2 a b c) (F3 a b c) = ((-1643 : ℝ)/50) ∧
         F2 (F1 a b c) (F2 a b c) (F3 a b c) = ((3289 : ℝ)/100) ∧
         F3 (F1 a b c) (F2 a b c) (F3 a b c) = ((-71 : ℝ)/200)) ↔
        ((a = t11 ∧ b = bStory t11 r1 ∧ c = cStory t11 r1) ∨
         (a = t12 ∧ b = bStory t12 r1 ∧ c = cStory t12 r1) ∨
         (a = t13 ∧ b = bStory t13 r1 ∧ c = cStory t13 r1) ∨
         (a = t21 ∧ b = bStory t21 r2 ∧ c = cStory t21 r2) ∨
         (a = t22 ∧ b = bStory t22 r2 ∧ c = cStory t22 r2) ∨
         (a = t23 ∧ b = bStory t23 r2 ∧ c = cStory t23 r2) ∨
         (a = t31 ∧ b = bStory t31 r3 ∧ c = cStory t31 r3) ∨
         (a = t32 ∧ b = bStory t32 r3 ∧ c = cStory t32 r3) ∨
         (a = t33 ∧ b = bStory t33 r3 ∧ c = cStory t33 r3))) := by
  obtain ⟨r1, r2, r3, h12, h23, hz1, hz2, hz3, hloc, hn1, hn2, hn3⟩ :=
    certificate_nine
  obtain ⟨s1, hs1a, hs1b, hs1z⟩ := story2_nine_1.1
  obtain ⟨s2, hs2a, hs2b, hs2z⟩ := story2_nine_2.1
  obtain ⟨s3, hs3a, hs3b, hs3z⟩ := story2_nine_3.1
  obtain ⟨⟨hr1a, hr1b⟩, ⟨hr2a, hr2b⟩, ⟨hr3a, hr3b⟩⟩ :=
    triple_order h12 h23 hs1a hs1b hs2a hs2b hs3a hs3b
      (by norm_num) (by norm_num)
      (hloc s1 hs1z) (hloc s2 hs2z) (hloc s3 hs3z)
  obtain ⟨hL1, hK1, t11, t12, t13, ht112, ht123, hcub1⟩ :=
    story2_nine_1.2 r1 hr1a hr1b hz1
  obtain ⟨hL2, hK2, t21, t22, t23, ht212, ht223, hcub2⟩ :=
    story2_nine_2.2 r2 hr2a hr2b hz2
  obtain ⟨hL3, hK3, t31, t32, t33, ht312, ht323, hcub3⟩ :=
    story2_nine_3.2 r3 hr3a hr3b hz3
  have fib1 := fiber_at r1 t11 t12 t13 hK1 hcub1
  have fib2 := fiber_at r2 t21 t22 t23 hK2 hcub2
  have fib3 := fiber_at r3 t31 t32 t33 hK3 hcub3
  have fibN := fiber_nine_at r1 r2 r3 hz1 hz2 hz3 hloc
  have m11 := (fib1 t11 (bStory t11 r1) (cStory t11 r1)).mpr
    (Or.inl ⟨rfl, rfl, rfl⟩)
  have m12 := (fib1 t12 (bStory t12 r1) (cStory t12 r1)).mpr
    (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  have m13 := (fib1 t13 (bStory t13 r1) (cStory t13 r1)).mpr
    (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
  have m21 := (fib2 t21 (bStory t21 r2) (cStory t21 r2)).mpr
    (Or.inl ⟨rfl, rfl, rfl⟩)
  have m22 := (fib2 t22 (bStory t22 r2) (cStory t22 r2)).mpr
    (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  have m23 := (fib2 t23 (bStory t23 r2) (cStory t23 r2)).mpr
    (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
  have m31 := (fib3 t31 (bStory t31 r3) (cStory t31 r3)).mpr
    (Or.inl ⟨rfl, rfl, rfl⟩)
  have m32 := (fib3 t32 (bStory t32 r3) (cStory t32 r3)).mpr
    (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  have m33 := (fib3 t33 (bStory t33 r3) (cStory t33 r3)).mpr
    (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
  have hy1 := (fibN r1 (P2Nine r1) (P3Nine r1)).mpr (Or.inl ⟨rfl, rfl, rfl⟩)
  have hy2 := (fibN r2 (P2Nine r2) (P3Nine r2)).mpr
    (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))
  have hy3 := (fibN r3 (P2Nine r3) (P3Nine r3)).mpr
    (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))
  refine ⟨r1, r2, r3, t11, t12, t13, t21, t22, t23, t31, t32, t33,
    h12, h23, ⟨ht112, ht123⟩, ⟨ht212, ht223⟩, ⟨ht312, ht323⟩,
    m11.1, m12.1, m13.1, m21.1, m22.1, m23.1, m31.1, m32.1, m33.1, ?_⟩
  intro a b c
  constructor
  · rintro ⟨g1, g2, g3⟩
    rcases (fibN (F1 a b c) (F2 a b c) (F3 a b c)).mp ⟨g1, g2, g3⟩ with
      h | h | h
    · rcases (fib1 a b c).mp h with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl h')
      · exact Or.inr (Or.inr (Or.inl h'))
    · rcases (fib2 a b c).mp h with h' | h' | h'
      · exact Or.inr (Or.inr (Or.inr (Or.inl h')))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h')))))
    · rcases (fib3 a b c).mp h with h' | h' | h'
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inl h')))))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr h')))))))
  · rintro (⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ |
      ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ |
      ⟨ha, hb, hc⟩)
    · rw [ha, hb, hc, m11.1, m11.2.1, m11.2.2]; exact hy1
    · rw [ha, hb, hc, m12.1, m12.2.1, m12.2.2]; exact hy1
    · rw [ha, hb, hc, m13.1, m13.2.1, m13.2.2]; exact hy1
    · rw [ha, hb, hc, m21.1, m21.2.1, m21.2.2]; exact hy2
    · rw [ha, hb, hc, m22.1, m22.2.1, m22.2.2]; exact hy2
    · rw [ha, hb, hc, m23.1, m23.2.1, m23.2.2]; exact hy2
    · rw [ha, hb, hc, m31.1, m31.2.1, m31.2.2]; exact hy3
    · rw [ha, hb, hc, m32.1, m32.2.1, m32.2.2]; exact hy3
    · rw [ha, hb, hc, m33.1, m33.2.1, m33.2.2]; exact hy3

/-- A point differs from another when the first coordinates differ. -/
lemma ne_fst {a a' b b' c c' : ℝ} (h : a ≠ a') :
    (⟨a, b, c⟩ : ℝ × ℝ × ℝ) ≠ ⟨a', b', c'⟩ :=
  fun h' => h (congrArg Prod.fst h')

/-- Two points with different F1-images differ. -/
lemma ne_img {a a' b b' c c' r r' : ℝ}
    (i : F1 a b c = r) (i' : F1 a' b' c' = r') (h : r ≠ r') :
    (⟨a, b, c⟩ : ℝ × ℝ × ℝ) ≠ ⟨a', b', c'⟩ := by
  intro h'
  simp only [Prod.mk.injEq] at h'
  obtain ⟨e1, e2, e3⟩ := h'
  apply h
  rw [← i, ← i', e1, e2, e3]

/-- **The count**: a nine-element set containing precisely the solutions
of F(F x) = yNine. -/
theorem comp_nine_count :
    ∃ S : Finset (ℝ × ℝ × ℝ), S.card = 9 ∧
      ∀ a b c : ℝ,
        (F1 (F1 a b c) (F2 a b c) (F3 a b c) = ((-1643 : ℝ)/50) ∧
         F2 (F1 a b c) (F2 a b c) (F3 a b c) = ((3289 : ℝ)/100) ∧
         F3 (F1 a b c) (F2 a b c) (F3 a b c) = ((-71 : ℝ)/200)) ↔
        (a, b, c) ∈ S := by
  classical
  obtain ⟨r1, r2, r3, t11, t12, t13, t21, t22, t23, t31, t32, t33,
    h12, h23, ⟨o11, o12⟩, ⟨o21, o22⟩, ⟨o31, o32⟩,
    i11, i12, i13, i21, i22, i23, i31, i32, i33, hiff⟩ := comp_nine
  have n12 : r1 ≠ r2 := ne_of_lt h12
  have n13 : r1 ≠ r3 := ne_of_lt (lt_trans h12 h23)
  have n23 : r2 ≠ r3 := ne_of_lt h23
  refine ⟨{(t11, bStory t11 r1, cStory t11 r1),
           (t12, bStory t12 r1, cStory t12 r1),
           (t13, bStory t13 r1, cStory t13 r1),
           (t21, bStory t21 r2, cStory t21 r2),
           (t22, bStory t22 r2, cStory t22 r2),
           (t23, bStory t23 r2, cStory t23 r2),
           (t31, bStory t31 r3, cStory t31 r3),
           (t32, bStory t32 r3, cStory t32 r3),
           (t33, bStory t33 r3, cStory t33 r3)}, ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨ne_fst (ne_of_lt o11), ne_fst (ne_of_lt (lt_trans o11 o12)),
          ne_img i11 i21 n12, ne_img i11 i22 n12, ne_img i11 i23 n12,
          ne_img i11 i31 n13, ne_img i11 i32 n13, ne_img i11 i33 n13⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨ne_fst (ne_of_lt o12),
          ne_img i12 i21 n12, ne_img i12 i22 n12, ne_img i12 i23 n12,
          ne_img i12 i31 n13, ne_img i12 i32 n13, ne_img i12 i33 n13⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨ne_img i13 i21 n12, ne_img i13 i22 n12, ne_img i13 i23 n12,
          ne_img i13 i31 n13, ne_img i13 i32 n13, ne_img i13 i33 n13⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨ne_fst (ne_of_lt o21), ne_fst (ne_of_lt (lt_trans o21 o22)),
          ne_img i21 i31 n23, ne_img i21 i32 n23, ne_img i21 i33 n23⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨ne_fst (ne_of_lt o22),
          ne_img i22 i31 n23, ne_img i22 i32 n23, ne_img i22 i33 n23⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨ne_img i23 i31 n23, ne_img i23 i32 n23, ne_img i23 i33 n23⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_insert, Finset.mem_singleton]
        push Not
        exact ⟨ne_fst (ne_of_lt o31), ne_fst (ne_of_lt (lt_trans o31 o32))⟩),
      Finset.card_insert_of_notMem (by
        simp only [Finset.mem_singleton]
        exact ne_fst (ne_of_lt o32)),
      Finset.card_singleton]
  · intro a b c
    rw [hiff a b c]
    simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]

end KellerComp
