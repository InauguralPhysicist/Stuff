/-
  Bridge layer for the level-set certificates: the facts report §IV.2b
  quotes ("verified but unformalized") between the fiber cubic and the
  map F, proved.

  Global (all of ℝ³, y = F x): cubic_identity, shape2_identity,
  shape3_identity — fiber-cubic membership and both cleared shape-lemma
  relations hold identically under y = F(x).

  Per certified point X ∈ {Nine, Three, Five, Seven}:
    existsX1/2/3, g2X/g3X, nfBridgeX — data lemmas (all by ring), and
    fiber_X — **fiber determination**: F⁻¹ of the point is exactly the
    three certified preimages (ξ, P2X ξ, P3X ξ), ξ the roots of the
    fiber cubic CX, each carrying the published sign of the first-story
    wall polynomial L.  With KellerCerts this makes the first story of
    each n₂ certificate machine-checked end to end; the remaining quoted
    step is the second-story root count at the (algebraic) preimages.
-/
import KellerCerts

namespace KellerBridge
open KellerCerts

noncomputable def F1 (a b c : ℝ) : ℝ := (1 + a*b)^3*c + b^2*(1 + a*b)*(4 + 3*a*b)
noncomputable def F2 (a b c : ℝ) : ℝ := b + 3*a*(1 + a*b)^2*c + 3*a*b^2*(4 + 3*a*b)
noncomputable def F3 (a b c : ℝ) : ℝ := 2*a - 3*a^2*b - a^3*c
noncomputable def Lpoly (u v w : ℝ) : ℝ := 27*u^2*w^2 - 18*u*v*w + 16*u + v^3*w - v^2
noncomputable def Kpoly (u v w : ℝ) : ℝ := 27*u*w^2 - 9*v*w + 8
noncomputable def Bpoly (v w : ℝ) : ℝ := 4 - 3*v*w
noncomputable def G2side (a u v w : ℝ) : ℝ := ((-729 : ℝ)/1) * a^2 * u^3 * w^3 + ((567 : ℝ)/1) * a^2 * u^2 * v * w^2 + ((-432 : ℝ)/1) * a^2 * u^2 * w + ((-27 : ℝ)/1) * a^2 * u * v^3 * w^2 + ((-27 : ℝ)/1) * a^2 * u * v^2 * w + ((48 : ℝ)/1) * a^2 * u * v + ((3 : ℝ)/1) * a^2 * v^4 * w + ((-3 : ℝ)/1) * a^2 * v^3 + ((162 : ℝ)/1) * a * u^2 * w^2 + ((-108 : ℝ)/1) * a * u * v * w + ((96 : ℝ)/1) * a * u + ((6 : ℝ)/1) * a * v^3 * w + ((-6 : ℝ)/1) * a * v^2 + ((81 : ℝ)/1) * u * v * w^2 + ((-72 : ℝ)/1) * u * w + ((-15 : ℝ)/1) * v^2 * w + ((16 : ℝ)/1) * v
noncomputable def G3side (a u v w : ℝ) : ℝ := ((-6561 : ℝ)/1) * a^2 * u^3 * v^2 * w^4 + ((-4374 : ℝ)/1) * a^2 * u^3 * v * w^3 + ((11664 : ℝ)/1) * a^2 * u^3 * w^2 + ((6561 : ℝ)/1) * a^2 * u^2 * v^3 * w^3 + ((-3402 : ℝ)/1) * a^2 * u^2 * v^2 * w^2 + ((-10368 : ℝ)/1) * a^2 * u^2 * v * w + ((6912 : ℝ)/1) * a^2 * u^2 + ((-243 : ℝ)/1) * a^2 * u * v^5 * w^3 + ((-1377 : ℝ)/1) * a^2 * u * v^4 * w^2 + ((3510 : ℝ)/1) * a^2 * u * v^3 * w + ((-1872 : ℝ)/1) * a^2 * u * v^2 + ((81 : ℝ)/1) * a^2 * v^6 * w^2 + ((-171 : ℝ)/1) * a^2 * v^5 * w + ((90 : ℝ)/1) * a^2 * v^4 + ((4374 : ℝ)/1) * a * u^3 * v * w^4 + ((8748 : ℝ)/1) * a * u^3 * w^3 + ((-4374 : ℝ)/1) * a * u^2 * v^2 * w^3 + ((-2916 : ℝ)/1) * a * u^2 * v * w^2 + ((5184 : ℝ)/1) * a * u^2 * w + ((162 : ℝ)/1) * a * u * v^4 * w^3 + ((1134 : ℝ)/1) * a * u * v^3 * w^2 + ((-1404 : ℝ)/1) * a * u * v^2 * w + ((192 : ℝ)/1) * a * u * v + ((-54 : ℝ)/1) * a * v^5 * w^2 + ((66 : ℝ)/1) * a * v^4 * w + ((-12 : ℝ)/1) * a * v^3 + ((-2916 : ℝ)/1) * u^3 * w^4 + ((2916 : ℝ)/1) * u^2 * v * w^3 + ((-4536 : ℝ)/1) * u^2 * w^2 + ((621 : ℝ)/1) * u * v^3 * w^3 + ((-1026 : ℝ)/1) * u * v^2 * w^2 + ((504 : ℝ)/1) * u * v * w + ((64 : ℝ)/1) * u + ((-207 : ℝ)/1) * v^4 * w^2 + ((454 : ℝ)/1) * v^3 * w + ((-256 : ℝ)/1) * v^2

/-- Every x in the fiber over y = F x has x₁ on the fiber cubic of y. -/
theorem cubic_identity (a b c : ℝ) :
    Lpoly (F1 a b c) (F2 a b c) (F3 a b c) * a^3
      + Bpoly (F2 a b c) (F3 a b c) * a - 2 * F3 a b c = 0 := by
  simp only [F1, F2, F3, Lpoly, Bpoly]; ring

/-- The x₂ shape relation holds identically under y = F x. -/
theorem shape2_identity (a b c : ℝ) :
    2 * Kpoly (F1 a b c) (F2 a b c) (F3 a b c) * b
      = G2side a (F1 a b c) (F2 a b c) (F3 a b c) := by
  simp only [F1, F2, F3, Kpoly, G2side]; ring

/-- The x₃ shape relation holds identically under y = F x. -/
theorem shape3_identity (a b c : ℝ) :
    8 * Kpoly (F1 a b c) (F2 a b c) (F3 a b c) * c
      = G3side a (F1 a b c) (F2 a b c) (F3 a b c) := by
  simp only [F1, F2, F3, Kpoly, G3side]; ring

/-! ### The point yNine = (-1643/50, 3289/100, -71/200) -/
noncomputable def P2Nine (x : ℝ) : ℝ := ((7557258154586670603 : ℝ)/5086598000000) * x^2 + ((-10481968432539 : ℝ)/254329900) * x + ((-1117162377967 : ℝ)/508659800)
noncomputable def P3Nine (x : ℝ) : ℝ := ((7561158257994234686392280643 : ℝ)/40692784000000000000) * x^2 + ((-994551705419519304623529 : ℝ)/203463920000000000) * x + ((-1150482690851450136579 : ℝ)/4069278400000000)
noncomputable def H1Nine (x : ℝ) : ℝ := ((-934027168742611098626579536039431260824504897713721858784879939424220497 : ℝ)/26777477064671930490346752640000000000000000000000) * x^8 + ((399481778444811665273773385187627045676907860843329907658108208136191 : ℝ)/133887385323359652451733763200000000000000000000) * x^7 + ((176178896088516220297792611750607708360765780554966387685249048707 : ℝ)/2677747706467193049034675264000000000000000000) * x^6 + ((-48343408480223143242795362036819965605852205761584390071389 : ℝ)/6085790241970893293260625600000000000000) * x^5 + ((-22466745086781934557873240351281764440854021003065297357611 : ℝ)/267774770646719304903467526400000000000000) * x^4 + ((1688124565028377118798867655473119038039924123189793479 : ℝ)/267774770646719304903467526400000000000) * x^3 + ((2473230268700085221301393135469537483351899599431893 : ℝ)/26777477064671930490346752640000000000) * x^2 + ((-2692296285160489258396959409105093956981 : ℝ)/26321597524191935838400000000) * x + ((2771304270465241240261394449 : ℝ)/103493916854416000000)
noncomputable def H2Nine (x : ℝ) : ℝ := ((-370780175681465474870192891660283538859358446397671097 : ℝ)/5264319504838387167680000000000000000) * x^6 + ((107154567050553079515405970742120920708175904591891 : ℝ)/26321597524191935838400000000000000) * x^5 + ((37288083168541541229585550270593052204339873587 : ℝ)/263215975241919358384000000000000) * x^4 + ((-79555266994376138748753920389093139273757 : ℝ)/13160798762095967919200000000) * x^3 + ((-6866024035335720099453075115699877786337 : ℝ)/52643195048383871676800000000) * x^2 + ((8325752295555847187302063347 : ℝ)/103493916854416000000) * x + ((-15970312659 : ℝ)/5086598)
noncomputable def H3Nine (x : ℝ) : ℝ := ((2164047232156011 : ℝ)/203463920000) * x^2 + ((-9867 : ℝ)/400) * x + ((1 : ℝ)/2)

theorem existsNine1 (x : ℝ) :
    F1 x (P2Nine x) (P3Nine x) - ((-1643 : ℝ)/50) = H1Nine x * CNine x := by
  simp only [F1, P2Nine, P3Nine, H1Nine, CNine]; ring

theorem existsNine2 (x : ℝ) :
    F2 x (P2Nine x) (P3Nine x) - ((3289 : ℝ)/100) = H2Nine x * CNine x := by
  simp only [F2, P2Nine, P3Nine, H2Nine, CNine]; ring

theorem existsNine3 (x : ℝ) :
    F3 x (P2Nine x) (P3Nine x) - ((-71 : ℝ)/200) = H3Nine x * CNine x := by
  simp only [F3, P2Nine, P3Nine, H3Nine, CNine]; ring

theorem g2Nine (x : ℝ) :
    G2side x ((-1643 : ℝ)/50) ((3289 : ℝ)/100) ((-71 : ℝ)/200) = 2 * ((2543299 : ℝ)/2000000) * P2Nine x := by
  simp only [G2side, P2Nine]; ring

theorem g3Nine (x : ℝ) :
    G3side x ((-1643 : ℝ)/50) ((3289 : ℝ)/100) ((-71 : ℝ)/200) = 8 * ((2543299 : ℝ)/2000000) * P3Nine x := by
  simp only [G3side, P3Nine]; ring

theorem nfBridgeNine (x : ℝ) :
    ((41839807913549891391166801 : ℝ)/250000000000000000000000) * Lpoly x (P2Nine x) (P3Nine x) = NfNine x := by
  simp only [Lpoly, P2Nine, P3Nine, NfNine]; ring

theorem cNineEval (x : ℝ) :
    Lpoly ((-1643 : ℝ)/50) ((3289 : ℝ)/100) ((-71 : ℝ)/200) * x^3
      + Bpoly ((3289 : ℝ)/100) ((-71 : ℝ)/200) * x - 2 * ((-71 : ℝ)/200) = CNine x := by
  simp only [Lpoly, Bpoly, CNine]; ring

theorem kNineEval : Kpoly ((-1643 : ℝ)/50) ((3289 : ℝ)/100) ((-71 : ℝ)/200) = ((2543299 : ℝ)/2000000) := by
  simp only [Kpoly]; norm_num

/-- **Fiber determination at yNine**: F⁻¹ of the point is exactly the three
certified preimages, with the published L-sign at each. -/
theorem fiber_nine :
    ∃ r1 r2 r3 : ℝ, r1 < r2 ∧ r2 < r3 ∧
      (∀ a b c : ℝ,
        (F1 a b c = ((-1643 : ℝ)/50) ∧ F2 a b c = ((3289 : ℝ)/100) ∧ F3 a b c = ((-71 : ℝ)/200)) ↔
        ((a = r1 ∧ b = P2Nine r1 ∧ c = P3Nine r1) ∨
         (a = r2 ∧ b = P2Nine r2 ∧ c = P3Nine r2) ∨
         (a = r3 ∧ b = P2Nine r3 ∧ c = P3Nine r3))) ∧
      (Lpoly r1 (P2Nine r1) (P3Nine r1) < 0) ∧ (Lpoly r2 (P2Nine r2) (P3Nine r2) < 0) ∧ (Lpoly r3 (P2Nine r3) (P3Nine r3) < 0) := by
  obtain ⟨r1, r2, r3, h12, h23, hz1, hz2, hz3, hloc, hn1, hn2, hn3⟩ :=
    certificate_nine

  have hLneg : ∀ x : ℝ, NfNine x < 0 → Lpoly x (P2Nine x) (P3Nine x) < 0 := by
    intro x hnf
    by_contra hge
    rw [not_lt] at hge
    have hchain : (0 : ℝ) ≤ ((41839807913549891391166801 : ℝ)/250000000000000000000000) * Lpoly x (P2Nine x) (P3Nine x) := by
      linarith
    rw [nfBridgeNine x] at hchain
    linarith

  refine ⟨r1, r2, r3, h12, h23, ?_, hLneg r1 hn1, hLneg r2 hn2, hLneg r3 hn3⟩
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

/-! ### The point yThree = (-1249/10000, 9197/10000, 1267/5000) -/
noncomputable def P2Three (x : ℝ) : ℝ := ((-1893663543630615147883923 : ℝ)/2842995768106000000000000) * x^2 + ((-31441921950017409 : ℝ)/28429957681060000) * x + ((32953624099086323 : ℝ)/28429957681060000)
noncomputable def P3Three (x : ℝ) : ℝ := ((28232724680023916527277327364658853079 : ℝ)/5685991536212000000000000000000000000) * x^2 + ((157042592158666305148612936607631 : ℝ)/284299576810600000000000000000000) * x + ((-196345925406430891694496520043 : ℝ)/56859915362120000000000000000)
noncomputable def H1Three (x : ℝ) : ℝ := ((18292514897011693883588070349419767404933744558158304482709522310151232506270775288080614279031 : ℝ)/26131530351915877203426738116324838518101356559878400000000000000000000000000000000000000000000) * x^8 + ((4289534774791015823433477663759737861777104126566990681792218744937676423922069483698269159 : ℝ)/1306576517595793860171336905816241925905067827993920000000000000000000000000000000000000000) * x^7 + ((331193248022127906555938905507779197659768270954470483931058439771682718464923085307511 : ℝ)/261315303519158772034267381163248385181013565598784000000000000000000000000000000000000) * x^6 + ((-15639762412174255135977140347831641621513932951776089398300355160905255722800503 : ℝ)/1306576517595793860171336905816241925905067827993920000000000000000000000000000) * x^5 + ((-26695071472441652496217595497565529927203716437192876305426934033055293446566107 : ℝ)/2613153035191587720342673811632483851810135655987840000000000000000000000000000) * x^4 + ((375896154730789233073065061299229011034075940250782550804750977660972096967 : ℝ)/26131530351915877203426738116324838518101356559878400000000000000000000000) * x^3 + ((322799568189669474356861341063359838350534905281955621095832708160562569 : ℝ)/26131530351915877203426738116324838518101356559878400000000000000000000) * x^2 + ((-2281606387923925550444330763866915970708229618745301123 : ℝ)/459577369848226470862416317147618700320000000000000000) * x + ((-130518088038501795758474952708630777763 : ℝ)/32330499749874499707308944000000000000)
noncomputable def H2Three (x : ℝ) : ℝ := ((-28979564440376475756857575788834695974411956004940988930326063251498791 : ℝ)/9191547396964529417248326342952374006400000000000000000000000000000000) * x^6 + ((-4389765191358341328100261727072836209074494255100680198333337546799 : ℝ)/459577369848226470862416317147618700320000000000000000000000000000) * x^5 + ((214370624616200458215343000305799900331260417364047000092026169 : ℝ)/45957736984822647086241631714761870032000000000000000000000000) * x^4 + ((11403164362745392672854252162271873412821244680020952269 : ℝ)/459577369848226470862416317147618700320000000000000000) * x^3 + ((-1295824766392707167251895051554074179168982415274300391 : ℝ)/919154739696452941724832634295237400640000000000000000) * x^2 + ((-396574842675628509577826789112992333289 : ℝ)/32330499749874499707308944000000000000) * x + ((-5372211538923 : ℝ)/11371983072424)
noncomputable def H3Three (x : ℝ) : ℝ := ((2693797604825644357893 : ℝ)/1137198307242400000000) * x^2 + ((-27591 : ℝ)/40000) * x + ((1 : ℝ)/2)

theorem existsThree1 (x : ℝ) :
    F1 x (P2Three x) (P3Three x) - ((-1249 : ℝ)/10000) = H1Three x * CThree x := by
  simp only [F1, P2Three, P3Three, H1Three, CThree]; ring

theorem existsThree2 (x : ℝ) :
    F2 x (P2Three x) (P3Three x) - ((9197 : ℝ)/10000) = H2Three x * CThree x := by
  simp only [F2, P2Three, P3Three, H2Three, CThree]; ring

theorem existsThree3 (x : ℝ) :
    F3 x (P2Three x) (P3Three x) - ((1267 : ℝ)/5000) = H3Three x * CThree x := by
  simp only [F3, P2Three, P3Three, H3Three, CThree]; ring

theorem g2Three (x : ℝ) :
    G2side x ((-1249 : ℝ)/10000) ((9197 : ℝ)/10000) ((1267 : ℝ)/5000) = 2 * ((1421497884053 : ℝ)/250000000000) * P2Three x := by
  simp only [G2side, P2Three]; ring

theorem g3Three (x : ℝ) :
    G3side x ((-1249 : ℝ)/10000) ((9197 : ℝ)/10000) ((1267 : ℝ)/5000) = 8 * ((1421497884053 : ℝ)/250000000000) * P3Three x := by
  simp only [G3side, P3Three]; ring

theorem nfBridgeThree (x : ℝ) :
    ((4083051617486855813035427830675756018453336962481 : ℝ)/61035156250000000000000000000000000000000000) * Lpoly x (P2Three x) (P3Three x) = NfThree x := by
  simp only [Lpoly, P2Three, P3Three, NfThree]; ring

theorem cThreeEval (x : ℝ) :
    Lpoly ((-1249 : ℝ)/10000) ((9197 : ℝ)/10000) ((1267 : ℝ)/5000) * x^3
      + Bpoly ((9197 : ℝ)/10000) ((1267 : ℝ)/5000) * x - 2 * ((1267 : ℝ)/5000) = CThree x := by
  simp only [Lpoly, Bpoly, CThree]; ring

theorem kThreeEval : Kpoly ((-1249 : ℝ)/10000) ((9197 : ℝ)/10000) ((1267 : ℝ)/5000) = ((1421497884053 : ℝ)/250000000000) := by
  simp only [Kpoly]; norm_num

/-- **Fiber determination at yThree**: F⁻¹ of the point is exactly the three
certified preimages, with the published L-sign at each. -/
theorem fiber_three :
    ∃ r1 r2 r3 : ℝ, r1 < r2 ∧ r2 < r3 ∧
      (∀ a b c : ℝ,
        (F1 a b c = ((-1249 : ℝ)/10000) ∧ F2 a b c = ((9197 : ℝ)/10000) ∧ F3 a b c = ((1267 : ℝ)/5000)) ↔
        ((a = r1 ∧ b = P2Three r1 ∧ c = P3Three r1) ∨
         (a = r2 ∧ b = P2Three r2 ∧ c = P3Three r2) ∨
         (a = r3 ∧ b = P2Three r3 ∧ c = P3Three r3))) ∧
      (0 < Lpoly r1 (P2Three r1) (P3Three r1)) ∧ (0 < Lpoly r2 (P2Three r2) (P3Three r2)) ∧ (0 < Lpoly r3 (P2Three r3) (P3Three r3)) := by
  obtain ⟨r1, r2, r3, h12, h23, hz1, hz2, hz3, hloc, hn1, hn2, hn3⟩ :=
    certificate_three

  have hLpos : ∀ x : ℝ, 0 < NfThree x → 0 < Lpoly x (P2Three x) (P3Three x) := by
    intro x hnf
    by_contra hge
    rw [not_lt] at hge
    have hchain : ((4083051617486855813035427830675756018453336962481 : ℝ)/61035156250000000000000000000000000000000000) * Lpoly x (P2Three x) (P3Three x) ≤ (0 : ℝ) := by
      linarith
    rw [nfBridgeThree x] at hchain
    linarith

  refine ⟨r1, r2, r3, h12, h23, ?_, hLpos r1 hn1, hLpos r2 hn2, hLpos r3 hn3⟩
  intro a b c
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hcube := cubic_identity a b c
    rw [h1, h2, h3, cThreeEval] at hcube
    have hb : b = P2Three a := by
      have hs := shape2_identity a b c
      rw [h1, h2, h3, g2Three, kThreeEval] at hs
      exact mul_left_cancel₀
        (by norm_num : (2 * ((1421497884053 : ℝ)/250000000000) : ℝ) ≠ 0) hs
    have hc : c = P3Three a := by
      have hs := shape3_identity a b c
      rw [h1, h2, h3, g3Three, kThreeEval] at hs
      exact mul_left_cancel₀
        (by norm_num : (8 * ((1421497884053 : ℝ)/250000000000) : ℝ) ≠ 0) hs
    rcases hloc a hcube with ha | ha | ha
    · exact Or.inl ⟨ha, by rw [← ha]; exact hb, by rw [← ha]; exact hc⟩
    · exact Or.inr (Or.inl ⟨ha, by rw [← ha]; exact hb, by rw [← ha]; exact hc⟩)
    · exact Or.inr (Or.inr ⟨ha, by rw [← ha]; exact hb, by rw [← ha]; exact hc⟩)
  · have hback : ∀ r : ℝ, CThree r = 0 →
        F1 r (P2Three r) (P3Three r) = ((-1249 : ℝ)/10000) ∧
        F2 r (P2Three r) (P3Three r) = ((9197 : ℝ)/10000) ∧
        F3 r (P2Three r) (P3Three r) = ((1267 : ℝ)/5000) := by
      intro r hr
      have e1 := existsThree1 r
      have e2 := existsThree2 r
      have e3 := existsThree3 r
      rw [hr, mul_zero] at e1 e2 e3
      exact ⟨by linarith, by linarith, by linarith⟩
    rintro (⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩)
    · rw [ha, hb, hc]; exact hback r1 hz1
    · rw [ha, hb, hc]; exact hback r2 hz2
    · rw [ha, hb, hc]; exact hback r3 hz3

/-! ### The point yFive = (-29083/10000, -7379/5000, 6249/10000) -/
noncomputable def P2Five (x : ℝ) : ℝ := ((87662390975896884428442273 : ℝ)/5745446022096400000000000) * x^2 + ((58909848616145091 : ℝ)/28727230110482000) * x + ((-1112923541264030017 : ℝ)/143636150552410000)
noncomputable def P3Five (x : ℝ) : ℝ := ((-711109660588296909806896321630712919687 : ℝ)/5745446022096400000000000000000000000) * x^2 + ((-20054914544139506096578292863121151 : ℝ)/574544602209640000000000000000000) * x + ((24147460920044910926068278857531 : ℝ)/287272301104820000000000000000)
noncomputable def H1Five (x : ℝ) : ℝ := ((24395507772867465470477728525693383683667357141352571727958465084388168661058135608239649733451640807 : ℝ)/544835001274347590735173712137772914623821396966688780800000000000000000000000000000000000000000) * x^8 + ((769437451473448288134029907474403259375153110819631991805485364843820043589389372001170921742911 : ℝ)/54483500127434759073517371213777291462382139696668878080000000000000000000000000000000000000) * x^7 + ((-1883751532000975865976905179481965669939244722570466259254262561886686262070088512731304169303 : ℝ)/27241750063717379536758685606888645731191069848334439040000000000000000000000000000000000) * x^6 + ((-594325318747960517119454116111955877212138091476744084497577594601862261516379688633 : ℝ)/136208750318586897683793428034443228655955349241672195200000000000000000000000000) * x^5 + ((13352588064821844668871482908997081028626782217710850705694517778734307236489187396661 : ℝ)/340521875796467244209483570086108071639888373104180488000000000000000000000000000) * x^4 + ((-113533108674276422618787931207764043494798208917812416689492840436782796169196249 : ℝ)/17026093789823362210474178504305403581994418655209024400000000000000000000000) * x^3 + ((-63456782593386422099408749472983385528699826930683578988166808909213713010623 : ℝ)/8513046894911681105237089252152701790997209327604512200000000000000000000) * x^2 + ((341536757034793648271168463666035214760683164350697867151081 : ℝ)/118536271853170251890379961155604694500840000000000000000) * x + ((-215990447684389836522819303855051233498779 : ℝ)/825253749820583661926272324000000000000)
noncomputable def H2Five (x : ℝ) : ℝ := ((834867980485785698362654509407649558198676826968544737602734017099325513877 : ℝ)/94829017482536201512303968924483755600672000000000000000000000000000000) * x^6 + ((15111080279419720477138941925205924362594128419358879551222956274937021 : ℝ)/9482901748253620151230396892448375560067200000000000000000000000000) * x^5 + ((-44283360735376453807106457924219011138538335379499879260115247240667 : ℝ)/4741450874126810075615198446224187780033600000000000000000000000) * x^4 + ((7462296970523393405343792489229712521123826679832107650901 : ℝ)/11853627185317025189037996115560469450084000000000000000) * x^3 + ((164649167950734286953475568006718888610977639374901567452757 : ℝ)/59268135926585125945189980577802347250420000000000000000) * x^2 + ((-621140088105556452530126655058756300496337 : ℝ)/825253749820583661926272324000000000000) * x + ((144174317535411 : ℝ)/28727230110482)
noncomputable def H3Five (x : ℝ) : ℝ := ((-36213452111642691433671 : ℝ)/2872723011048200000000) * x^2 + ((22137 : ℝ)/20000) * x + ((1 : ℝ)/2)

theorem existsFive1 (x : ℝ) :
    F1 x (P2Five x) (P3Five x) - ((-29083 : ℝ)/10000) = H1Five x * CFive x := by
  simp only [F1, P2Five, P3Five, H1Five, CFive]; ring

theorem existsFive2 (x : ℝ) :
    F2 x (P2Five x) (P3Five x) - ((-7379 : ℝ)/5000) = H2Five x * CFive x := by
  simp only [F2, P2Five, P3Five, H2Five, CFive]; ring

theorem existsFive3 (x : ℝ) :
    F3 x (P2Five x) (P3Five x) - ((6249 : ℝ)/10000) = H3Five x * CFive x := by
  simp only [F3, P2Five, P3Five, H3Five, CFive]; ring

theorem g2Five (x : ℝ) :
    G2side x ((-29083 : ℝ)/10000) ((-7379 : ℝ)/5000) ((6249 : ℝ)/10000) = 2 * ((-14363615055241 : ℝ)/1000000000000) * P2Five x := by
  simp only [G2side, P2Five]; ring

theorem g3Five (x : ℝ) :
    G3side x ((-29083 : ℝ)/10000) ((-7379 : ℝ)/5000) ((6249 : ℝ)/10000) = 8 * ((-14363615055241 : ℝ)/1000000000000) * P3Five x := by
  simp only [G3side, P3Five]; ring

theorem nfBridgeFive (x : ℝ) :
    ((42565234474558405526185446260763508954986046638022561 : ℝ)/15625000000000000000000000000000000000000000000) * Lpoly x (P2Five x) (P3Five x) = NfFive x := by
  simp only [Lpoly, P2Five, P3Five, NfFive]; ring

theorem cFiveEval (x : ℝ) :
    Lpoly ((-29083 : ℝ)/10000) ((-7379 : ℝ)/5000) ((6249 : ℝ)/10000) * x^3
      + Bpoly ((-7379 : ℝ)/5000) ((6249 : ℝ)/10000) * x - 2 * ((6249 : ℝ)/10000) = CFive x := by
  simp only [Lpoly, Bpoly, CFive]; ring

theorem kFiveEval : Kpoly ((-29083 : ℝ)/10000) ((-7379 : ℝ)/5000) ((6249 : ℝ)/10000) = ((-14363615055241 : ℝ)/1000000000000) := by
  simp only [Kpoly]; norm_num

/-- **Fiber determination at yFive**: F⁻¹ of the point is exactly the three
certified preimages, with the published L-sign at each. -/
theorem fiber_five :
    ∃ r1 r2 r3 : ℝ, r1 < r2 ∧ r2 < r3 ∧
      (∀ a b c : ℝ,
        (F1 a b c = ((-29083 : ℝ)/10000) ∧ F2 a b c = ((-7379 : ℝ)/5000) ∧ F3 a b c = ((6249 : ℝ)/10000)) ↔
        ((a = r1 ∧ b = P2Five r1 ∧ c = P3Five r1) ∨
         (a = r2 ∧ b = P2Five r2 ∧ c = P3Five r2) ∨
         (a = r3 ∧ b = P2Five r3 ∧ c = P3Five r3))) ∧
      (0 < Lpoly r1 (P2Five r1) (P3Five r1)) ∧ (Lpoly r2 (P2Five r2) (P3Five r2) < 0) ∧ (0 < Lpoly r3 (P2Five r3) (P3Five r3)) := by
  obtain ⟨r1, r2, r3, h12, h23, hz1, hz2, hz3, hloc, hn1, hn2, hn3⟩ :=
    certificate_five

  have hLneg : ∀ x : ℝ, NfFive x < 0 → Lpoly x (P2Five x) (P3Five x) < 0 := by
    intro x hnf
    by_contra hge
    rw [not_lt] at hge
    have hchain : (0 : ℝ) ≤ ((42565234474558405526185446260763508954986046638022561 : ℝ)/15625000000000000000000000000000000000000000000) * Lpoly x (P2Five x) (P3Five x) := by
      linarith
    rw [nfBridgeFive x] at hchain
    linarith

  have hLpos : ∀ x : ℝ, 0 < NfFive x → 0 < Lpoly x (P2Five x) (P3Five x) := by
    intro x hnf
    by_contra hge
    rw [not_lt] at hge
    have hchain : ((42565234474558405526185446260763508954986046638022561 : ℝ)/15625000000000000000000000000000000000000000000) * Lpoly x (P2Five x) (P3Five x) ≤ (0 : ℝ) := by
      linarith
    rw [nfBridgeFive x] at hchain
    linarith

  refine ⟨r1, r2, r3, h12, h23, ?_, hLpos r1 hn1, hLneg r2 hn2, hLpos r3 hn3⟩
  intro a b c
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hcube := cubic_identity a b c
    rw [h1, h2, h3, cFiveEval] at hcube
    have hb : b = P2Five a := by
      have hs := shape2_identity a b c
      rw [h1, h2, h3, g2Five, kFiveEval] at hs
      exact mul_left_cancel₀
        (by norm_num : (2 * ((-14363615055241 : ℝ)/1000000000000) : ℝ) ≠ 0) hs
    have hc : c = P3Five a := by
      have hs := shape3_identity a b c
      rw [h1, h2, h3, g3Five, kFiveEval] at hs
      exact mul_left_cancel₀
        (by norm_num : (8 * ((-14363615055241 : ℝ)/1000000000000) : ℝ) ≠ 0) hs
    rcases hloc a hcube with ha | ha | ha
    · exact Or.inl ⟨ha, by rw [← ha]; exact hb, by rw [← ha]; exact hc⟩
    · exact Or.inr (Or.inl ⟨ha, by rw [← ha]; exact hb, by rw [← ha]; exact hc⟩)
    · exact Or.inr (Or.inr ⟨ha, by rw [← ha]; exact hb, by rw [← ha]; exact hc⟩)
  · have hback : ∀ r : ℝ, CFive r = 0 →
        F1 r (P2Five r) (P3Five r) = ((-29083 : ℝ)/10000) ∧
        F2 r (P2Five r) (P3Five r) = ((-7379 : ℝ)/5000) ∧
        F3 r (P2Five r) (P3Five r) = ((6249 : ℝ)/10000) := by
      intro r hr
      have e1 := existsFive1 r
      have e2 := existsFive2 r
      have e3 := existsFive3 r
      rw [hr, mul_zero] at e1 e2 e3
      exact ⟨by linarith, by linarith, by linarith⟩
    rintro (⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩)
    · rw [ha, hb, hc]; exact hback r1 hz1
    · rw [ha, hb, hc]; exact hback r2 hz2
    · rw [ha, hb, hc]; exact hback r3 hz3

/-! ### The point ySeven = (-320873/10000, 30951/1000, -1611/10000) -/
noncomputable def P2Seven (x : ℝ) : ℝ := ((392722139673500322632590530117 : ℝ)/60782214297418000000000000) * x^2 + ((-252191529965837591871 : ℝ)/303911071487090000) * x + ((350173681905876777 : ℝ)/60782214297418000)
noncomputable def P3Seven (x : ℝ) : ℝ := ((26820272631075754168319036046997531088868417 : ℝ)/2431288571896720000000000000000000000) * x^2 + ((-260783547854607208338113756801220026589 : ℝ)/1215644285948360000000000000000000) * x + ((-11053758254996945141363030630549237 : ℝ)/607822142974180000000000000000)
noncomputable def H1Seven (x : ℝ) : ℝ := ((-19324581717001350888061702504660650282151049781551071508010555714287744985660135662735956577769258535090530231753 : ℝ)/54596658205674518155008460896241247585109734690237168704000000000000000000000000000000000000000000) * x^8 + ((3893780229151854304192751638501721325922550152240211236268469474099490503541939651716567016895383984347011301 : ℝ)/27298329102837259077504230448120623792554867345118584352000000000000000000000000000000000000000) * x^7 + ((-286760010074500343636478531340193679657436603933663299698739368152290494552983045428717915969053279027367 : ℝ)/13649164551418629538752115224060311896277433672559292176000000000000000000000000000000000000) * x^6 + ((82389647689969716717005451794631199523096154359831763515237070253891420245129987431873900864613 : ℝ)/68245822757093147693760576120301559481387168362796460880000000000000000000000000000) * x^5 + ((221598503777317695627876615448216459462354084245273883216691755745516781762406889643323901 : ℝ)/54596658205674518155008460896241247585109734690237168704000000000000000000000000) * x^4 + ((-2593749977093776361018735089477244073901360807104722760840403305044361247905790902009771 : ℝ)/853072784463664346172007201503769493517339604534955761000000000000000000000000) * x^3 + ((20467880143752961184656550322667194942045500708341093287435341529586188460756143 : ℝ)/272983291028372590775042304481206237925548673451185843520000000000000000) * x^2 + ((344736727003925886513105185670170125819162039502970657345521019 : ℝ)/224558527674409513198788491440983646118632000000000000000) * x + ((-206636120622038122582050145639994458034578203 : ℝ)/3694477574897245135361466724000000000000)
noncomputable def H2Seven (x : ℝ) : ℝ := ((-147620261997966349896681601950885336627245056291196098431547863665401374260455191327 : ℝ)/898234110697638052795153965763934584474528000000000000000000000000000000) * x^6 + ((20264919928755633762195968550363373059598161156718958587764609742628487476821059 : ℝ)/449117055348819026397576982881967292237264000000000000000000000000000) * x^5 + ((-856312128695735282763420249068456115635349265202117890949282056931851866003 : ℝ)/224558527674409513198788491440983646118632000000000000000000000000) * x^4 + ((31433841701865991323102129501443259480319129451837727730821572439 : ℝ)/561396319186023782996971228602459115296580000000000000000) * x^3 + ((4933476750831611538782309906449521860493541806711405621763353 : ℝ)/898234110697638052795153965763934584474528000000000000) * x^2 + ((-613531668426947335087481084092155939103734609 : ℝ)/3694477574897245135361466724000000000000) * x + ((-4752006929899155 : ℝ)/60782214297418)
noncomputable def H3Seven (x : ℝ) : ℝ := ((319046471957748375974781 : ℝ)/243128857189672000000) * x^2 + ((-92853 : ℝ)/4000) * x + ((1 : ℝ)/2)

theorem existsSeven1 (x : ℝ) :
    F1 x (P2Seven x) (P3Seven x) - ((-320873 : ℝ)/10000) = H1Seven x * CSeven x := by
  simp only [F1, P2Seven, P3Seven, H1Seven, CSeven]; ring

theorem existsSeven2 (x : ℝ) :
    F2 x (P2Seven x) (P3Seven x) - ((30951 : ℝ)/1000) = H2Seven x * CSeven x := by
  simp only [F2, P2Seven, P3Seven, H2Seven, CSeven]; ring

theorem existsSeven3 (x : ℝ) :
    F3 x (P2Seven x) (P3Seven x) - ((-1611 : ℝ)/10000) = H3Seven x * CSeven x := by
  simp only [F3, P2Seven, P3Seven, H3Seven, CSeven]; ring

theorem g2Seven (x : ℝ) :
    G2side x ((-320873 : ℝ)/10000) ((30951 : ℝ)/1000) ((-1611 : ℝ)/10000) = 2 * ((30391107148709 : ℝ)/1000000000000) * P2Seven x := by
  simp only [G2side, P2Seven]; ring

theorem g3Seven (x : ℝ) :
    G3side x ((-320873 : ℝ)/10000) ((30951 : ℝ)/1000) ((-1611 : ℝ)/10000) = 8 * ((30391107148709 : ℝ)/1000000000000) * P3Seven x := by
  simp only [G3side, P3Seven]; ring

theorem nfBridgeSeven (x : ℝ) :
    ((853072784463664346172007201503769493517339604534955761 : ℝ)/15625000000000000000000000000000000000000000000) * Lpoly x (P2Seven x) (P3Seven x) = NfSeven x := by
  simp only [Lpoly, P2Seven, P3Seven, NfSeven]; ring

theorem cSevenEval (x : ℝ) :
    Lpoly ((-320873 : ℝ)/10000) ((30951 : ℝ)/1000) ((-1611 : ℝ)/10000) * x^3
      + Bpoly ((30951 : ℝ)/1000) ((-1611 : ℝ)/10000) * x - 2 * ((-1611 : ℝ)/10000) = CSeven x := by
  simp only [Lpoly, Bpoly, CSeven]; ring

theorem kSevenEval : Kpoly ((-320873 : ℝ)/10000) ((30951 : ℝ)/1000) ((-1611 : ℝ)/10000) = ((30391107148709 : ℝ)/1000000000000) := by
  simp only [Kpoly]; norm_num

/-- **Fiber determination at ySeven**: F⁻¹ of the point is exactly the three
certified preimages, with the published L-sign at each. -/
theorem fiber_seven :
    ∃ r1 r2 r3 : ℝ, r1 < r2 ∧ r2 < r3 ∧
      (∀ a b c : ℝ,
        (F1 a b c = ((-320873 : ℝ)/10000) ∧ F2 a b c = ((30951 : ℝ)/1000) ∧ F3 a b c = ((-1611 : ℝ)/10000)) ↔
        ((a = r1 ∧ b = P2Seven r1 ∧ c = P3Seven r1) ∨
         (a = r2 ∧ b = P2Seven r2 ∧ c = P3Seven r2) ∨
         (a = r3 ∧ b = P2Seven r3 ∧ c = P3Seven r3))) ∧
      (0 < Lpoly r1 (P2Seven r1) (P3Seven r1)) ∧ (Lpoly r2 (P2Seven r2) (P3Seven r2) < 0) ∧ (Lpoly r3 (P2Seven r3) (P3Seven r3) < 0) := by
  obtain ⟨r1, r2, r3, h12, h23, hz1, hz2, hz3, hloc, hn1, hn2, hn3⟩ :=
    certificate_seven

  have hLneg : ∀ x : ℝ, NfSeven x < 0 → Lpoly x (P2Seven x) (P3Seven x) < 0 := by
    intro x hnf
    by_contra hge
    rw [not_lt] at hge
    have hchain : (0 : ℝ) ≤ ((853072784463664346172007201503769493517339604534955761 : ℝ)/15625000000000000000000000000000000000000000000) * Lpoly x (P2Seven x) (P3Seven x) := by
      linarith
    rw [nfBridgeSeven x] at hchain
    linarith

  have hLpos : ∀ x : ℝ, 0 < NfSeven x → 0 < Lpoly x (P2Seven x) (P3Seven x) := by
    intro x hnf
    by_contra hge
    rw [not_lt] at hge
    have hchain : ((853072784463664346172007201503769493517339604534955761 : ℝ)/15625000000000000000000000000000000000000000000) * Lpoly x (P2Seven x) (P3Seven x) ≤ (0 : ℝ) := by
      linarith
    rw [nfBridgeSeven x] at hchain
    linarith

  refine ⟨r1, r2, r3, h12, h23, ?_, hLpos r1 hn1, hLneg r2 hn2, hLneg r3 hn3⟩
  intro a b c
  constructor
  · rintro ⟨h1, h2, h3⟩
    have hcube := cubic_identity a b c
    rw [h1, h2, h3, cSevenEval] at hcube
    have hb : b = P2Seven a := by
      have hs := shape2_identity a b c
      rw [h1, h2, h3, g2Seven, kSevenEval] at hs
      exact mul_left_cancel₀
        (by norm_num : (2 * ((30391107148709 : ℝ)/1000000000000) : ℝ) ≠ 0) hs
    have hc : c = P3Seven a := by
      have hs := shape3_identity a b c
      rw [h1, h2, h3, g3Seven, kSevenEval] at hs
      exact mul_left_cancel₀
        (by norm_num : (8 * ((30391107148709 : ℝ)/1000000000000) : ℝ) ≠ 0) hs
    rcases hloc a hcube with ha | ha | ha
    · exact Or.inl ⟨ha, by rw [← ha]; exact hb, by rw [← ha]; exact hc⟩
    · exact Or.inr (Or.inl ⟨ha, by rw [← ha]; exact hb, by rw [← ha]; exact hc⟩)
    · exact Or.inr (Or.inr ⟨ha, by rw [← ha]; exact hb, by rw [← ha]; exact hc⟩)
  · have hback : ∀ r : ℝ, CSeven r = 0 →
        F1 r (P2Seven r) (P3Seven r) = ((-320873 : ℝ)/10000) ∧
        F2 r (P2Seven r) (P3Seven r) = ((30951 : ℝ)/1000) ∧
        F3 r (P2Seven r) (P3Seven r) = ((-1611 : ℝ)/10000) := by
      intro r hr
      have e1 := existsSeven1 r
      have e2 := existsSeven2 r
      have e3 := existsSeven3 r
      rw [hr, mul_zero] at e1 e2 e3
      exact ⟨by linarith, by linarith, by linarith⟩
    rintro (⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩ | ⟨ha, hb, hc⟩)
    · rw [ha, hb, hc]; exact hback r1 hz1
    · rw [ha, hb, hc]; exact hback r2 hz2
    · rw [ha, hb, hc]; exact hback r3 hz3

end KellerBridge
