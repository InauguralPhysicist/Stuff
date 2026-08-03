/-
  Bridge layer, phase 1: the facts report §IV.2b quotes ("verified but
  unformalized") between the fiber cubic and the map F, now proved.

  Global (all of ℝ³, y = F x):
    · cubic_identity   — x₁ of any preimage satisfies the fiber cubic
    · shape2_identity  — 2·K(Fx)·x₂ equals a polynomial in (x₁, Fx)
    · shape3_identity  — 8·K(Fx)·x₃ equals a polynomial in (x₁, Fx)
  At the n₂ = 9 point (KellerCerts.certificate_nine):
    · existsNine₁₂₃    — the candidate map ξ ↦ (ξ, P2Nine ξ, P3Nine ξ)
                         lands exactly on the fiber when CNine ξ = 0
    · g2Nine, g3Nine   — the shape relations at this point pin x₂, x₃ to
                         P2Nine x₁, P3Nine x₁  (K ≠ 0 numerically)
    · nfBridgeNine     — 64·K⁴·L(candidate ξ) = NfNine ξ, so the
                         certificate's Nf-signs are the sibling L-signs
  Phase 2 (next): assemble these into "F⁻¹(y₉) has exactly the three
  certified points, all with L < 0", then the second story.
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

/-! ### The n₂ = 9 point -/
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

/-- At the certified point, the shape relation for x₂ evaluates to
2·K·P2Nine (K = Kpoly at the point, nonzero). -/
theorem g2Nine (x : ℝ) :
    G2side x ((-1643 : ℝ)/50) ((3289 : ℝ)/100) ((-71 : ℝ)/200)
      = 2 * (((2543299 : ℝ)/2000000)) * P2Nine x := by
  simp only [G2side, P2Nine]; ring

theorem g3Nine (x : ℝ) :
    G3side x ((-1643 : ℝ)/50) ((3289 : ℝ)/100) ((-71 : ℝ)/200)
      = 8 * (((2543299 : ℝ)/2000000)) * P3Nine x := by
  simp only [G3side, P3Nine]; ring

/-- The certified Nf-signs are sibling L-signs: 64·K⁴·L(candidate) = Nf. -/
theorem nfBridgeNine (x : ℝ) :
    ((41839807913549891391166801 : ℝ)/250000000000000000000000) * Lpoly x (P2Nine x) (P3Nine x) = NfNine x := by
  simp only [Lpoly, P2Nine, P3Nine, NfNine]; ring

end KellerBridge
