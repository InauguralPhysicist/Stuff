# Source note and its companion artifacts

This directory archives the object of verification — the note that
`../keller_quantization_report.md` independently verifies — together with its
companion and earlier-draft scripts, so the repository is self-contained.

## Hash verification

The report header pins the note and its companion script by SHA-256
(abbreviated there as `f2c9aa14…327a6b612` and `09303167…daa453f91`). The
files archived here match those pins byte for byte. Full digests:

| File | SHA-256 |
|---|---|
| `kellermapoperators.md` | `f2c9aa1415f6bf094aa95df807031f971cebd84426c9f34656f2877327a6b612` |
| `fiber_and_escape.py` | `0930316714a5720e0c63b582b50b3b5e25654e72b32ad817e408835daa453f91` |
| `spectrum.py` | `2b5dcef64aaefe42a59236aed079986faf7b1751c03fc25c55dfd6942619dcbc` |
| `errata_check.py` | `a4c2553933d5974e26b0d4f7d7582e69b5a008fe8abf00fad18a3b19c9c5fb68` |
| `quantum.py` | `7d947702bf2a1fea55bcfcbc38e7f04db14a175a29a7fb89da631e020c2ebf45` |

Re-verify with `sha256sum` in this directory; the first two are the digests
the report certifies.

## Contents

- **`kellermapoperators.md`** — the source note, *"A Non-Regular Heisenberg
  System from the Alpöge Keller Map"*: the CCR construction from Alpöge's
  Jacobian-conjecture counterexample, the fiber cubic and wall polynomial L,
  the Stone–von Neumann failure, and the four open questions the report
  addresses.
- **`fiber_and_escape.py`** — the note's shipped companion script: exact
  fiber counts via sign(L) and escape-time prediction along the P′ flows.
  This is the replacement for the fragile resultant sampler.
- **`quantum.py`** — the note's symbolic verification of its §3 identities
  (A·DFᵀ = I, Piola divergences, commutator coefficients, intertwining).
- **`spectrum.py`** — the **earlier-draft** sampler and flow test, preserved
  as a historical artifact: it contains the exact defects dissected in the
  note's Appendix A — the `abs(r) < 1e-9` root discard of erratum A.1 (drops
  the x₁ = 0 sheet) and the shrinking adaptive step of erratum A.2 (creeps
  toward the blowup and reports "no escape" from data that does blow up). Do
  not use it for results; that is the point of keeping it.
- **`errata_check.py`** — the diagnosis script behind Appendix A: recomputes
  the keystone claims exactly and reproduces, then explains, the earlier
  draft's wrong numbers (including the seed-11 "n = 2" sample).

## Provenance

Alpöge's map is dated 20 July 2026; the note's literature search is dated
31 July 2026. These files are archived unmodified — any fix or follow-up
belongs in the report layer at the repository root, never in edits here,
since the hashes above are what the report's verification refers to.
