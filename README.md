# The Alpöge Keller Map as a Quantum System

Independent verification and new results for the note *"A Non-Regular
Heisenberg System from the Alpöge Keller Map"*, together with
machine-checked Lean 4 layers for Part IV — the level-set certificates,
fiber determination at every certified point, and the full n₂ = 9
tower step assembled end to end.

The full write-up is [`keller_quantization_report.md`](keller_quantization_report.md)
(revision 9). Headline outcomes:

- **Part I** — every checkable claim of the source note verified, with one
  error found and corrected (§10's characterization of boundary-reaching
  directions).
- **Part II** — Open Questions 1 and 2 settled: P′₁ has deficiency indices
  (∞, ∞), and the wall {L = 0} has a cuspidal edge along the empty-fiber
  curve.
- **Part III** — Open Question 3 answered, including the **ladder no-go
  theorem**: no self-adjoint extension contains the transported oscillator
  ladder.
- **Part IV** — the tower F, F², F³ separated exactly:
  spec(C₂\*C₂) = {1, 3, 5, 7, 9} with exact rational certificates, each one
  machine-checked in Lean.
- **Part IV, formalized end to end** — the bridge/depth/existence/composition
  layers prove fiber determination at all four certified points and assemble
  `comp_nine`: F ∘ F has exactly nine real preimages over the n₂ = 9 point,
  machine-checking the tower step 9 = 3 × 3 that report §IV.2 quotes.
- **F⁴** — the tower extended one story: exact certificate n₄ ≥ 13, so
  S_{F⁴} is inequivalent to S_{F²} and S_F (F⁴ vs F³ remains open).

## Repository contents

| File | What it is |
|---|---|
| `keller_quantization_report.md` | The report (revision 9) |
| `keller_quantization.py` | Companion code — eight subcommands reproduce every number in the report |
| `KellerCerts.lean` | Lean 4 certificates for the Part IV level sets (n₂ = 3, 5, 7, 9) |
| `KellerBridge.lean` | Bridge layer — global fiber-cubic/shape identities, and fiber determination at the four certified points |
| `KellerDepth.lean` | Depth layer — second story of the n₂ = 9 certificate (three roots over each first-story preimage) |
| `KellerExist.lean` | Existence layer — global existence lemmas in memory-bounded split-chain form |
| `KellerComp.lean` | Composition layer — `comp_nine`: F ∘ F has exactly nine preimages over the n₂ = 9 point |
| `KellerTower.lean` | Tower layer — `tower_eleven`: eleven distinct F³-preimages of y\* = F(z\*), so n₃(y\*) ≥ 11 pointwise |
| `KellerOpen.lean` | Openness layer — `tower_eleven_nhds`: the eleven preimages persist on a neighborhood of y\* (explicit inverse Jacobian, det DF ≡ −2, inverse function theorem) |
| `AxiomCheck.lean` | `#print axioms` audit of every certificate |
| `tower4_certificate.py` | Exact F⁴ certificate: n₄ ≥ 13 at Y = F(F(z\*)) |
| `friedrichs_levels.html` | Figure: Friedrichs spectrum of the transformed oscillator (Part III) |
| `source-note/` | The verified note and its companion scripts, archived with matching SHA-256 (see its README) |
| `lakefile.toml`, `lean-toolchain` | Lake build config, pinned to Lean 4 / mathlib v4.32.0 |

## Lean certificates

Requires [elan](https://github.com/leanprover/elan); the toolchain is pinned
by `lean-toolchain`.

```sh
lake update            # resolve mathlib (first run only; commit lake-manifest.json)
lake exe cache get     # download prebuilt mathlib oleans (highly recommended)
lake build KellerCerts KellerBridge KellerDepth KellerExist KellerComp KellerTower
                       # check all certificate layers
lake build AxiomCheck  # print the axioms each certificate depends on
```

The axiom check should report only the three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) — no `sorry`.

The existence and composition layers elaborate large ring identities;
set `LEAN_NUM_THREADS=1` (as CI does) to keep peak memory bounded —
concurrent heavy ring checks stack their peaks and can OOM a 16 GB
machine.

CI builds every layer and enforces the axiom allowlist on every push
(see `.github/workflows/ci.yml`).

## Python verification suite

```sh
pip install -r requirements.txt
python keller_quantization.py --help
```

Subcommands map to the report as follows:

| Subcommand | Report section |
|---|---|
| `verify` | Part I — symbolic identities, fiber structure, direction census |
| `singular` | Theorem 2 — singular locus and A₂ criterion |
| `fates` | Theorem 1 — algebraic trajectory fates with the exchange rule |
| `boundary` | I.2/I.3 — origin-lift fates per direction |
| `spectrum` | Part III — Friedrichs spectrum (`--bc dirichlet\|neumann\|glue`) |
| `nogo` | III.4 — ladder no-go overlap |
| `monodromy` | IV.4 — covering monodromy over {L < 0} |
| `tower` | Part IV — multiplicity certificates for F² and F³ (`--exact3`) |

Defaults are sized for a quick run; the published figures used larger
parameters noted in each subcommand's `--help` (e.g. the direction census
used `--dirs 400000` over ten seeds, the no-go Monte Carlo 4×10⁷ samples).

The F⁴ extension is a standalone script (everything exact over ℚ or
ℚ[u]/Qr; CI runs it on every push):

```sh
python tower4_certificate.py   # exact certificate n₄ ≥ 13
```

## The trust ledger

Facts the machine-checked layers quote rather than prove, each with its
status.  "Done" for a claim means proved above this ledger; the ledger is
the definition of the remaining frontier, and it shrinks release by
release.

| Quoted fact | Status |
|---|---|
| n_k = fiber count of F^k (the operator bridge, §I.1/§IV) | Deliberate trust boundary — verified in the report (five adversarial review rounds), not formalized |
| n₃(y\*) ≥ 11 pointwise (§IV.2) | **Done** — machine-checked in Lean (`KellerTower.tower_eleven`: eleven distinct F³-preimages), independently exact in Python (`tower --exact3`, CI-run) |
| n₃ ≥ 11 propagates to a positive-measure set (§IV.2, "on an open neighborhood") | **Done** — machine-checked in Lean (`KellerOpen.tower_eleven_nhds`): the inverse Jacobian of F is exhibited explicitly (det DF ≡ −2), F³ maps neighborhoods to neighborhoods, and every y near y\* has eleven distinct F³-preimages |
| n(y) ≥ 1 off the empty-fiber curve (§II.3) | Main case (L ≠ 0 ∧ K ≠ 0) formalized as `KellerTower.fiber_nonempty`; the degenerate off-curve strata (L = 0 or K = 0) remain report-verified |
| max ess-range(n₂) = 9 (§IV.2) | Report-verified; the Lean certificates pin the attained values 3, 5, 7, 9 exactly |
| sympy exact arithmetic, mathlib oleans, the Lean kernel | Toolchain trust base |

Open mathematics (not a formalization gap): whether S_{F⁴} and S_{F³} are
inequivalent — both essential ranges contain values ≥ 11.

## Provenance

The source note is identified in the report header by SHA-256
(`kellermapoperators.md`, `fiber_and_escape.py`). Both files — plus the
note's other companion scripts and the earlier-draft artifacts its Appendix A
dissects — are archived unmodified in [`source-note/`](source-note/), with
digests verified against the report's pins (see that directory's README).
The report's revision note records the full adversarial-review history
(five external rounds).
