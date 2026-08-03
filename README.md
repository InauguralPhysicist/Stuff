# The Alpöge Keller Map as a Quantum System

Independent verification and new results for the note *"A Non-Regular
Heisenberg System from the Alpöge Keller Map"*, together with a
machine-checked Lean 4 layer for the Part IV level-set certificates.

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

## Repository contents

| File | What it is |
|---|---|
| `keller_quantization_report.md` | The report (revision 9) |
| `keller_quantization.py` | Companion code — eight subcommands reproduce every number in the report |
| `KellerCerts.lean` | Lean 4 certificates for the Part IV level sets (n₂ = 3, 5, 7, 9) |
| `AxiomCheck.lean` | `#print axioms` audit of every certificate |
| `friedrichs_levels.html` | Figure: Friedrichs spectrum of the transformed oscillator (Part III) |
| `source-note/` | The verified note and its companion scripts, archived with matching SHA-256 (see its README) |
| `lakefile.toml`, `lean-toolchain` | Lake build config, pinned to Lean 4 / mathlib v4.32.0 |

## Lean certificates

Requires [elan](https://github.com/leanprover/elan); the toolchain is pinned
by `lean-toolchain`.

```sh
lake update            # resolve mathlib (first run only; commit lake-manifest.json)
lake exe cache get     # download prebuilt mathlib oleans (highly recommended)
lake build KellerCerts # check the certificates
lake build AxiomCheck  # print the axioms each certificate depends on
```

The axiom check should report only the three standard axioms
(`propext`, `Classical.choice`, `Quot.sound`) — no `sorry`.

CI runs both builds on every push (see `.github/workflows/ci.yml`).

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

## Provenance

The source note is identified in the report header by SHA-256
(`kellermapoperators.md`, `fiber_and_escape.py`). Both files — plus the
note's other companion scripts and the earlier-draft artifacts its Appendix A
dissects — are archived unmodified in [`source-note/`](source-note/), with
digests verified against the report's pins (see that directory's README).
The report's revision note records the full adversarial-review history
(five external rounds).
