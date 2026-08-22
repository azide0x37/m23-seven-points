# The Galois action on the seven M23 Hurwitz points

**Paper (PDF): [paper/main.pdf](paper/main.pdf)** · LaTeX source:
[paper/main.tex](paper/main.tex)

Computational artifacts for *The Galois action on the seven M23
Hurwitz points* (Alexander West Templeton, 2026). This repository is
the artifact of record; releases are archived with a DOI.

## What the paper establishes

Huang, Jackson, Lee, Poonen, Pries, and Zhang (arXiv:2608.08538)
realized M23 as a Galois group over Q by finding a G_Q-fixed point
among the seven Hurwitz points of Ni(2A, 23A, 23B), noting they had no
conceptual explanation for the fixed point. This paper determines the
Galois action on the full seven-point fiber.

- **Exact.** Complex conjugation acts as (1 2)(5 7), fixing labels
  3, 4, 6 — proved by finite anchored certificates, three independent
  implementations, and a Magma referee run.
- **Exact.** The finite-level Grothendieck–Teichmüller group
  GT_1(M23) induces the full S7 on the seven classes: the symmetry
  breaking is not forced at this level.
- **High-precision numerical determination**, subject to the stated
  integer-relation recognitions: the G_Q-partition is 1 + 6 with
  maximal image — rho(G_Q) = Stab_S7(6) ≅ S6, and rho(G_K) = S6 by an
  exact argument conditional on the recognition. Two independently
  descended coordinates yield the same sextic field, by an exact
  symbolic certificate (paper Appendix; `receipts/iso-beta-receipt.json`).
- **Conditional on the same recognition, exact:** the 23-adic
  factorization of the displayed sextic gives the local decomposition
  Q_23 × F_2 × F_4 — tame inertia of cycle type (1)(2)(4), with label
  6 the unique inertia-fixed point at 23 (Magma-refereed).

## Reproduce (one command)

    git clone https://github.com/azide0x37/m23-seven-points
    cd m23-seven-points/pipeline
    python3 reproduce_p100.py      # phased; rerun until it prints DONE

Requirements: `python3` with `mpmath`, `sympy`, `python-flint`
(`pip install mpmath sympy python-flint`).

The pipeline starts from the seven stored 100-digit solver outputs
(`data/label{1..7}-out-p100.m`, found automatically) and reproduces
every computational assertion in the paper: marked Petri invariants
for all seven labels, trace/norm descent with exact label-6 anchors,
both exact sextics with recognition margins, the S6 Galois groups,
the 199-prime Frobenius inventory, the 23-adic factorization
certificate, and the exact field-identity certificate. Final receipt:
`partition-p100-receipt.json`.

`paper/gen_results_tex.py` regenerates every table in the PDF from
the receipts.

## Repository layout

| Path | Contents |
| --- | --- |
| `paper/` | LaTeX source, compiled PDF, table generator |
| `pipeline/` | reproduction pipeline and its libraries |
| `data/` | the seven 100-digit solver outputs (~12 MB each) |
| `receipts/` | machine-checkable JSON receipts and referee ledgers |
| `magma/` | exact Magma referee scripts (single-paste, free calculator) |
| `lean/` | in-progress Lean 4 formalization (see below) |

## Verification layers

Every computational claim in the paper names a receipt. The exact
combinatorial layer (census, conjugation certificates, generation) is
verified by three independent implementations, including the Magma
referee scripts in `magma/` whose verbatim outputs are recorded in
`receipts/*ledger*.txt`. The 100-digit solver outputs were produced
by the job scripts in `pipeline/job*.py` with the standalone Arnoldi
solver of the Belyi package (Musty–Schiavone–Sijsling–Voight, MIT;
see `THIRD_PARTY_NOTICES.md`).

`lean/` is an in-progress Lean 4 development that encodes and checks
the small finite certificates; the full census build and the glue
lemmas are incomplete, and no end-to-end formal verification is
claimed.

## AI assistance

This project made extensive use of AI systems, principally Claude
(Anthropic) and ChatGPT (OpenAI), throughout: exploratory
mathematical discussion, proposing and criticizing candidate
approaches, literature triage, generation and debugging of
computational code, orchestration and analysis of numerical
experiments, and drafting and editing the manuscript under the
author's direction. The author selected the research questions,
determined which claims to pursue, executed or supervised the
computations, evaluated the evidence, and takes responsibility for
all claims. AI-generated suggestions were not treated as
mathematical evidence — which is precisely why this repository
exists: every computational claim is backed by receipts, independent
referee runs, and a one-command reproduction. The disclosure is part
of the method.

## Licensing

- Code, data, and receipts in this repository: MIT
  (`LICENSE`, with upstream notices in `THIRD_PARTY_NOTICES.md`).
- The paper (`paper/`) is copyright the author; the copy here is the
  version of record for this release.
