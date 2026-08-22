# m23-seven-points

Artifacts for: **The Galois action on the seven M23 Hurwitz points**
(A. W. Templeton).

The paper determines, for the seven Hurwitz points through which
Huang–Jackson–Lee–Poonen–Pries–Zhang (arXiv:2608.08538) realized M23
as a Galois group over Q: the action of complex conjugation
(unconditionally: (1 2)(5 7)), the numerically certified G_Q-partition
(1+6, image S6 — maximal given the fixed point), the exact 23-adic
structure (1+2+4 tame, label 6 the unique inertia-fixed point), and an
exact negative theorem (finite-level GT constraints at M23 permit all
of S7).

## Reproduce

From `pipeline/`, with the seven solver outputs in place
(`data/label{1..7}-out-p100.m`, symlink or copy them beside the
scripts):

    python3 reproduce_p100.py   # rerun until it prints DONE (phased)

produces `partition-p100-receipt.json`: marked Petri invariants for all
seven labels, trace/norm descent with label-6 exact anchors, the two
exact sextics with recognition margins, S6 Galois groups, the
199-prime Frobenius inventory with the split-prime parity argument,
the 23-adic factorization certificate, and an exact (symbolically
verified) field isomorphism between the two independent sextics.
Requires: python3, mpmath, sympy, python-flint.

`paper/gen_results_tex.py` regenerates every table in the PDF from the
receipts. The Magma referee scripts in `magma/` are single-paste files
for the public Magma calculator; `receipts/*ledger*.txt` record their
verbatim outputs.

The solver outputs themselves were produced by the job scripts in
`pipeline/job*.py` (emission + the standalone Arnoldi solver
`powser_arnoldi.c` of the Belyi package of Musty et al., MIT license).

`lean/` is the in-progress Lean 4 formalization of the finite
combinatorial core; it is not claimed as part of the paper's
verification.
