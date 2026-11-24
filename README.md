# Three-generation chiral SU(5)

The main theorem is `ChiralSU5.exists_interacting_three_generation_theory_with_exact_running`.
It concerns four-dimensional SU(5) gauge theory with three generations of
left-handed fermions in the 10 and the antifundamental representation, 5̄.

The theorem constructs a continuum vacuum and fields from a common lattice
history. For the gauge-invariant observables in the statement, the Euclidean
correlations satisfy reflection positivity on the specified positive-time
tests. The relativistic theory has a positive Hilbert space, a cyclic vacuum,
and unitary time evolution.

Two conclusions identify interactions on this construction.

- In the reconstructed vacuum the real part of the connected correlation
  between a matter current from a single generation and a gauge-field clover observable is
  nonzero for the specified smearings. Both test functions have compact
  support, and the supports are spacelike separated. The gauge observable
  has zero vacuum expectation for this test.
- On the lattice history that gives this vacuum, the average ultraviolet
  slope of the fitted inverse squared gauge coupling converges to 43/3.
  With the normalization used in the theorem, the stationary gauge
  contribution converges to 55/3 and the screening contribution to 4.
  These limits hold to any prescribed positive tolerance on sufficiently
  deep and sufficiently long ultraviolet windows, uniformly over the volume
  rows and cutoffs in which the window fits.

For the physics statement, including the precise meaning of the ultraviolet
limit, see [the claim](CLAIM.md). `SU5ExactJointTarget.lean` gives the full
formal proposition.
`SU5RelativisticTarget.lean` states the reconstruction conditions and
`SU5ExactRunningTarget.lean` defines the three limits.
`SU5ExactJointChallenge.lean` states the reference theorem.
`SU5ExactJointSolution.lean` supplies its proof. The two entry modules are
built separately so the submitted proof must establish the independently
stated reference theorem. The source lists for each entry point appear in
`reference-files.txt` and `solution-files.txt`.

## Verification record

The native Comparator accepted the theorem with both stock kernels. Its
unedited output is in [the comparison log](verification/comparison.log).
Lake and both kernels ran inside one outer bubblewrap sandbox with isolated
namespaces and read-only proof inputs. The run repeated the positive,
negative and containment controls. Lake's warning about its disabled inner sandbox refers to this outer-sandbox configuration. The public replay below uses Lake's built-in sandbox for each checker.
The native run reused authenticated compiled modules and compiled the
additional sources before exporting the reference and solution. The accepted
export hashes and the three controls are in [the verification record](verification/acceptance.json).

## Verify the archive and replay the proof

Compare the archive's SHA-256 digest with the one supplied by the sender.
After extracting the archive, check the other files against `SHA256SUMS`.
From the extracted project directory, run

```sh
sha256sum --check --strict SHA256SUMS
./tools/setup-linux /absolute/path/to/new-tools
./tools/verify /absolute/path/to/new-tools /absolute/path/to/new-run
```

To check the sources and stage the two entry points before building them,
run `./tools/verify --stage-only /absolute/path/to/new-staging-directory`.

Use fresh directories on a high-memory native Linux machine. The setup needs
Python 3.9 or later, Git, curl, zstd, GNU tar and coreutils, make, a C compiler
and bubblewrap with user namespaces enabled. The initial setup downloads the
pinned public toolchains and libraries. Leave room for the build products and
both proof exports. The nine library revisions are in `lake-manifest.json`.

The sources build with Lean 4.32.0. The replay exports the reference and the
solution, then runs the official Lake Comparator from Lean 4.35.0. Its two
kernels are Lean's default kernel and con-ron in verified mode. The permitted
axioms are `propext`, `Classical.choice` and `Quot.sound`. A successful replay
exits with status zero. The final `comparator.log` in the run directory records
both kernel acceptances and ends with `Your solution is okay!`.

Third-party code is identified in `notices/`, alongside its source credits
and applicable licenses.
