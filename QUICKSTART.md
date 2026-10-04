# Quick start

This guide gets you from a fresh clone to stepping through proofs and adding your own lemmas. For background on VarJ, see the [README](README.md).

## 1. Get Rocq

Pick one of these options.

**VS Code devcontainer (recommended).** Install Docker and the VS Code *Dev Containers* extension. Open the repository folder and run **Dev Containers: Reopen in Container**. The first build takes a few minutes, longer on Apple Silicon, where the amd64 image runs under emulation. You get Rocq 9.2 and the VsRocq extension with its language server.

**Docker only.** No setup beyond Docker:

```sh
docker run --rm -v "$PWD":/w -w /w rocq/rocq-prover:9.2 make check
```

On Apple Silicon, add `--platform linux/amd64`.

**Local install.** Install Rocq 9.2 or later, for example with `opam install rocq-prover` or `brew install rocq`. For editor support, also install the `vsrocq-language-server` opam package and the VsRocq extension.

## 2. Build and check

```sh
make          # compile every file
make check    # compile, then verify which assumptions the lemmas rely on
```

A successful `make check` ends with a line like:

```
Checked 11 lemmas; assumptions used: CT Object context_movement weakening_subtyping
```

`CT` and `Object` are global parameters of the calculus (the class table and the root class). `weakening_subtyping` and `context_movement` are the two lemmas that are still unproven.

## 3. Step through a proof

Open `VarJ_Lemmas.v` in VS Code and move the cursor into the proof of `inversion_field`. VsRocq shows the goals and hypotheses at that point (use **Rocq: Step Forward** and **Step Backward**, or **Interpret to Point**). The proof goes by induction on the typing derivation: the field-access rule is the base case, and the subsumption rule is the inductive case.

To see what a result depends on, add this after it and step over it:

```coq
Print Assumptions inversion_field.
```

## 4. Find your way around

Read the files in dependency order. Each one builds on the ones before it:

1. `VarJ_Env.v`: names (atoms) and environments as ordered association lists.
2. `VarJ_Syntax.v`: types, expressions, and class tables. Start with the `typ` and `exp` inductives.
3. `VarJ_OpenClose.v`, `VarJ_Substitution.v`: locally nameless binders. A bound type variable `t_bvar i j` is the j-th parameter of the i-th enclosing binder.
4. `VarJ_Variance.v`: the variance lattice and the variance of a type position.
5. `VarJ_Lookup.v`, `VarJ_Subtyping.v`, `VarJ_Wellform.v`: auxiliary judgments.
6. `VarJ_Typing.v`, `VarJ_Reduction.v`: the type system and operational semantics.
7. `VarJ_Lemmas.v`: metatheory.

## 5. Add a lemma

1. Add it to the appropriate file (metatheory goes in `VarJ_Lemmas.v`), and import modules with `From VarJ Require Import ...`.
2. Run `make check`. If the lemma depends on something unproven, the check fails and names it.
3. If you finish proving `weakening_subtyping` or `context_movement`, remove it from `ALLOWED` in `scripts/check_assumptions.sh`, so the check keeps it proven.

Conventions to follow:

- Judgments over lists are written as separate `wide_*` judgments (for example `wide_typing`), not with `In`-based premises.
- Follow each new judgment with `#[global] Hint Constructors <name> : core.` Be careful with hints that can apply themselves forever: `eauto` loops on them.
- The variance orderings are written `(v1 < v2)%var` and `(v1 <= v2)%var`.

## 6. Before you push

CI runs `make check` on Rocq 9.2 for every push to `main` and every pull request. The build should produce no warnings, so treat any new warning as something to fix.
