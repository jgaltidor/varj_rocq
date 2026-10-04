# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

A Rocq (formerly Coq) encoding of **VarJ**, a Featherweight-Java-style calculus with definition-site variance annotations, use-site variance via existential types, and wildcard capture. Binders use the **locally nameless** representation (Aydemir et al., *Engineering Formal Metatheory*, 2008). The encoding is incomplete. Per the author's design notes (`git show dd6e750:archive/notes.txt`), work stopped once the encoding approach was validated, and parts would need refactoring before soundness proofs could be finished.

## Building

The code targets **Rocq 9.2**. It was ported from Coq 8.4, and the last Coq 8.4 version is commit `6f11afb`. Rocq is not installed on the host. Build inside the devcontainer (`.devcontainer/`, image `rocq/rocq-prover:9.2`, amd64-only so it runs emulated on Apple Silicon), or run a one-off build with:

    docker run --rm --platform linux/amd64 -v "$PWD":/w -w /w rocq/rocq-prover:9.2 make

`_CoqProject` lists the files in dependency order and maps the repo root to the logical path `VarJ`. `Makefile` is a thin wrapper that generates `Makefile.rocq` with `rocq makefile`.

- Build everything: `make`
- Check a single file and its dependencies: `make VarJ_Typing.vo`
- Clean: `make clean`

There are no tests. "Passing" means every `.v` file compiles. The unfinished proofs `weakening_subtyping` and `context_movement` in `VarJ_Lemmas.v` end in `Admitted`. Use `Print Assumptions <lemma>.` to see what a result depends on. The remaining build warnings (`register-all`, `notation-incompatible-prefix`, `closed-notation-not-level-0`) are expected and harmless.

### Rocq conventions used here

- Imports are qualified: `From VarJ Require Import VarJ_Syntax.` and `From Stdlib Require Import List.`
- Hints declared outside a section use `#[global] Hint ... : core.`, which keeps the Coq 8.4 behaviour where hints were visible to every file that imports the module.
- Type abbreviations in `VarJ_Syntax.v` use `Abbreviation`, not `Notation`. This keyword needs Rocq 9.2 or later.

## Architecture

All modules are flat in the repo root. The dependency chain, bottom to top:

1. **`VarJ_Env.v`**: names and environments, built only on the standard library. Atoms are `nat` (`==` is `Nat.eq_dec`, freshness via `list_max`). Environments are ordered association lists with `get` (first match), `binds`, `no_binds`, `dom` (`map fst`), and the `\in`/`\notin` notations. Keep environments as lists: rules depend on order, for example `combine (dom fds) es` in reduction, and opening binders with `dom tcxt`.
2. **`VarJ_Syntax.v`**: all syntax. It re-exports `VarJ_Env`, `List`, and `Arith`, so every other VarJ module just `Require Import VarJ_Syntax`. Key points:
   - Types are a mutual inductive: `typ` (existential `t_ext`, bound var `t_bvar level index`, free var `t_fvar`), `typ_n` (class type `n_typ C ts`), and `typ_b` (lower bound or `b_bot`). Bound variables are **two-indexed**: binder depth, then position within that binder's parameter list, because binders introduce lists of variables.
   - `typ_p` adds `p_inf` (inferred type argument). `typ_r` is an "opened" type body.
   - Class tables, method/field defs, and contexts (`cxt_t` for type variables with bounds, `cxt_e` for expression variables) are `Abbreviation`s over tuples and lists, not inductives.
   - Global assumptions (`Parameter`): `this`, `Object`, the class table `CT`, and, in `VarJ_Typing.v`, `classTableOK : CT_isOK CT`.
3. **Binder operations**: `VarJ_OpenClose.v` (`open_*` for each syntactic category, `*_with_names`, `fresh_list`, local closure `lc_t`, `bodies_*`) and `VarJ_Substitution.v` (`subst_*`, simultaneous substitution of name lists).
4. **`VarJ_Variance.v`**: the variance lattice (`covar`, `contravar`, `invar`, `bivar` with `+`/`-`/`*` notations in `variance_scope`), the transform/meet/join operators as both `*_op` functions and relational `Prop` wrappers, and the variance-of-a-type judgment `var_t`/`var_p`.
5. **Judgments**: `VarJ_Lookup.v` (`fields`, `ftype`, `mtype`, `mbody`), `VarJ_Subtyping.v` (`subtype_n`/`subtype_t`/`subtype_b`), `VarJ_Wellform.v` (`ok_t`, `ubound_t`, `ok_cxt_e`), `VarJ_Typing.v` (expression `typing`, which also outputs a context of opened existential variables, plus `method_typing`, `class_typing`, and `CT_isOK`), and `VarJ_Reduction.v` (`step`).
6. **`VarJ_Lemmas.v`**: metatheory lemmas (weakening, inversion). This file is the least complete.

### Conventions

- **`wide_*` judgments** lift a judgment pointwise over lists, for example `wide_ftype`, `wide_typing`, and `wide_var_lt`. The author chose these deliberately over `In`-based premises (see the design notes), so follow the same pattern when adding list-level rules.
- Every inductive judgment is followed by a `Hint Constructors`, and some get `Hint Extern` entries so `auto`/`eauto` can search them. Watch for cyclic hints: a past commit had to remove a lemma from the hint database because `eauto` looped.
- `Close Scope nat_scope` in `VarJ_Syntax.v` makes `*` mean the product type, not multiplication.

## History

- `master` is the only branch. The early history was imported from SVN. An abandoned experiment with length-indexed vectors instead of lists was deleted: a single judgment form over lists of different lengths fits the encoding better.
- Commit `dd6e750` is the last one with `archive/`, which held design notes and pre-repo snapshots of the encoding.
