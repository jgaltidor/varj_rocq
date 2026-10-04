# varj_rocq

A mechanization of **VarJ** in the [Rocq Prover](https://rocq-prover.org/) (formerly Coq).

VarJ is a core calculus for Java-like generics that combines **definition-site variance** (variance annotations on class type parameters, as in Scala or C#) with **use-site variance** (Java wildcards, modeled as existential types). It was introduced in:

> John Altidor, Shan Shan Huang, and Yannis Smaragdakis. *Taming the Wildcards: Combining Definition- and Use-Site Variance.* PLDI 2011.

VarJ builds on TameFJ (Cameron, Drossopoulou, and Ernst, *A Model for Java with Wildcards*, ECOOP 2008). Binders are encoded with the **locally nameless** representation (Aydemir et al., *Engineering Formal Metatheory*, POPL 2008).

## Status

This is an incomplete, exploratory development. It defines the full language: syntax, opening and substitution, variance, subtyping, well-formedness, typing, and reduction. It also proves a few metatheory lemmas. It does not prove type soundness, and two weakening lemmas are left `Admitted`. `archive/notes.txt` records the design issues that remained open when work stopped.

## Building

You need Rocq 9.2 or later. The easiest way to get it is the included devcontainer (`.devcontainer/`), which uses the official `rocq/rocq-prover:9.2` image. Without a devcontainer, Docker alone works:

```sh
docker run --rm --platform linux/amd64 -v "$PWD":/w -w /w rocq/rocq-prover:9.2 make
```

With Rocq installed locally:

```sh
make                 # build everything
make VarJ_Typing.vo  # build one file and its dependencies
make clean
```

The build is driven by `_CoqProject`, which maps the repository root to the logical path `VarJ`.

## Layout

| File | Contents |
| --- | --- |
| `VarJ_Env.v` | Atoms (natural numbers), freshness, and ordered association-list environments |
| `VarJ_Syntax.v` | Types, expressions, class tables, and contexts |
| `VarJ_OpenClose.v`, `VarJ_Substitution.v` | Locally nameless opening, local closure, and substitution |
| `VarJ_Variance.v` | The variance lattice and the variance-of-a-type judgment |
| `VarJ_Lookup.v` | Field and method lookup |
| `VarJ_Subtyping.v` | Subtyping |
| `VarJ_Wellform.v` | Well-formed types and contexts |
| `VarJ_Typing.v` | Expression, method, and class typing |
| `VarJ_Reduction.v` | Small-step reduction |
| `VarJ_Lemmas.v` | Metatheory lemmas (weakening, inversion) |
| `archive/` | Design notes and earlier snapshots; not part of the build |

## History

The encoding was written for Coq 8.4 between 2013 and 2015, and was ported to Rocq 9.2 in 2026. The last Coq 8.4 version is commit `6f11afb`.

## Credits

The VarJ encoding is by John Altidor. Earlier versions used `Atom.v` (Arthur Charguéraud and Brian Aydemir) and `Metatheory.v` (Bruno De Fraine's Cast-Free Featherweight Java development) for names and environments. These were replaced by `VarJ_Env.v` in 2026.

## License

Released under the MIT License; see [LICENSE](LICENSE). The `archive/` folder holds earlier snapshots that include third-party files under their original authors' terms.
