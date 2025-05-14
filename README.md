# groebner

The goal of this project is formalization of Gröbner basis theory in the Lean 4 theorem prover, establishing the mathematical infrastructure required for computational algebra in Lean. Based on it, we aim to bridge the gap between Lean and some computational algebra problems, such as solving systems of multivariate polynomial equations, ideal membership problems, and so on.

This project is still work in process. There are some errors and out-of-date information on our documents and maybe even unproved statements. Any fix and suggestions will be welcomed.

[![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/WuProver/groebner_proj)

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/WuProver/groebner_proj)

## Introduction

### Definitions

- [`MonomialOrder.leadingTerm`](https://wuprover.github.io/groebner_proj/docs/find/#doc/MonomialOrder.leadingTerm): leading term
- [`MonomialOrder.sPolynomial`](https://wuprover.github.io/groebner_proj/docs/find/#doc/MonomialOrder.sPolynomial): S-polynomial
- [`MonomialOrder.IsRemainder`](https://wuprover.github.io/groebner_proj/docs/find/#doc/MonomialOrder.IsRemainder)
- [`MonomialOrder.IsGroebnerBasis`](https://wuprover.github.io/groebner_proj/docs/find/#doc/MonomialOrder.IsGroebnerBasis)

### Main Statements

Given a monomial order, a field $k$, and an index set $\sigma$, we will show the following properties about $k[x_i:i\in \sigma]$:

- [`MonomialOrder.exists_groebner_basis`](https://wuprover.github.io/groebner_proj/docs/find/#doc/MonomialOrder.exists_groebner_basis): if the $\sigma$ is finite, then each ideal $I \subseteq k[x_i: i\in \sigma]$ has its Gröbner basis.
- [`MonomialOrder.groebner_basis_isRemainder_zero_iff_mem_span`](https://wuprover.github.io/groebner_proj/docs/find/#doc/MonomialOrder.groebner_basis_isRemainder_zero_iff_mem_span) (WIP): given a Gröbner basis $G$ of an ideal $I\subseteq k[x_i: i\in \sigma]$, a polynomial $p\in k[x_i: i\in \sigma]$, and a remainder $r$ of $p$ on division by $G$, then $r = 0$ if and only if $p\in I$.
- [`MonomialOrder.is_groebner_basis_iff`](https://wuprover.github.io/groebner_proj/docs/find/#doc/MonomialOrder.is_groebner_basis_iff): given an ideal $I\subseteq k[x_i:i\in\sigma]$ and a finite set $G\subseteq k[x_i:i\in\sigma]$, then $G$ is a Gröbner basis of $I$ if and only if $G \subseteq I$ and $0$ is a remainder of each $p\in I$ on division by $G$.
- [`MonomialOrder.span_groebner_basis`](https://wuprover.github.io/groebner_proj/docs/find/#doc/MonomialOrder.span_groebner_basis): if $G$ is a Gröbner basis of $I\subseteq k[x_i:i\in\sigma]$, then $I=\langle G\rangle$.
- [`MonomialOrder.buchberger_criterion`](https://wuprover.github.io/groebner_proj/docs/find/#doc/MonomialOrder.buchberger_criterion) (WIP): a finite set $G\subseteq k[x_i:i\in\sigma]$ is Gröbner basis of $\langle G\rangle$, if and only if $0$ is the remainder of the S-polynomial of each two elements in $G$ on division by $G$.

## Project Resources

We maintain a set of web-based resources to track and explore the formalization effort:

- 📘 **[Project Homepage](https://wuprover.github.io/groebner_proj/)**

- 📐 **[Formalization Blueprint](https://wuprover.github.io/groebner_proj/blueprint/)**
  A detailed list of definitions, lemmas, and theorems, including their proof status and logical dependencies.

- 🔗 **[Dependency Graph](https://wuprover.github.io/groebner_proj/blueprint/dep_graph_document.html)**
  A visual representation of the dependency structure of the formalized components.

These tools help us manage development, track formalization progress, and guide future contributors.

## Build

To use this project, you'll need to have Lean 4 and its package manager `lake` installed. If you don’t already have Lean 4 set up, follow the [Lean 4 installation instructions](https://leanprover-community.github.io/get_started.html).

Once Lean is installed, you can clone this repository and build the project:

```bash
git https://github.com/WuProver/groebner_proj.git
cd groebner_proj
lake exe cache get
lake build
```

The blueprint can be generated as following:
```bash
pip install https://github.com/WuProver/plastexdepgraph/archive/refs/heads/settitle.zip leanblueprint

leanblueprint pdf
leanblueprint web
```

## Reference
This project draws heavily from the following reference:
[Ideals, Varieties, and Algorithms](https://link.springer.com/book/10.1007/978-3-319-16721-3)
