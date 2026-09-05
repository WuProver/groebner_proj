# Groebner

The goal of this project is formalization of Gröbner basis theory in the Lean 4 theorem prover, establishing the mathematical infrastructure required for computational algebra in Lean. Based on it, we aim to bridge the gap between Lean and some computational algebra problems, such as solving systems of multivariate polynomial equations, ideal membership problems, and so on.

This project is still work in process. There are some errors and out-of-date information on our documents and maybe even unproved statements. Any fix and suggestions will be welcomed.

[![Open in GitHub Codespaces](https://github.com/codespaces/badge.svg)](https://codespaces.new/WuProver/groebner_proj)

[![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/WuProver/groebner_proj)

## Introduction

### Files

- [`Groebner/MonomialOrderEmbedding.lean`](/Groebner/MonomialOrderEmbedding.lean): embedding between monomial orders;
- [`Groebner/MonomialOrder.lean`](./Groebner/MonomialOrder.lean): lemmas about monomial order and `withBotDegree`;
- [`Groebner/Remainder.lean`](./Groebner/Remainder.lean): remainder;
- [`Groebner/Groebner.lean`](./Groebner/Groebner.lean): Groebner basis;
- [`Groebner/Reduced.lean`](./Groebner/Reduced.lean): reduced Gröbner basis;
- [`archive`](./archive/): archived version of the source code before updating to a new version of mathlib with some of our formalization merged.

### Definitions

- [`MonomialOrder.leadingTerm`](https://wuprover.github.io/groebner_proj/docs/find/#doc/MonomialOrder.leadingTerm): leading term
- [`MonomialOrder.sPolynomial`](https://wuprover.github.io/groebner_proj/docs/find/#doc/MonomialOrder.sPolynomial): S-polynomial
- [`MonomialOrder.IsRemainder`](https://wuprover.github.io/groebner_proj/docs/find/#doc/MonomialOrder.IsRemainder): remainder
- [`MonomialOrder.IsGroebnerBasis`](https://wuprover.github.io/groebner_proj/docs/find/#doc/MonomialOrder.IsGroebnerBasis): Gröbner basis
- [`MonomialOrder.IsGroebnerBasis.IsMinimal`](https://wuprover.github.io/groebner_proj/docs/find/#doc/MonomialOrder.IsGroebnerBasis.IsMinimal): minimal Gröbner basis
- [`MonomialOrder.IsGroebnerBasis.IsReduced`](https://wuprover.github.io/groebner_proj/docs/find/#doc/MonomialOrder.IsGroebnerBasis.IsReduced): reduced Gröbner basis

### Main Statements

Given a monomial order, a field $k$, and an index set $\sigma$, we will show the following properties about $k[x_i:i\in \sigma]$:

- [`MonomialOrder.IsGroebnerBasis.exists_isGroebnerBasis`](https://wuprover.github.io/groebner_proj/docs/find/#doc/MonomialOrder.IsGroebnerBasis.exists_isGroebnerBasis): if the $\sigma$ is finite, then each ideal $I \subseteq k[x_i: i\in \sigma]$ has its Gröbner basis.
- [`MonomialOrder.IsGroebnerBasis.remainder_eq_zero_iff_mem_ideal`](https://wuprover.github.io/groebner_proj/docs/find/#doc/MonomialOrder.IsGroebnerBasis.remainder_eq_zero_iff_mem_ideal): given a Gröbner basis $G$ of an ideal $I\subseteq k[x_i: i\in \sigma]$, a polynomial $p\in k[x_i: i\in \sigma]$, and a remainder $r$ of $p$ on division by $G$, then $r = 0$ if and only if $p\in I$.
- [`MonomialOrder.IsGroebnerBasis.isGroebnerBasis_iff_subset_ideal_and_isRemainder_zero`](https://wuprover.github.io/groebner_proj/docs/find/#doc/MonomialOrder.IsGroebnerBasis.isGroebnerBasis_iff_subset_ideal_and_isRemainder_zero): given an ideal $I\subseteq k[x_i:i\in\sigma]$ and a set $G\subseteq k[x_i:i\in\sigma]$, then $G$ is a Gröbner basis of $I$ if and only if $G \subseteq I$ and $0$ is a remainder of each $p\in I$ on division by $G$.
- [`MonomialOrder.IsGroebnerBasis.existsUnique_isRemainder`](https://wuprover.github.io/groebner_proj/docs/find/#doc/MonomialOrder.IsGroebnerBasis.existsUnique_isRemainder): remainder of any polynomial on division by Gröbner basis is unique.
- [`MonomialOrder.IsGroebnerBasis.ideal_eq_span`](https://wuprover.github.io/groebner_proj/docs/find/#doc/MonomialOrder.IsGroebnerBasis.ideal_eq_span): if $G$ is a Gröbner basis of $I\subseteq k[x_i:i\in\sigma]$, then $I=\langle G\rangle$.
- [`MonomialOrder.IsGroebnerBasis.isGroebnerBasis_iff_isRemainder_sPolynomial_zero`](https://wuprover.github.io/groebner_proj/docs/find/#doc/MonomialOrder.IsGroebnerBasis.isGroebnerBasis_iff_isRemainder_sPolynomial_zero): (Buchberger's criterion) a set $G\subseteq k[x_i:i\in\sigma]$ is Gröbner basis of $\langle G\rangle$, if and only if $0$ is the remainder of the S-polynomial of each two elements in $G$ on division by $G$.
- [`MonomialOrder.IsGroebnerBasis.IsReduced.uniqueExists_of_isGroebnerBasis`](https://wuprover.github.io/groebner_proj/docs/find/#doc/MonomialOrder.IsGroebnerBasis.IsReduced.uniqueExists_of_isGroebnerBasis): unique existence of reduced Groebner basis.

## Project Resources

We maintain a set of web-based resources to track and explore the formalization effort:

- 📘 **[Project Homepage](https://wuprover.github.io/groebner_proj/)**

- 📐 **[Formalization Dependency Graph](https://wuprover.github.io/groebner_proj/blueprint/dep_graph_document.html)**
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

The dependency graph can be generated as following:
```bash
pip install https://github.com/WuProver/plastexdepgraph/archive/refs/heads/settitle.zip leanblueprint
./generate-content.sh
leanblueprint pdf
leanblueprint web
```

## Reference

This project draws heavily from [_Ideals, Varieties, and Algorithms_](https://link.springer.com/book/10.1007/978-3-319-16721-3) by David A. Cox, John Little, Donal O’Shea.

And some theorems are from [_Gröbner Bases for the Polynomial Ring with Infinite Variables and Their Applications_](https://doi.org/10.1080/00927870802502878) by Kei-ichiro Iima and Yuji Yoshino.

The division for weak reduction in `Groebner/WeakRemainder.lean` is from [_On the construction of Gröbner bases using syzygies_](https://www.sciencedirect.com/science/article/pii/S074771718880052X)
