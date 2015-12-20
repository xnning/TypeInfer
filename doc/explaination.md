# Higher-rank type inference on dependent type

\newcommand{\system}{$\lambda^{\mu}_\star$ }
\newcommand{\overbar}[1]{\mkern 1.5mu\overline{\mkern-1.5mu#1\mkern-1.5mu}\mkern 1.5mu}

Apply paper [Practical type inference for arbitrary-rank types](http://research.microsoft.com/en-us/um/people/simonpj/papers/higher-rank/putting.pdf) on dependent type system \system.

Introduce the syntax differences first, then comes the main differences of typing rules.

## 1 Syntax

- Star type $\star$.
- Pi type. $\Pi(x:\tau).\tau_2$ with dependency, compared to function type $\tau_1 \rightarrow \tau_2$
- Forall type. Forall have type annotation $\forall \overbar{x:\tau}. \rho$, compared to $\forall \overbar{a}. \rho$ in which $a$ can only have type $\star$.
- castup.
- castdown.

## 2 Typing Rules

The differences comes from several aspects. Here introduces the modifications based on aspects.

### 2.1 Typing

#### Star type

Star has type $\star$. Involving: AX.

Pi and Forall type have type $\star$. Involving: Implicit-Pi, Explicit-Pi, FunPoly.

#### Annotation

Annotation need to be checked to make sure it has type $\star$. Involving: LamAnn-Infer, LamAnn-Check, Ann

#### Substitute dependency

Pi type have dependency on arguments. So substitution occurs in application. Involving: App.

Let will use substitution rule instead of changing context, which will make the rule simpler. Involving: Let.

### 2.2 Generation and Instantiate

