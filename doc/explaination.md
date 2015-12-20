# Higher-rank type inference on dependent type

\newcommand{\system}{$\lambda^{\mu}_\star$ }
\newcommand{\overbar}[1]{\mkern 1.5mu\overline{\mkern-1.5mu#1\mkern-1.5mu}\mkern 1.5mu}

Apply paper [Practical type inference for arbitrary-rank types](http://research.microsoft.com/en-us/um/people/simonpj/papers/higher-rank/putting.pdf) on dependent type system \system.

Introduce the syntax differences first, then comes the main differences of typing rules. According to the function, the explaination of typing rules will be split into three parts, namely typing rules which is to type the expressions, generalization and instantiation rules, and polymorphism relationship.

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

#### Cast

CastUp in check mode will step on the provided type and check the expression with that type. CastUp cannot be infered because there are many expressions can be casted to a type. Involving: CastUp-Check.

CastDown will infer the expression type first, then try to step on the infer result, finally use the inst rule to get the result. Involving: CastDown.

### 2.2 Generalization and Instantiate


In original type systems, when a forall is instantiated, the type variable definitely is $\star$. But it is not the case in dependent type. For example type $\forall a:int. Vect\ a$ can be instantiated to $Vect\ b$. But the $b$ is of type int instead of $\star$.

So we will associate the type of the type variable to the type variable. It can be regarded as the data type definition in Haskell

```haskell
data Expr = ... | TVar Name Expr
```

So actually the type variable $b$ in previous example will be $TVar\ b\ int$.

It influences two rules, which is generation and instantiation.

In instantiation, when instantiate a forall, the type of the type variable will be remembered, as shown in the precondition.

Then in generalization, the free type variables will be extracted with their types as the precondition shows. So the generated forall will have type annotations.

This part is involving: Gen-Infer, Gen-Check, Inst-Infer.

### 2.3 Polymorphism Relatioship

#### Pr

Unlike original system, where Pr-Mono is used to deal with variables, here types can be of other forms, and pr will just keep them the same. Involving: Pr-OtherCase.

#### Envoriment



#### Cases


