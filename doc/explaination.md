# Higher-rank type inference on dependent type

\newcommand{\system}{$\lambda^{\mu}_\star$ }
\newcommand{\overbar}[1]{\mkern 1.5mu\overline{\mkern-1.5mu#1\mkern-1.5mu}\mkern 1.5mu}

Apply paper [Practical type inference for arbitrary-rank types](http://research.microsoft.com/en-us/um/people/simonpj/papers/higher-rank/putting.pdf) on dependent type system \system.

Introduce the syntax differences first, then comes the main differences of typing rules.

## 1 Syntax

Only list the differences:

- Star type $\star$.
- Pi type. $\Pi(x:\tau).\tau_2$ with dependency, compared to function type $\tau_1 \rightarrow \tau_2$
- Forall type. Forall have type annotation $\forall \overbar{x:\tau}. \rho$, compared to $\forall \overbar{a}. \rho$ in which $a$ can only have type $\star$.
- castup.
- castdown.

## 2 Typing Rules

The differences comes from several aspects. Here introduces the modifications based on function, namely typing rules which is to type the expressions, generalization and instantiation rules, and polymorphism relationship.

### 2.1 Typing

#### Star type

Star has type $\star$. Involving: AX.

Pi and Forall type have type $\star$. Involving: Implicit-Pi, Explicit-Pi, FunPoly.

#### Annotation

Annotation need to be checked to make sure it has type $\star$. Involving: LamAnn-Infer, LamAnn-Check, Ann.

#### Substitute dependency

Pi type have dependency on arguments. So substitution occurs in application. Involving: App.

Let will use substitution rule instead of changing context, which will make the rule simpler. Involving: Let.

#### Cast

CastUp in check mode will step on the provided type and check the expression with that type. CastUp cannot be infered because there are many expressions can be casted to a type. Involving: CastUp-Check.

CastDown will infer the expression type first, then try to step on the infer result, finally use the inst rule to get the result. Involving: CastDown.

### 2.2 Generalization and Instantiation


In original type system, when a forall is instantiated, the type variable definitely is $\star$. But it is not the case in dependent type. For example type $(\forall a:int. Vect\ a)$ can be instantiated to $(Vect\ b)$. But the $b$ is of type int instead of $\star$.

So we will associate the type of the type variable to the type variable. It can be regarded as the data type definition in Haskell

```haskell
data Expr = ... | TVar Name Expr
```

So actually the type variable $b$ in previous example will be $TVar\ b\ int$.

It influences two rules, which is generation and instantiation.

In instantiation, when instantiate a forall, the type of the type variable will be remembered, as shown in the precondition of Inst-Infer.

Then in generalization, the free type variables will be extracted with their types as the precondition in Gen-Infer shows. So the generated forall will have type annotations.

This part is involving: Gen-Infer, Gen-Check, Inst-Infer.

### 2.3 Polymorphism Relatioship

#### Pr

Unlike original system, where Pr-Mono is used to deal with variables, here types can be of other forms, and pr will just keep them the same. Involving: Pr-OtherCase.

#### Environment

This part explains the $\Sigma\vdash a:\tau$ with rules Exists, NotExists.

In original type system, when do instantiation in Deep-Skol or Spec, the type variable can be instantiated to any type. Because type variable is of type $\star$, and every type has type $\star$. But it is not the case here since type variable have their own types. So when you try to instantiate a forall, you need to make sure it has the right type. It also influences the argument of Pi type, for example two types $(\forall a:int. \Pi b:int.\ Vect\ a)$, and $(\Pi b:int. Vect\ b)$, the first type is more polymorphic than the second one since a can be instantiated to b. It can only do so because $\Sigma\vdash b:int$. If the second one is $\Pi b:char. Vect\ b$ then it will fail.

To make sure the instantiation is right, is what $\Sigma\vdash a:\tau$ do, namely rule Exists and NotExists.

It also influence the preconditions in dsk and dsk\* : DeepSkol, Spec, Fun, LamAnn.

#### Cases

dsk\* rule has more cases than original type system.

Fun rule is modified. While check the body type, the x will be added into envoriment with the more specific one.

App requires the argument to be identical. Then it checks the polymorphism relationship between the abstractions.

Lam continues to check the body without the argument added, while LamAnn will add the the argument but requires the annotations to be identical.

Ann requires the annotation to be identical and check the annotated expression.

CastUp and CastDown continues to check the expressions to be casted.

In Other Case, we requires the expressions to be $\alpha-$equal.
