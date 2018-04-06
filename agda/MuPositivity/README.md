Exploring Cardinality in the Modal μ-Calculus 
==============================================

This is an exploration of the meaning of cardinality constraints in
the Modal μ-Calculus when applied to finite transition systems. It
implements an interpreter for Modal μ-formulae.

Monotonicity 
============

In order to show that fixed points are well defined, we need to know
that the functions associated with formulae of a given free variable
in the modal μ-calculus are monotonic. That is for a function `⟦φ⟧` on
the the power set of a set `U` the following hold:

~~~

X ⊆ Y → ⟦ φ ⟧(X) ⊆ ⟦ φ ⟧(Y)

~~~

With this fact we have well defined fixed points (least and greatest
respectively) such that:

~~~

⟦ μ X . φ ⟧ ≔ ⋂{ X ⊆ U | ⟦ φ ⟧(X) ⊆ X }

⟦ ν X . φ ⟧ ≔ ⋃{ X ⊆ U | X ⊆ ⟦ φ ⟧(X) }

~~~ 

In order to show montonicity, we also need antitonicity as negation
will induce an inversion of the principle such that:

~~~

(∀ X Y → Y ⊆ X → ⟦ φ ⟧(X) ⊆ ⟦ φ ⟧(Y))
 → 
(∀ X Y → X ⊆ Y → ⟦ ¬φ ⟧(X) ⊆ ⟦ ¬φ ⟧(Y))

~~~

In order to show montonicity and antitonicity we can impose a
restriction on the syntax of the formulae known as "positivity". The
positivity restriction states that free variables to be used in fixed
points must be in a "positive" position in the formula. This can be
defined inductively which we find convenient to do simultaneously with
the definition of negatively occuring formulae with a single inductive
relation called "Polarity".

The Polarity of a term gives a set of all variables (from 𝓥) which
occur in a positive context and all variables in a negative context
for a given term.

~~~

  data Polarity : Φ → 𝒫(𝓥) → 𝒫(𝓥) → Set where
    Var : ∀ {x} → Polarity (v x) [ x ] []
    Prop : ∀ {p} → Polarity (P p) [] []
    Alpha : ∀ {s a p n} → Polarity s p n → Polarity (α[ a ] s) p n
    And : ∀ {s₁ s₂ p₁ p₂ n₁ n₂} → Polarity s₁ p₁ n₁ → Polarity s₂ p₂ n₂ → Polarity (s₁ ⊗ s₂) (p₁ ∪ p₂) (n₁ ∪ n₂)
    Not : ∀ {s p n} → Polarity s p n → Polarity (- s) n p φ

~~~ 

Since it is possible to have variables in a mixed polarity (both
positive and negative), posivity for a free variable x can be defined
as a polarity in which the variable is not in a negative poliarity for
the formula. This also allows the variable to not be free in a
positive position since it is not necessary to refer to a variable,
only that it not occur negatively.

~~~

Positive x φ ≔ Polarity φ 𝓟 𝓝 ∧ x ∉ 𝓝

~~~

Given a positive formulae φ we can ensure monotonicity and thereby
fixed-points.

Cardinality 
===========

Cardinality is not present in the modal μ-Calculus but we require
cardinality in most "Shape" languages for the semantic-web such as
ShEx and SHACL. We can add cardinality to the Modal μ without too much
complication. However, we need to remember that the monotonicity
conditions must be respected in order to employ fixed points. 

Cardinality here is expressed strictly in terms of equality over
natural numbers for simplitiy, rather than a general numeric
predicate, though a general predicate is quite easy to add and
pressents no problems for any decidable arithmetic fragment.

We define cardinality using a right restriction, written in terms of
set comprehension (given in our various comprehension libraries). 

`R ⟨ a ⟩▹ A` is the right restriction of `R` to `A` at transition `a`. 

`σ₁ s R` is the selection of `s` in the first element of a triple from
the relation `R` (sometimes written by juxtaposition in mathematical
literature: `sR`).

`𝓒 s R` is the cardinality of the selection `s` at `R`.

~~~
_⟨_⟩▹_ : ∀ (R : Transitions) (a : C) (A : List C)  → Transitions
R ⟨ a ⟩▹ A = ⟪ τ ∈ R ∣ ⌊ eqC (prop τ) a ⌋ ∧ ⌊ (obj τ) WFC.∈? A ⌋ ⟫

σ₁ : ∀ s R → Transitions
σ₁ s R = ⟪ τ ∈ R ∣ ⌊ eqC (sub τ) s ⌋ ⟫

𝓒 : ∀ s R → ℕ
𝓒 s R = length (σ₁ s R)
~~~

Using this we can extend the modal-μ calculus with the following semantics: 

~~~
⟦ α⟨ a ⟩⁅ n ⁆ φ  ⟧+ i = ⟪ s ∈ 𝓢 ∣ ⌊ 𝓒 s (𝓣 ⟨ a ⟩▹ (⟦ φ ⟧+ i)) ≟ℕ n ⌋ ⟫
~~~

We can read this as, for every transition `a`, we return the set of
`s` at which the number of triples in the relation `𝓣` restricted to
`⟦ φ ⟧+ i`, is equal to `n`. This is the intuitive meaning of
cardinality as expressed in languages such as SHACL and ShEx.

As it turns out, we see in the file `CounterExample.agda`, the most
natural cardinality condition is neither monotone, nor antitone. This
means that in the polarity we have to add the variable to both
positive and negative contexts (as it is essentially of a
mixed-polarity). Utilising this restriction we can cleanly express the
monotonicity of our calculus as is shown in the file `Monotonic.agda`.

The counter example is very simple and utilises the following
transition system:

~~~
𝓣 : Transitions
𝓣 = (A , B , C) ∷ (A , B , D) ∷ (E , B , F) ∷ []
~~~

Given this system and the sets `X₁`, `Y₁`, `X₂` and `Y₂` as follows: 

~~~
X₁ : Subjects
X₁ = C ∷ ∅

Y₁ : Subjects
Y₁ = C ∷ D ∷ ∅

X₂ : Subjects
X₂ = C ∷ ∅

Y₂ : Subjects
Y₂ = C ∷ F ∷ ∅
~~~

We have that the formula `φ` with one free variable a and a
cardinality of 1 off of the transition B defined as:

~~~
φ⟨_⟩ : (a : ℕ) → Φ+
φ⟨ a ⟩ = α⟨ B ⟩⁅ 1 ⁆ (v a)
~~~

A `B` tranition with cardinality 1.

...is neither monotone nor antitone, i.e.

~~~
φNotMonotone : ∀ (a : ℕ) → 
 ----------------------------------------------------------
  ¬ (⟦ φ⟨ a ⟩ ⟧+ (i [ a ≔ X₁ ]) ⊆ ⟦ φ⟨ a ⟩ ⟧+ (i [ a ≔ Y₁ ]))

φNotAntitone : ∀ (a : ℕ) →
  ¬ (⟦ φ⟨ a ⟩ ⟧+ (i [ a ≔ Y₂ ]) ⊆ ⟦ φ⟨ a ⟩ ⟧+ (i [ a ≔ X₂ ]))
~~~



