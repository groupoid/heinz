# HFTT: Hopf Fibrations Type Theory

A Minimal Framework for Homotopy Groups of Spheres.

We introduce Hopf Fibrations Type Theory (HFTT), a novel type system designed
to efficiently represent and compute homotopy groups of spheres, addressing
the computational challenges of Cubical Homotopy Type Theory (CCHM). Built
on a minimal set of primitives—Hopf fibrations (ℝ, ℂ, ℍ, 𝕆), suspension,
and n-truncation — HFTT leverages fibrations to encode
topological structure directly. Alongside standard types (Π, Σ, Id),
HFTT includes natural numbers (ℕ) and an extended order type (ℕ∞) to
access group properties. Key innovations include eliminators for
suspensions and truncations, enabling streamlined reductions, and
a derivable order function that extracts the order of elements in πₙ(Sᵐ),
supporting both finite (e.g., π₄(S³) ≅ ℤ/2ℤ) and infinite (e.g.,
π₃(S²) ≅ ℤ) groups. Computational rules ensure efficient
normalization, while the fibrations provide a basis for
homotopy groups, potentially simplifying proofs of properties
like π₄(S³). This article outlines HFTT’s syntax, rules, and its
promise as a compact, expressive framework for homotopy type theory.

```
> π₃(S²) = ℤ
```

## Syntax

* Universe: Uⁿ.
* Types: Fib, Susp(A), Truncⁿ(A), ℕ, ℕ∞, Π(x:A).B, Σ(x:A).B, Id_A(u, v).
* Derivables: Sⁿ, πₙ(Sᵐ), order function.
* Terms: t, u, v ::= x, 𝟎, suc(t), fin(t), inf, hopfⁿ, susp(t), truncⁿ(t), λx.t, t u, (t, u), fst(t), snd(t), p, refl.
* Contexts: Γ ::= ∅ `|` Γ, x:A.

# JMTT: Jack Morava Type Theory

Encompasses unstable homotopy, stable homotopy (e.g., π₀^S(S⁰) = ℤ),
and chromatic phenomena (e.g., H^*(RP^2), spectral sequences),
inspired by Morava’s chromatic vision.

To enable cohomology computations in Hopf Fibrations Type Theory (HFTT) using
spectra like Hℤ or Hℚ, we need to refine and extend the spectrum-related rules.
Cohomology in chromatic homotopy theory often involves spectra (e.g., Eilenberg-MacLane
spectra Hℤ) and their stable homotopy groups, which represent cohomology groups when
applied to other spectra or spaces. Our current HTT setup has spectra, stable homotopy
groups (πₙ^S), and K(G, n) spaces trough n-Truncations and Groups, but lacks explicit
rules for cohomology operations—pairings, cochain complexes, or spectrum maps—that
make computations practical. Jack Morava Type Theory adds these rules, focusing on cohomology
as H^n(X; G) = [X, K(G, n)] or, in the stable setting, π₋ₙ^S(HG ∧ X).

```
> H^*(RP^2; ℤ/2ℤ) = ℤ/2ℤ[α]/(α³)
```

## Syntax

* Universe: Uⁿ.
* Types: Fibⁿ, Susp(A), Truncⁿ(A), ℕ, ℕ∞, Π(x:A).B, Σ(x:A).B, Id_A(u, v), Spec, πₙ^S(A), S⁰[p], Group, A ∧ B, [A, B], Hⁿ(X; G), G ⊗ H, SS(E, r).
* Derivables: Sⁿ, πₙ(Sᵐ), K(G, n), Cohomology Rings, Chromatic Towers.
* Terms: t, u, v ::= x, 𝟎, suc(t), fin(t), inf, hopfⁿ, susp(t), truncⁿ(t), λx.t, t u, (t, u), fst(t), snd(t), p, refl, spec({Aₙ},{σₙ}), stable(t), loc_p(t), grp(G, e, op, inv), smash(t, u), map(t), tensor(g, h), t : SS(E, r)^{p,q}.
* Contexts: Γ ::= ∅ `|` Γ, x:A.
  
# Inference Rules

## Formations

```
Γ ⊢ Sⁿ : U := ℕ-iter U 𝟐 Susp
Γ ⊢ Fibⁿ : U (n ∈ {1, 2, 4, 8})
Γ ⊢ Susp(A) : U
Γ ⊢ Truncⁿ(A) : U
Γ ⊢ ℕ : U
Γ ⊢ ℕ∞ : U
Γ ⊢ Π(x:A).B : U
Γ ⊢ Σ(x:A).B : U
Γ ⊢ Id_A(u, v) : U

Γ ⊢ Spec : U
Γ ⊢ πₙ^S(A) : U
Γ ⊢ A ∧ B : Spec
Γ ⊢ [A, B] : Spec
Γ ⊢ Hⁿ(X; G) : U
Γ ⊢ G ⊗ H : Group
Γ ⊢ SS(E, r) : U
Γ ⊢ Group : U
Γ ⊢ S⁰[p] : Spec
```

## Introductions

```
ℕ: 𝟎 : ℕ, suc : ℕ → ℕ
ℕ∞: fin : ℕ → ℕ∞, inf : ℕ∞
Fibⁿ: hopfⁿ : Fibⁿ
Susp: susp(t) : Susp(A) if t : A
Truncⁿ: truncⁿ(t) : Truncⁿ(A) if t : A
Π: λx.t : Π(x:A).B if Γ, x:A ⊢ t : B
Σ: (t, u) : Σ(x:A).B if t : A, u : B[t/x]
Id: refl : Id_A(u, u)

Spec: spec({Aₙ},{σₙ}) : Spec)
πₙ^S(A): stable(t) : πₙ^S(A)
S⁰[p]: loc_p(t) : S⁰[p]
Group: grp(G, e, op, inv)
∧: smash(t, u)
SS: t(E,r,p,q)
[,]: map(t)
⊗: tensor(g, h) : G ⊗ H
```

## Eliminators

```
Γ ⊢ C : ℕ → U, z : C(𝟎), s : Π(k:ℕ).C(k) → C(suc(k)) ⊢ rec_ℕ(C, z, s, t) : C(t) (t : ℕ)
Γ ⊢ C : ℕ∞ → U, f : Π(k:ℕ).C(fin(k)), i : C(inf) ⊢ case_ℕ∞(C, f, i, t) : C(t) (t : ℕ∞)
Γ ⊢ A : U, t : Susp(A), C : Susp(A) → U, s : Π(a:A).C(susp(a)) ⊢ elim_Susp(C, s, t) : C(t)
Γ ⊢ A : U, t : Truncⁿ(A), C : Truncⁿ(A) → U, trunc : Π(a:A).C(truncⁿ(a)) ⊢ elim_Truncⁿ(C, trunc, t) : C(t)

Γ ⊢ t : A ∧ B, C : (A ∧ B) → U, s : Π(a:A).Π(b:B).C(smash(a, b)) Γ ⊢ elim_Smash(C, s, t) : C(t)
Γ ⊢ t : [A, B], C : [A, B] → U, m : Π(f:A→B).C(map(f)) Γ ⊢ elim_Map(C, m, t) : C(t)
Γ ⊢ E : Spec, C : Spec → U, : Π({Aₙ}:ℕ→U).Π({σₙ}:Π(n:ℕ).Aₙ→Susp(Aₙ₊₁)).C(spec({Aₙ},{σₙ})) ⊢ elim_Spec(C, s, E) : C(E)
Γ ⊢ A : Spec, t : πₙ^S(A), C : πₙ^S(A) → U, s : Π(k:ℕ).Π(a:πₙ₊ₖ(Aₖ)).C(stable(a)) ⊢ elim_πₙ^S(C, s, t) : C(t)

order : Π(n:ℕ).Π(m:ℕ).Π(x:πₙ(Sᵐ)).ℕ∞
order(n)(m)(x) = rec_ℕ(k ↦ ℕ∞, inf, λk.prev.case(test(k),
    λeq.fin(suc(k)), λ_.prev), suc(k_max))
    test(n)(m)(x)(k) = trunc⁰(pow(n)(m)(x)(k) = refl)
```

## Computations

```
rec_ℕ(C, z, s, 𝟎) ≡ z
rec_ℕ(C, z, s, suc(k)) ≡ s(k, rec_ℕ(C, z, s, k))
case_ℕ∞(C, f, i, fin(k)) ≡ f(k)
case_ℕ∞(C, f, i, inf) ≡ i
elim_Susp(C, s, susp(a)) ≡ s(a)
Susp(Sⁿ) ≡ Sⁿ⁺¹
elim_Truncⁿ(C, trunc, truncⁿ(a)) ≡ trunc(a)
πₖ(Truncⁿ(A)) ≡ 𝟎    (k > n)
Fib¹ ≡ S⁰ → S¹
Fib² ≡ S¹ → S³ → S²
Fib⁴ ≡ S³ → S⁷ → S⁴
Fib⁸ ≡ S⁷ → S¹⁵ → S⁸
(λx.t) u ≡ t[u/x]
fst(t, u) ≡ t
snd(t, u) ≡ u
πₙ(Sᵐ) ≅ Id_Suspⁿ⁻ᵐ(Fibᵏ)(hopfᵏ, hopfᵏ)    (m ≤ k, k ∈ {1, 2, 4, 8})
pow(n)(m)(x)(k) = rec_ℕ(k’ ↦ πₙ(Sᵐ), refl, λk’.p.p · x, k)
(p · q) · r ≡ p · (q · r), p · refl ≡ p, refl · p ≡ p, p · inv(p) ≡ refl

elim_Spec(C, s, spec({Aₙ},{σₙ})) ≡ s({Aₙ},{σₙ})
cup(map(f), map(g)) ↦ map(λx.kgn(tensor(f(x), g(x)), n+m))
cup(t, u) associative, graded-commutative
diffᵣ(diffᵣ(t)) ≡ 0    (d² = 0)
SS(E, r+1) ≅ ker(diffᵣ) / im(diffᵣ)    (next page)
diffᵣ(diffᵣ(t)) ≡ 0, SS(E, r+1) ≅ ker(diffᵣ) / im(diffᵣ)
Hⁿ(X; G) ≅ π₀^S([X, K(G, n)]), Hⁿ(X; G) ≅ π₋ₙ^S(HG ∧ X)
Hⁿ(X; G) ≅ π₀^S([X, K(G, n)]), Hⁿ(X; G) ≅ π₋ₙ^S(HG ∧ X)    (stable equivalence)
HG ∧ S⁰ ≡ HG
elim_Map(C, m, map(f)) ≡ m(f), πₙ^S([X, Y]) ≅ [Suspⁿ(X), Y]₀   (adjointness)
[spec({Aₙ},{σₙ}), spec({Bₙ},{τₙ})]ₖ ≡ [Aₖ, Bₖ]    (component-wise)
elim_Smash(C, s, smash(a, b)) ≡ s(a, b), S⁰ ∧ X ≡ X
(spec({Aₙ},{σₙ})) ∧ (spec({Bₙ},{τₙ})) ≡ spec({Aₙ ∧ Bₙ},{σₙ ∧ τₙ})
πₙ(K(G, n)) ≅ G, susp(kgn(g, n)) ↦ kgn(g, n+1)
loc_p(spec({Aₙ},{σₙ})) ↦ spec({Aₙ[p]},{σₙ[p]})
πₙ^S(A) ≡ colimₖ πₙ₊ₖ(Aₖ), stable(aₖ) ↦ colimₖ(aₖ)
elim_Spec(C, s, spec({Aₙ},{σₙ})) ≡ s({Aₙ},{σₙ})
πₙ^S(A ∧ B) ≅ colimₖ πₙ₊ₖ(Aₖ ∧ Bₖ) - stable Homotopy Refinement
```

## Coherences

```
susp(hopfⁿ) ↦ hopfⁿ⁺¹, (n ∈ {1, 2, 4}, n+1 ≤ 8)
susp(truncⁿ(a)) ↦ truncⁿ⁺¹(susp(a))
proj : Fibⁿ → Sᵐ, (m = n/2, e.g., Fib² → S²)
lift : Π(a:Sᵐ).Π(b:Sᵐ).Id_Fibⁿ(hopfⁿ, hopfⁿ) → Id_Sᵐ(a, b)
(p · q) · r ≡ p · (q · r)
p · refl ≡ p    refl · p ≡ p
p · inv(p) ≡ refl    (inv(p) : Id_A(v, u) if p : Id_A(u, v))
Γ ⊢ t : Trunc⁰(A), u : Trunc⁰(A) ⊢ t ≡ u : Trunc⁰(A) or  Γ ⊢ t ≠ u : Trunc⁰(A)
Γ ⊢ t : Fibⁿ  ⇒  t ≡ hopfⁿ
Γ ⊢ t : Truncⁿ(A)    Γ ⊢ u : Truncⁿ(A)    πₖ(t) ≡ πₖ(u) (k ≤ n)  ⇒  t ≡ u
```

## Copyright

Namdak Tonpa

