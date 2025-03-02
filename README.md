# JMTT: Jack Morava Type Theory

<img src="img/Jack_and_Ellen_Yoho_BC_1971.jpg" height=600/>

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
* Contexts: Γ ::= ∅, Γ + x:A.

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
* Types: HopfFibⁿ (n=1,2,4,8), Susp(A), Truncⁿ(A), ℕ, ℕ∞, Π(x:A).B, Σ(x:A).B, Id_A(u, v).
* Derivables: Sⁿ, πₙ(Sᵐ), order function.
* Terms: t, u, v ::= x, 𝟎, suc(t), fin(t), inf, hopfⁿ, susp(t), truncⁿ(t), λx.t, t u, (t, u), fst(t), snd(t), p, refl.
* Contexts: Γ ::= ∅ `|` Γ, x:A.

# Inference Rules

## Formations

```
Γ ⊢ Sⁿ : U := ℕ-iter U 𝟐 Susp
Γ ⊢ HopfFibⁿ : U (n ∈ {1, 2, 4, 8})
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
Susp: susp(t) : Susp(A) if t : A
Truncⁿ: truncⁿ(t) : Truncⁿ(A) if t : A
Π: λx.t : Π(x:A).B if Γ, x:A ⊢ t : B
Σ: (t, u) : Σ(x:A).B if t : A, u : B[t/x]
Id: refl : Id_A(u, u)
Γ ⊢ t : HopfFibⁿ  ⇒  t ≡ hopfⁿ
fiber : HopfFibⁿ → U (fiber(HopfFib¹) = S⁰, fiber(HopfFib²) = S¹, fiber(HopfFib⁴) = S³, fiber(HopfFib⁸) = S⁷)
total : HopfFibⁿ → U (total(HopfFib¹) = S¹, total(HopfFib²) = S³, total(HopfFib⁴) = S⁷, total(HopfFib⁸) = S¹⁵)
fibration : Π(f:HopfFibⁿ).fiber(f) → total(f)
lift : Π(a:Sᵐ).Π(b:Sᵐ).Id_Fibⁿ(hopfⁿ, hopfⁿ) → Id_Sᵐ(a, b)
inv : Id_A(u, v) → Id_A(v, u)
proj : HopfFibⁿ → Sᵐ, (m = n/2, e.g., HopfFib² → S²)
Spec : U, Aₙ : ℕ → U, σₙ : Aₙ → Susp(Aₙ₊₁) ⊢ spec({Aₙ}, {σₙ}) : Spec
S⁰ : Spec, S⁰ := spec({Sⁿ}, {σₙ}) ⊢ σₙ : Sⁿ → Susp(Sⁿ₊₁) ≡ Sⁿ⁺¹
Γ ⊢ A : Spec, a : A₀ ⊢ πₙ^S(A) : U := colimₖ πₙ₊ₖ(Aₖ)
stable(t) : πₙ^S(A)
A : Spec, p : ℕ (prime), S⁰[p] : Spec ⊢ loc_p(t) : S⁰[p]
grp(G, e, op, inv) : Group
smash(t, u) : ∧
t(E,r,p,q) : SS
map(t) : [,]
tensor(g, h) : G ⊗ H 
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
susp(HopfFibⁿ) ↦ HopfFibⁿ⁺¹, (n ∈ {1, 2, 4}, n+1 ≤ 8)
susp(truncⁿ(a)) ↦ truncⁿ⁺¹(susp(a))
Susp(HopfFib⁸) ≡ Susp(total(HopfFib⁸))    (fallback to S¹⁶)
Susp(Truncⁿ(A)) ↦ Truncⁿ⁺¹(Susp(A))    (term-level coherence)
elim_Truncⁿ(C, trunc, truncⁿ(a)) ≡ trunc(a)
πₖ(Truncⁿ(A)) ≡ 𝟎    (k > n)
HopfFib¹ ≡ S⁰ → S¹
HopfFib² ≡ S¹ → S³ → S²
HopfFib⁴ ≡ S³ → S⁷ → S⁴
HopfFib⁸ ≡ S⁷ → S¹⁵ → S⁸
fibration(HopfFibⁿ) : fiber(HopfFibⁿ) → total(HopfFibⁿ)
proj(fibration(HopfFibⁿ)(x)) ≡ baseᵐ
lift(baseᵐ, baseᵐ, refl) ≡ refl
lift(a, b, p) · q ≡ lift(a, c, p · q)    (path composition)
πₙ(Sᵐ) ≅ Id_total(HopfFibᵏ)(fibration(hopfᵏ)(x), fibration(hopfᵏ)(y))    (adjusted definition)
(λx.t) u ≡ t[u/x]
fst(t, u) ≡ t
snd(t, u) ≡ u
πₙ(Sᵐ) ≅ Id_Suspⁿ⁻ᵐ(HopfFibᵏ)(hopfᵏ, hopfᵏ)    (m ≤ k, k ∈ {1, 2, 4, 8})
pow(n)(m)(x)(k) = rec_ℕ(k’ ↦ πₙ(Sᵐ), refl, λk’.p.p · x, k)
(p · q) · r ≡ p · (q · r), p · refl ≡ p, refl · p ≡ p, p · inv(p) ≡ refl
proj(hopfⁿ) ≡ baseᵐ    (fixed point in Sᵐ)
lift(a, b, p) · q ≡ lift(a, c, p · q)    (path composition)

πₙ^S(S⁰) ≡ colimₖ πₙ₊ₖ(Sᵏ)
stable(aₖ) ↦ colimₖ(aₖ)    (aₖ : πₙ₊ₖ(Aₖ))
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
πₙ^S(S⁰[p]) ≡ πₙ^S(S⁰) ⊗ ℤ_{(p)}    (p-local integers)
elim_Spec(C, s, spec({Aₙ},{σₙ})) ≡ s({Aₙ},{σₙ})
πₙ^S(A ∧ B) ≅ colimₖ πₙ₊ₖ(Aₖ ∧ Bₖ) - stable Homotopy Refinement
Γ ⊢ finite : Π(n:ℕ).Π(m:ℕ).Trunc⁰(πₙ(Sᵐ)) → U, finite(n)(m)(trunc⁰(x)) = Σ(k:ℕ).Id_πₙ(Sᵐ)(pow(n)(m)(x)(k), refl)
```

## Coherences

```
(p · q) · r ≡ p · (q · r)
p · refl ≡ p    refl · p ≡ p
p · inv(p) ≡ refl    (inv(p) : Id_A(v, u) if p : Id_A(u, v))
Γ ⊢ t : Trunc⁰(A), u : Trunc⁰(A) ⊢ t ≡ u : Trunc⁰(A) or  Γ ⊢ t ≠ u : Trunc⁰(A)
Γ ⊢ t : HopfFibⁿ  ⇒  t ≡ hopfⁿ
Γ ⊢ t : Truncⁿ(A)    Γ ⊢ u : Truncⁿ(A)    πₖ(t) ≡ πₖ(u) (k ≤ n)  ⇒  t ≡ u
```

## Publications

* <a href="https://tonpa.guru/stream/2018/2018-06-29 Хроматична Теорія Гомотопій.htm">2018-06-29 Хроматична Теорія Гомотопій</a>
* <a href="https://tonpa.guru/stream/2020/2020-05-03 Модельні категорії.htm">2020-05-03 Модельні категорії</a>

## Copyright

Namdak Tonpa
