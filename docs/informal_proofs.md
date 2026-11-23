# Informal proofs

## Knaster–Tarski
Let L be a complete lattice, f : L → L monotone, P = {x | f x ≤ x}, a = inf P.

1. For every x ∈ P: a ≤ x, so f a ≤ f x ≤ x. Hence f a is a lower bound of P, so f a ≤ a.
2. Applying f to f a ≤ a gives f (f a) ≤ f a, so f a ∈ P, hence a ≤ f a.
3. By antisymmetry f a = a.
4. If f x = x then x ∈ P, so a ≤ x: a is the least fixed point.

The greatest fixed point is the order-dual argument with sup and post-fixed points {x | x ≤ f x}.

## Cantor–Schröder–Bernstein
Let f : A → B, g : B → A be injective.

1. Define F on subsets of A: F(S) = A \ g[B \ f[S]]. F is monotone (larger S ⇒ larger f[S] ⇒ smaller B \ f[S] ⇒ smaller g[…] ⇒ larger F(S)).
2. By Knaster–Tarski take S with F(S) = S, i.e. A \ S = g[B \ f[S]].
3. Define h(a) = f(a) if a ∈ S, and h(a) = the unique b with g(b) = a if a ∉ S (exists by step 2).
4. Injective: two points in S use injectivity of f; two outside S use that g is a function;
   one in S and one outside would give a b ∈ f[S] with g(b) ∉ S, contradicting b ∈ B \ f[S].
5. Surjective: b ∈ f[S] is hit from S. Otherwise b ∈ B \ f[S], so g(b) ∉ S and h(g(b)) = b by injectivity of g.
