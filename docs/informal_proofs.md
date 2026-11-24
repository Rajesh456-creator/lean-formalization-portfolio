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

## Ramsey R(3,3) = 6

**Upper bound.** Colour the pairs of {0,…,5} with two colours. Vertex 0 has five edges and only two
colours, so three of them, to vertices a < b < d, have the same colour x. Look at the edges ab, ad, bd:

* if one of them has colour x, it forms a monochromatic triangle together with 0;
* otherwise all three have the other colour, so a, b, d is a monochromatic triangle.

**Lower bound.** Colour the pair {i, j} of {0,…,4} by "adjacent on the 5-cycle 0-1-2-3-4-0".
The cycle and its complement (the pentagram, which is also a 5-cycle) are both triangle-free,
so there is no monochromatic triangle.

## Van der Waerden W(2;3) = 9

**Upper bound.** There are only 2^9 = 512 colourings of {0,…,8}, and 16 three-term progressions
(7 with d = 1, 5 with d = 2, 3 with d = 3, 1 with d = 4). Lean checks all cases with `decide`.

**Lower bound.** Colour 0,…,7 as RRBBRRBB, i.e. colour(n) depends only on n mod 4. A progression a, a+d, a+2d has d ≤ 3:

* d = 1: three consecutive terms always contain both colours (runs have length at most 2).
* d = 2: a and a+4 have the same colour, but a+2 has the opposite colour.
* d = 3: a+6 ≡ a+2 (mod 4), so a+6 has the opposite colour from a.

So no progression is monochromatic.

## Schur S(2) = 4

**Upper bound.** There are 2^5 = 32 colourings of {1,…,5}. The relevant triples x + y = z are
1+1=2, 1+2=3, 1+3=4, 1+4=5, 2+2=4, 2+3=5, and Lean checks that every colouring makes one of them monochromatic.

**Lower bound.** Colour 1 and 4 red, 2 and 3 blue. Then 1+1=2 (R,R,B), 1+2=3 (R,B,B),
1+3=4 (R,B,R) and 2+2=4 (B,B,R) all use both colours.
