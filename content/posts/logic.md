---
title: Basic Logic in Lean
date: 2020-08-30
---

A cool website for learning some basic logic is the Incredible Proof Machine, which can be found [here](http://incredible.pm/). The web UI allows for the user to see what they're doing, and how everything ties together. However, this UI can sometimes be a bit frustrating, and sometimes we end up spending more time than necessary creating the same sub-proof over and over again. So I got interesting in trying to port this to Lean, and see what it would be like to try and solve them in Lean instead.

## Session 1

All of the exercises in Session 1 on the page are to do with conjunctions, and we can easily formalise these in Lean. For example, we can look at a basic exercise showing that `A ∧ B → B ∧ A`.

```lean
example (h : A ∧ B) : B ∧ A :=
begin
  cases h with hA hB,
  split,
  exact hB,
  exact hA,
end
```

Much like the webpage, we can split the `A ∧ B` into `A` and `B`. We can also split the goal `B ∧ A` into `B` and `A` and prove each one separately.

## Session 2

In Session 2, implication is introduced. In the Incredible Proof Machine, there is a block for showing that if `X → Y` and we have a proof of `X`, then we have a proof of `Y`. In Lean, `X → Y` is just the type of functions from `X` to `Y`, so this is in fact just the same as applying a function. There is also a block for showing `X → Y`, and in Lean we can emulate that with a `have`, which adds a new local hypothesis.

```lean
example (h1 : A → A → B) (h2 : (A → B) → A) : B :=
begin
  have hAB : A → B,
  { intro a,
    apply h1,
    exact a,
    exact a },
  have hA : A,
  { apply h2,
    exact hAB },
  apply h1,
  exact hA,
  exact hA
end
```

## Interlude - Term Mode

Using just `have`, `intro`, `apply`, `exact`, `cases` and `split`, we can solve all of the goals here. But if we're only using these tactics, there is little to no benefit with using tactics, since we could just as well use term mode, which would also end up being less verbose. Let's go through converting our proofs into term mode.

To start off, let's use the second proof.

```lean
example (h1 : A → A → B) (h2 : (A → B) → A) : B :=
```

We can change the `have` into term mode fairly easily, the only changes are that we need to use `by` to go back into tactic mode for the time being.

```lean
example (h1 : A → A → B) (h2 : (A → B) → A) : B :=
have hAB : A → B, by { intro a, apply h1, exact a, exact a },
have hA : A, by { apply h2, exact hAB },
sorry
```

Then, we cna use the `show_term` tactic to convert our proofs from tactic mode to term mode. If we put `show_term` after the `by` like so, we get the corresponding term. Click on the suggestion and it will automatically replace the proof.

```lean
example (h1 : A → A → B) (h2 : (A → B) → A) : B := 
have hAB : A → B, by show_term { intro a, apply h1, exact a, exact a },
have hA : A, by { apply h2, exact hAB },
sorry
```

However, in term mode we will need a `from` to tell Lean what comes next is a proof of the local hypothesis.

```lean
example (h1 : A → A → B) (h2 : (A → B) → A) : B := 
have hAB : A → B, from λ (a : A), h1 a a,
have hA : A, by { apply h2, exact hAB },
sorry
```

We can do the same with the second `have`,

```lean
example (h1 : A → A → B) (h2 : (A → B) → A) : B := 
have hAB : A → B, from λ (a : A), h1 a a,
have hA : A, from h2 hAB,
sorry
```

Finally, paste in the code to finish the proof into another `by {}`, and we can use `show_term` to automatically generate the term for us.

```lean
example (h1 : A → A → B) (h2 : (A → B) → A) : B := 
have hAB : A → B, from λ (a : A), h1 a a,
have hA : A, from h2 hAB,
by { apply h1, exact hA, exact hA }
```

We don't need to add a `from` here, so it looks like this:

```lean
example (h1 : A → A → B) (h2 : (A → B) → A) : B := 
have hAB : A → B, from λ (a : A), h1 a a,
have hA : A, from h2 hAB,
h1 hA hA
```

Equally, we could have copied our original tactic proof and let `show_term` generate the term mode proof, which would look like so:

```lean
example (h1 : A → A → B) (h2 : (A → B) → A) : B := 
h1 (h2 (λ (a : A), h1 a a)) (h2 (λ (a : A), h1 a a))
```

We can do something similar for the first proof. `show_term` can be used, but the proof it generates is not "idiomatic".

```lean
example (h : A ∧ B) : B ∧ A :=
```

The `cases` line can be replaced with `let ... := ... in ...` and pattern matching. `⟨hA, hB⟩` is an anonymous constructor, and 

```lean
example (h : A ∧ B) : B ∧ A :=
let ⟨hA, hB⟩ := h in
_
```
