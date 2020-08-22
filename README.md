# Schmitty the Solver

If you wanna solve some problems, you’re in luck! Schmitty is an Agda library which gives you bindings to SMT solvers! I know, cool right?!

So basically, what Schmitty can offer you right now is a well-typed embedding of *some* of the SMT-LIB language in Agda. That means you can write SMT queries in Agda, like this!
```agda
blegh : Script [] (INT ∷ INT ∷ []) (SAT ∷ [])
blegh = declare-const INT
      ∷ declare-const INT
      ∷ assert (app₂ eq
               (app₂ sub x y)
               (app₂ add (app₂ add x (app₁ neg y)) (lit (int 1)))
               )
      ∷ check-sat
      ∷ []
      where
        x = var (suc zero , refl)
        y = var (    zero , refl)
```
Where is the solving? You might’ve seen that I recently extended Agda with the `execTC` primitive, which allows you to make arbitrary system calls… well, within reason at least. Schmitty lets to take the script above, print it as an SMT-LIB term, and pass it to Z3!
```agda
_ : z3 blegh ≡ unsat ∷ []
_ = refl
```
Aww, boo, that one isn’t satisfiable! Did you pick up on that `unsat` there? Schmitty doesn’t just give you back the solver’s output… she is kind enough to actually parse the output for you! In fact, while Schmitty prints the term, she is builds you an output parser, which can parses the solver output, including models! Let’s make sure the next one is satisfiable!
```agda
yesss : Script [] (INT ∷ INT ∷ []) (SAT ∷ [])
yesss = declare-const INT
      ∷ declare-const INT
      ∷ assert (app₂ eq x y)
      ∷ get-model
      ∷ []
      where
        x = var (suc zero , refl)
        y = var (    zero , refl)
```
If we call `get-model` instead of `check-sat`, Schmitty will give us back a valid model!
```agda
_ : z3 yesss ≡ ((+ 0 ∷ + 0 ∷ []) ∷ [])
_ = refl
```
Okay, I know that wasn’t a particularly hard problem, but I was in a rush. Send me a pull-request if you’ve got better queries for Schmitty!

If you’d like to work with Schmitty, a good place to start are the examples. Right now, Schmitty supports two theories, [Core][SMT.Theories.Core] and [Ints][SMT.Theories.Ints], and one backend, [Z3][SMT.Backend.Z3]. I’ve got a couple of other theories and backends under development, but if you’d like to contribute, your help is more than welcome!

The examples are a good place to start reading! You can find them in [`SMT.Theories.Core.Example`][SMT.Theories.Core.Example] and [`SMT.Theories.Ints.Example`][SMT.Theories.Ints.Example]!

# Roadmap

- [ ] Finish Reals theory for Floats and Rationals.
- [ ] Add error reporting to the output parser.
- [ ] Merge [`Reflection.External`][Reflection.External] into [agda-stdlib][agda-stdlib].
- [ ] Use reflection to reflect Agda expression to SMT-LIB terms.
- [ ] Use postulates to provide “evidence” when the solver succeeds.
- [ ] Use [kazkansouh][kazkansouh]’s SAT solver to provide *actual* evidence for the Core theory.

---

Note: You’ll need *at least* [Agda version 2.6.2-20eb4f3][agda-version] to run Schmitty.

[SMT.Theory]: https://wenkokke.github.io/schmitty/SMT.Theory.html
[SMT.Theories.Core]: https://wenkokke.github.io/schmitty/SMT.Theories.Core.html
[SMT.Theories.Core.Extensions]: https://wenkokke.github.io/schmitty/SMT.Theories.Core.Extensions.html
[SMT.Theories.Core.Example]: https://wenkokke.github.io/schmitty/SMT.Theories.Core.Example.html
[SMT.Theories.Ints]: https://wenkokke.github.io/schmitty/SMT.Theories.Ints.html
[SMT.Theories.Ints.Example]: https://wenkokke.github.io/schmitty/SMT.Theories.Ints.Example.html
[SMT.Theories.Reals]: https://wenkokke.github.io/schmitty/SMT.Theories.Reals.html
[SMT.Script]: https://wenkokke.github.io/schmitty/SMT.Script.html
[SMT.Logics]: https://wenkokke.github.io/schmitty/SMT.Logics.html
[SMT.Backend.Z3]: https://wenkokke.github.io/schmitty/SMT.Backend.Z3.html
[Reflection.External]: https://wenkokke.github.io/schmitty/Reflection.External.html
[agda-stdlib]: https://github.com/agda/agda-stdlib
[agda-version]: https://github.com/agda/agda/commit/20eb4f3ebb6eb73385f2651cf9b5c4bdac9a2f10
[kazkansouh]: https://github.com/kazkansouh
