# Schmitty the Solver

Schmitty is an Agda library which uses the new `execTC` primitive to integrate Agda with SMT-LIB compliant solvers.

The library contains a well-typed embedding of *a subset of* SMT-LIB lisp:

- [`SMT.Script`][SMT.Script]
- [`SMT.Script.Show`][SMT.Script.Show]
- [`SMT.Theory`][SMT.Theory]
- [`SMT.Theories.Core`][SMT.Theories.Core]
- [`SMT.Theories.Core.Extensions`][SMT.Theories.Core.Extensions]
- [`SMT.Theories.Ints`][SMT.Theories.Ints]
- [`SMT.Theories.Reals`][SMT.Theories.Reals]

Macros to run SMT scripts on various backends:

- [`SMT.Backend.Z3`][SMT.Backend.Z3]
- [`Reflection.External`][Reflection.External]

As well as a number of examples:

- [`SMT.Theories.Ints.Example`][SMT.Theories.Ints.Example]
- [`SMT.Theories.Core.Example`][SMT.Theories.Core.Example]

The examples are a good place to start reading!

# Roadmap

- [ ] Merge [`Reflection.External`][Reflection.External] into [agda-stdlib][agda-stdlib].
- [ ] Implement lattice of logics.
- [ ] Extend theories with a logic checker.
- [ ] Parse solver *output* and convert to Agda types.
- [ ] Reflect Agda types to SMT lisp terms.
- [ ] Provide solver macro which provides “evidence” using postulates.
- [ ] Integrate Core theory with @kazkansouh’s SAT solver.

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
[SMT.Script.Show]: https://wenkokke.github.io/schmitty/SMT.Script.Show.html
[SMT.Backend.Z3]: https://wenkokke.github.io/schmitty/SMT.Backend.Z3.html
[Reflection.External]: https://wenkokke.github.io/schmitty/Reflection.External.html
[agda-stdlib]: https://github.com/agda/agda-stdlib
[agda-version]: https://github.com/agda/agda/commit/20eb4f3ebb6eb73385f2651cf9b5c4bdac9a2f10
