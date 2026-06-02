# fiat-pyrosome translator

## structure + roadmap

(as of 02 june 2026)

run `make -j16` to build. `pyrosome` and `fiat2` build fine let's keep it that way

- `Translator.v` (contains actual translation functions)
  - [x] fiat to pyro is good and has some interesting stuff
  - [ ] pyro to fiat is more rudimentary atm
    - [ ] need variable naming (the sorting order is wrong. annoying)
- `FiatToPyroSound.v` (proofs)
  - [x] type safety proof (works well! for now)
    - [x] tactics run in reasonable time 
- `PyroToFiatSound.v` (proofs)
  - [ ] type safety proof
    - [ ] **blocker: value sort equivalence: figure out subst / contexts**
    - [ ] sorting admits (see translator.v)
  - [ ] some cleanup? (things are named stupidly and unreferenceable)
  - i could probably write a tactic for rule checks (currently it's `repeat [destruct H; equality]`)

## things to note before i forget

### how to induct on pyrosome terms

`BoolLang.v` (for reference) is [here](https://github.com/DIJamner/pyrosome/blob/623eb535d87bbb6fb9aabb4a656ccbfa4d0bd3fd/WIP/BoolLang.v)

notes from meeting: 

```
judgement induction should...

   one level of induction -- there's a lemma for that...
   eq_sort causes issues...
   the t being scon ty directly might be bad for induction in rocq / you don't want to lose the generality
   the ty thing: induction rather than conclusion
   and rocq equality rather than eq_sort

   lemma: sort equality on ty, list_ty has to...
   ref boollang.v

   list_ty and ty: manually write a lemma for cases
```

dealing with `wf_args`: repeated destruct is fine

### tactics

- custom tactics are in `Tactics.v`
- `eauto` takes infinite time, be careful. 90% of things being slow is that
  - use auto or limit scope where possible
  - `eauto 2` works well
- tactic profiling: `Set Ltac Profiling` to start profiling and `Show Ltac Profile` to well show profile
  - but this will **timeout with pyrosome terms** (`{{e {x} ...}}`) so make sure you disable it
- `cbn` is useful `intuition` is useful
