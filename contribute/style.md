# NCML Coding Style

Coding conventions for the formal proofs in this repository. The guiding principle: proofs are read and maintained by humans, so write them the way the human maintainers read them.

As a baseline, follow the [Mathlib style guide](https://leanprover-community.github.io/contribute/style.html) (line length, spacing, naming, calc/tactic formatting, etc.). This document only records what is specific to this project; where it differs from the Mathlib guide, this document takes precedence.

The examples below are deliberately elementary — arithmetic, lists, orders — rather than drawn from the repository's own modal-logic material, so that each one illustrates the convention and nothing else. Keep them that way when adding items: an example that first has to be understood as mathematics has stopped being an example.

Human contributors need not follow this document to the letter — treat it as a description of the house style. 🤖 AI coding agents should follow it as closely as possible, especially the items marked 🤖: machine-generated proofs tend to drift toward a verbose, defensive style, and those items exist to counteract that drift.

## General conventions

- **Use `lemma`, not `theorem`, for auxiliary results.** Reserve `theorem` for the headline results a
  reader would look up: the formalized counterparts of a source's numbered theorems, and the main entry
  points of a file's API. Closure lemmas, derived rules, combinators and technical bridges are `lemma`.
  Most files should end up with zero or one `theorem`; when a declaration's status is unclear, use
  `lemma`.
- Omit type annotations that are trivially inferred from context.
- Do not introduce implicit variables ad hoc in lemma statements. Declare them with `variable` in a `section`, and cut a new `section` when the context changes, rather than keeping one giant file-wide block.

## Proof style

Overall: construct terms directly when the type determines them, and hand the residue to automation — rather than opening holes in the goal and filling them one by one.

🤖 **Prefer direct term construction over `refine … ?_`.**

```lean
-- Avoid:
refine ⟨n, ?_, ?_⟩
· exact hn
· exact hn.le

-- Prefer:
exact ⟨n, hn, hn.le⟩
```

Reserve `refine` for components that genuinely need tactic work — and never write bound variables inside it:

```lean
-- Avoid:
refine ⟨hd, fun x hx => ?_⟩

-- Prefer:
refine ⟨hd, ?_⟩
intro x hx
```

**Prove existential goals with `use`, not `refine`.** Avoid leaving `?_` holes where `use` closes the goal directly.

**Split nested conjunctions with `and_intros`,** not `refine ⟨?_, ⟨?_, ?_⟩, ?_⟩` or repeated `constructor`.

Conversely, **do not fold a `constructor` and its branches into one anonymous constructor when the folded term would be long**. The measure is the term written out on a single line without wrapping: short enough to read at a glance, `exact ⟨…, …⟩` is fine; longer than that, give each part its own branch under `constructor` or `and_intros`, even though it costs lines. The two directions of an `↔`, and the components of a `∧` proved separately, are what a reader matches against the statement.

**Use `obtain` when extracting witnesses from existential hypotheses** (`obtain ⟨n, hn⟩ := exists_bound f`), in preference to `rcases`/`rintro`. For other pattern decomposition, `rcases`/`rintro` are equally fine.

🤖 **Use `show` only when the goal unfolds non-trivially.** Restating a goal that is already displayed in the needed form is noise.

**Prefer term-mode pattern matching for structural inductions**, or `induction` with a `<;> simp`-style batch discharge:

```lean
theorem Even.add_two : Even n → Even (n + 2)
  | zero      => …
  | add_two h => …
```

When running an `induction`, try `grind` or `simp_all` on the trivial cases (base cases, plain recursive cases) before writing them out — they usually close.

🤖 **Lean on automation for the final assembly.** State the few needed facts as `have`s and pass them to a tactic (`grind`, `simp`) instead of hand-chaining compositions:

```lean
-- Prefer:
have h₁ : P ↔ Q := …
have h₂ : Q ↔ R := …
grind

-- Avoid:
exact step1.trans <| step2.trans <| step3.trans step4
```

🤖 **Keep proofs short; extract lemmas.** A tactic block beyond roughly thirty lines should be split: promote intermediate `have`s to stand-alone (possibly `private`) lemmas.

🤖 **Do not bundle lemmas into a `structure … : Prop` for convenience.** It is justified only when three or more properties must travel together as the hypothesis of a mutual or nested induction; otherwise state separate lemmas.

🤖 **Do not introduce disjunctions with `Or.inl` / `Or.inr`.** Use the `left` / `right` tactics, let `tauto`, `grind` or `simp` discharge the goal, or restructure so that the disjunction never has to be introduced by hand. A term-mode `Or.inl` is acceptable only where it is plainly the clearest thing to write.

```lean
-- Avoid:
exact Or.inr ⟨y, z, Ixy, Myz, Izx⟩

-- Prefer:
right;
exact ⟨y, z, Ixy, Myz, Izx⟩
```

🤖 **`open` the namespaces you would otherwise spell out repeatedly.** Writing `Model.Forces.persistent` and `Model.Forces.of_fallible` throughout a file is noise; `open Model.Forces` at the top and then `persistent` / `of_fallible` reads better and is shorter. The same goes for `Model`, `ProvableBDHilbert`, and `BDFormula`. Place the `open` lines where the surrounding files place theirs, and stop short of the point where an unqualified name becomes ambiguous or misleading to a reader.

**When proving several equivalences at once with `List.TFAE`, do not refer to them by index** (`foo_TFAE.out 1 0`) from other proofs: the indices break as soon as the list is reordered. Cut the individual implications out as named lemmas instead.

### Trailing semicolons

Terminate each tactic line with a semicolon (`;`). This is a deliberate house convention of this repository; do not strip the semicolons in the course of an unrelated refactor.

## Naming intermediate steps

🤖 Name intermediate `have`s with short positional names (`h₁`, `h₂`, …) or conventional ones (`hp`, `ih`), and let the type annotation carry the meaning. Do not give every step a one-shot descriptive compound name — it duplicates the type and goes stale under refactoring. A descriptive name is warranted only when the fact is referred to several times.

```lean
-- Prefer:
have h₁ : a ≤ b := le_of_lt hab
have h₂ : b ≤ c := hbc.le
exact h₁.trans h₂

-- Avoid:
have ha_le_b_of_lt  : a ≤ b := le_of_lt hab
have hb_le_c_weaken : b ≤ c := hbc.le
exact ha_le_b_of_lt.trans hb_le_c_weaken
```

## Variable naming

Modal logic:

| kind | letters |
| --- | --- |
| propositional variables | `a`, `b`, `c`, … |
| formulas | `A`, `B`, `C`, `D`, … |
| lists / finite sets of formulas | `Γ`, `Δ` |
| theories | `T`, `T₁`, `U` |
| sets of formulas not meant as theories | `X`, `Y`, `Z` |
| pair-canonical-model worlds (`CanonicalPair L`) | `P`, `Q` / `P₁`, `P₂` |

Never use Greek letters (`φ`, `ψ`) or late-alphabet capitals (`P`, `Q`) for modal formulas — those namespaces are taken: `P`/`Q` name the worlds of a pair canonical model (`CanonicalPair L`), spelled `P₁`, `P₂`, … when more than two are in scope. `Γ` and `Δ` are for lists and finite sets only: a theory is `T`, and a set of formulas that is not yet known to be one is `X`, `Y` or `Z`. Within a proof, introduce formulas in order (`A`, `B`, `C`), without skipping letters.

Kripke semantics: worlds are `x`, `y`, `z`, `w`, `v`, `u`. When introducing several world variables, use subscripted names (`x₁`, `x₂`, `y₁`, `y₂`, …) rather than primed variants (`x'`, `x''`). When building one model out of another, index the new model by `M.World` rather than reintroducing a `κ : Type u`. This applies to the worlds of a general `Model κ`; a pair canonical model's worlds are `CanonicalPair L`-typed and use `P`/`Q` instead (see above).

Name a hypothesis witnessing a binary relation `R x y` after the relation's leading letter plus the two endpoints it relates: an `iRel x y` hypothesis is named `Ixy`, an `mRel x y` hypothesis is named `Mxy` (e.g. `Ix₁x₂ : x₁ ≼ x₂`, `Mx₂y₂ : x₂ ⊏ y₂`). Avoid generic names such as `h`, `h1`, `h2`, `hxy`.

## Signature indentation

When a declaration signature spans several lines, indent the first level of continuation by **two spaces** from the declaration keyword (`lemma`/`theorem`/`def`). This applies to the branches of a `↔`/`→` broken across lines, to binders placed on their own lines, and to a `: …` result line. The only exception is a single binder (or result type) that is itself too long: its inner continuation may be indented one further level.

```lean
-- Avoid (four-space, staircase indentation):
lemma foo_bar_indep {A : Baz α} (hA : A.Cond) :
    P (f a b) A ↔
      P (f a' b) A := by

-- Prefer:
lemma foo_bar_indep {A : Baz α} (hA : A.Cond) :
  P (f a b) A ↔
  P (f a' b) A := by

lemma sup_le_of_forall_le
  (hbound :
    ∀ {α : Type u} [SemilatticeSup α] [OrderBot α] (s : Finset α) (a : α),
    (∀ b ∈ s, b ≤ a) → s.sup id ≤ a
  )
  : s.sup id ≤ a := by
```

## Comments and docstrings

All comments and docstrings are written in English.

🤖 Keep comments minimal. A docstring says what the declaration is, and nothing else — one line wherever possible. It does not give the proof strategy, the motivation, a comparison with the literature, or a justification for a design choice; if the name already says it, drop the docstring entirely. Reasons of that kind belong in the pull request, not in the source. Do not annotate individual `have`s with comments restating them. An inline comment is justified only for what the code cannot express (an elaboration pitfall, why a natural alternative fails), in about one line. Long "Implementation notes" sections are unwanted; if the design needs that much explanation, restructure the proof instead. A proof sketch inside the proof body is warranted only when it will genuinely help someone writing a neighbouring proof. Most declarations need no docstring at all: the default is to omit one, and add it back only where it earns its place.

Module docstrings must be placed before `@[expose] public section`.

### What, not why or how

🤖 **A docstring says what a declaration is. It never says why it exists, and never says how it is proved.** State the content of the definition or statement and stop there.

Out of scope as **why**: motivation, design rationale, the role the declaration plays in a larger development, comparisons with alternatives that were rejected, and remarks on how it will be used later — even when true and even when short.

```lean
-- Avoid:
/-- The divisors of `n`, in increasing order. We return a `List` rather than a `Finset`
because the sieve below consumes the divisors in order, and converting between the two
turned out to dominate the running time. -/

-- Prefer:
/-- The divisors of `n`, in increasing order. -/
```

Out of scope as **how**: the proof method, the induction and its measure, which case is the hard one, which lemma does the work, and how far the argument follows or departs from the source. The docstring describes the statement, which is the same whether the proof is three lines of `grind` or three hundred lines of induction; a reader who wants the method reads the proof.

```lean
-- Avoid:
/-- Every natural number greater than `1` has a prime factor. Proved by strong induction
on `n`: if `n` is prime there is nothing to do, otherwise split off a proper divisor and
apply the induction hypothesis, the composite case being the only delicate one. -/

-- Prefer:
/-- Every natural number greater than `1` has a prime factor. -/
```

The same holds for the module docstring: describe what the file defines and proves, not why the file was split out this way, what motivated the development, or by what route the results are obtained.

These remain welcome, and are neither why nor how in this sense: the citation list (see below), the one-line inline comments inside a proof body that record what the code cannot express, and the mandatory explanation attached to a `set_option` (see below). A statement that is genuinely only meaningful relative to another declaration may name that relationship as a fact ("the converse of `foo`"), which is still what.

### Naming imported from the literature

Write the names used in this repository, not the notation of the source paper. The one exception is the docstring of the definition itself, which may record where the alternative name comes from ("also known as `K4.3` in the source").

The same applies to labels: do not carry over tags such as "condition (C)" or "property (\*)" from a paper or a planning document, and do not invent new ones. A condition is referred to by the name of the class or definition that states it.

### References and citations

When a definition or theorem formalizes a result from the literature, add the source to [references.bib](../references.bib) (formatted with bibtool, see [index.md](./index.md)) and cite it in the docstring, so a reader can find the informal counterpart.

Citations go at the end of the docstring as a list, one line per BibTeX key, of the form `- [key, kind number]` — even for a single citation. Do not embed them in running text, write `**Corollary 41(i) in [AB05]**:`, or spell out author names, years, titles and journals. Several results from the same key stay on one line:

```
- [AB05, Corollary 42]
- [VS83, Theorem 10, Theorem 11(b), Theorem 11(c)]
```

If you find a bare year or author name in a docstring, look the work up in `references.bib` and replace it with the key. If no entry corresponds, leave it as plain prose without brackets.

**Cite a declaration only when the declaration IS the cited result.** A citation asserts "this statement is that numbered result of that paper" — not "this is used in the proof of it", and not "this is about the same subject". A step extracted from a source's proof, a technical bridge, and general vocabulary all get no citation, and no note explaining the absence either. Most declarations need none: default to omitting. A `private` declaration never carries one.

This applies to what actually formalizes a result: a definition or theorem the source states. General-purpose vocabulary does not need a citation at all — an auxiliary operation that a paper happens to use along the way is ordinary notation, not a formalization of that paper. Do not decorate such declarations with a source, and do not write a note explaining their absence either.

### Stale comments and planning artifacts

🤖 Code and docstrings must not reference development-time artifacts: plan steps ("see plan Step4 §3"), issue numbers, bare step numbers, section/line labels (`§2`, `L4-1`), or the implementation status of another file ("even while Step 2 is incomplete…"). Fine as working memos, but remove or rewrite them into self-contained explanations before submission. `grep -n "see plan\|issue #\|Step [0-9]\|§[0-9]\|L[0-9]-[0-9]"` helps find survivors; note that `§` inside a citation list entry is legitimate.

🤖 Likewise remove skeleton-era comments (e.g. "most lemmas below are stated with `sorry`") that contradict the finished code.

## The `grind` tactic

Attach `@[grind]` to lemmas and definitions that plausibly help `grind` close goals, choosing a direction (`@[grind =>]`, `@[grind .]`) where it matters. 🤖 Do not attach it mechanically to every declaration. The post-hoc form `attribute [grind] name₁ name₂ …` is also acceptable. Inside proofs, try `grind` before settling on a longer tactic sequence.

## `set_option`

Whenever you use `set_option` (including the single-declaration form `set_option foo false in`), always add a comment explaining the intent: which option is changed, why, and for which declaration. The comment must make clear to a later reader that the option change is deliberate, not a workaround left behind by accident. For example, when suppressing a linter warning:

```lean
-- Intentionally kept as a global simp lemma; scoping it would break implicit uses elsewhere.
set_option warning.simp.varHead false in
@[simp] lemma eq_zero : n = 0 := by cases n; omega
```

**`set_option maxHeartbeats` must not be used actively.** 🤖 In particular, do not raise it to push a proof through — needing it is a sign the proof is in an inefficient form. If a proof only works that way, refactor until the option is unnecessary: extract lemmas, narrow `grind`/`simp` sets, avoid computationally heavy definitions.

## The module system

Cross-file `scoped` notation requires `open scoped Ns` at the use site; a plain `open Ns` does not bring it into scope.
