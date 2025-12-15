Library Style Guidelines
In addition to the naming conventions, files in the Lean library generally adhere to the following guidelines and conventions. Having a uniform style makes it easier to browse the library and read the contents, but these are meant to be guidelines rather than rigid rules.

Variable conventions
u, v, w, ... for universes
α, β, γ, ... for generic types
a, b, c, ... for propositions
x, y, z, ... for elements of a generic type
h, h₁, ... for assumptions
p, q, r, ... for predicates and relations
s, t, ... for lists
s, t, ... for sets
m, n, k, ... for natural numbers
i, j, k, ... for integers
Types with a mathematical content are expressed with the usual mathematical notation, often with an upper case letter (G for a group, R for a ring, K or 𝕜 for a field, E for a vector space, ...). This convention is not followed in older files, where greek letters are used for all types. Pull requests renaming type variables in these files are welcome.

Line length
Lines should not be longer than 100 characters. This makes files easier to read, especially on a small screen or in a small window. If you are editing with VS Code, there is a visual marker which will indicate a 100 character limit.

Header and imports
The file header should contain copyright information, a list of all the authors who have made significant contributions to the file, and a description of the contents. Do all imports right after the header, without a line break, on separate lines.

/-
Copyright (c) 2024 Joe Cool. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joe Cool
-/
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Group.Defs
(Tip: If you're editing mathlib in VS Code, you can write copy and then press TAB to generate a skeleton of the copyright header.)

Regarding the list of authors: use Authors even when there is only a single author. Don't end the line with a period, and use commas (, ) to separate all author names (so don't use and between the penultimate and final author.) We don't have strict rules on what contributions qualify for inclusion there. The general idea is that the people listed there should be the ones we would reach out to if we had questions about the design or development of the Lean code.

Module docstrings
After the copyright header and the imports, please add a module docstring (delimited with /-! and -/) containing

a title of the file,
a summary of the contents (the main definitions and theorems, proof techniques, etc…)
notation that has been used in the file (if any)
references to the literature (if any)
In total, the module docstring should look something like this:

/-!

# Foos and bars

In this file we introduce `foo` and `bar`,
two main concepts in the theory of xyzzyology.

## Main results

- `exists_foo`: the main existence theorem of `foo`s.
- `bar_of_foo_of_baz`: a construction of a `bar`, given a `foo` and a `baz`.
  If this doc-string is longer than one line, subsequent lines should be indented by two spaces
  (as required by markdown syntax).
- `bar_eq`    : the main classification theorem of `bar`s.

## Notation

- `|_|` : The barrification operator, see `bar_of_foo`.

## References

See [Thales600BC] for the original account on Xyzzyology.
-/
New bibliography entries should be added to docs/references.bib.

See our documentation requirements for more suggestions and examples.

Structuring definitions and theorems
All declarations (e.g., def, lemma, theorem, class, structure, inductive, instance, etc.) and commands (e.g., variable, open, section, namespace, notation, etc.) are considered top-level and these words should appear flush-left in the document. In particular, opening a namespace or section does not result in indenting the contents of that namespace or section. (Note: within VS Code, hovering over any declaration such as def Foo ... will show the fully qualified name, like MyNamespace Foo if Foo is declared while the namespace MyNamespace is open.)

These guidelines hold for declarations starting with def, lemma and theorem. For "theorem statement", also read "type of a definition" and for "proof" also read "definition body".

Use spaces on both sides of ":", ":=" or infix operators. Put them before a line break rather than at the beginning of the next line.

In what follows, "indent" without an explicit indication of the amount means "indent by 2 additional spaces".

After stating the theorem, we indent the lines in the subsequent proof by 2 spaces.

open Nat
theorem nat_case {P : Nat → Prop} (n : Nat) (H1 : P 0) (H2 : ∀ m, P (succ m)) : P n :=
  Nat.recOn n H1 (fun m IH ↦ H2 m)
If the theorem statement requires multiple lines, indent the subsequent lines by 4 spaces. The proof is still indented only 2 spaces (not 6 = 4 + 2). When providing a proof in tactic mode, the by is placed on the line prior to the first tactic; however, by should not be placed on a line by itself. In practice this means you will often see := by at the end of a theorem statement.

import Mathlib.Data.Nat.Basic

theorem le_induction {P : Nat → Prop} {m}
    (h0 : P m) (h1 : ∀ n, m ≤ n → P n → P (n + 1)) :
    ∀ n, m ≤ n → P n := by
  apply Nat.le.rec
  · exact h0
  · exact h1_

def decreasingInduction {P : ℕ → Sort*} (h : ∀ n, P (n + 1) → P n) {m n : ℕ} (mn : m ≤ n)
    (hP : P n) : P m :=
  Nat.leRecOn mn (fun {k} ih hsk => ih <| h k hsk) (fun h => h) hP
When a proof term takes multiple arguments, it is sometimes clearer, and often necessary, to put some of the arguments on subsequent lines. In that case, indent each argument. This rule, i.e., indent an additional two spaces, applies more generally whenever a term spans multiple lines.

open Nat
axiom zero_or_succ (n : Nat) : n = zero ∨ n = succ (pred n)
theorem nat_discriminate {B : Prop} {n : Nat} (H1: n = 0 → B) (H2 : ∀ m, n = succ m → B) : B :=
  Or.elim (zero_or_succ n)
    (fun H3 : n = zero ↦ H1 H3)
    (fun H3 : n = succ (pred n) ↦ H2 (pred n) H3)
Don't orphan parentheses; keep them with their arguments.

Here is a longer example.

import Mathlib.Init.Data.List.Lemmas

open List
variable {T : Type}

theorem mem_split {x : T} {l : List T} : x ∈ l → ∃ s t : List T, l = s ++ (x :: t) :=
  List.recOn l
    (fun H : x ∈ [] ↦ False.elim ((mem_nil_iff_).mp H))
    (fun y l ↦
      fun IH : x ∈ l → ∃ s t : List T, l = s ++ (x :: t) ↦
      fun H : x ∈ y :: l ↦
      Or.elim (eq_or_mem_of_mem_cons H)
        (fun H1 : x = y ↦
          Exists.intro [] (Exists.intro l (by rw [H1]; rfl)))
        (fun H1 : x ∈ l ↦
          let ⟨s, (H2 : ∃ t : List T, l = s ++ (x :: t))⟩ := IH H1
          let ⟨t, (H3 : l = s ++ (x :: t))⟩ := H2
          have H4 : y  ::  l = (y :: s) ++ (x :: t) := by rw [H3]; rfl
          Exists.intro (y :: s) (Exists.intro t H4)))
A short declaration can be written on a single line:

open Nat
theorem succ_pos : ∀ n : Nat, 0 < succ n := zero_lt_succ

def square (x : Nat) : Nat := x * x
A have can be put on a single line when the justification is short.

example (n k : Nat) (h : n < k) : ... :=
  have h1 : n ≠ k := ne_of_lt h
  ...
When the justification is too long, you should put it on the next line, indented by an additional two spaces.

example (n k : Nat) (h : n < k) : ... :=
  have h1 : n ≠ k :=
    ne_of_lt h
  ...
When the justification of the have uses tactic mode, the by should be placed on the same line, regardless of whether the justification spans multiple lines.

example (n k : Nat) (h : n < k) : ... :=
  have h1 : n ≠ k := by apply ne_of_lt; exact h
  ...

example (n k : Nat) (h : n < k) : ... :=
  have h1 : n ≠ k := by
    apply ne_of_lt
    exact h
  ...
When the arguments themselves are long enough to require line breaks, use an additional indent for every line after the first, as in the following example:

import Mathlib.Data.Nat.Basic

theorem Nat.add_right_inj {n m k : Nat} : n + m = n + k → m = k :=
  Nat.recOn n
    (fun H : 0 + m = 0 + k ↦ calc
      m = 0 + m := Eq.symm (zero_add m)
      _ = 0 + k := H
      _= k     := zero_add _)
    (fun (n : Nat) (IH : n + m = n + k → m = k) (H : succ n + m = succ n + k) ↦
      have H2 : succ (n + m) = succ (n + k) := calc
        succ (n + m) = succ n + m   := Eq.symm (succ_add n m)
        _= succ n + k   := H
        _            = succ (n + k) := succ_add n k
      have H3 : n + m = n + k := succ.inj H2
      IH H3)
In a class or structure definition, fields are indented 2 spaces, and moreover each field should have a docstring, as in:

structure PrincipalSeg {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends r ↪r s where
  /-- The supremum of the principal segment -/
  top : β
  /-- The image of the order embedding is the set of elements `b` such that `s b top` -/
  down' : ∀ b, s b top ↔ ∃ a, toRelEmbedding a = b

class Module (R : Type u) (M : Type v) [Semiring R] [AddCommMonoid M] extends
    DistribMulAction R M where
  /-- Scalar multiplication distributes over addition from the right. -/
  protected add_smul : ∀ (r s : R) (x : M), (r + s) • x = r • x + s • x
  /-- Scalar multiplication by zero gives zero. -/
  protected zero_smul : ∀ x : M, (0 : R) • x = 0
When using a constructor taking several arguments in a definition, arguments line up, as in:

theorem Ordinal.sub_eq_zero_iff_le {a b : Ordinal} : a - b = 0 ↔ a ≤ b :=
  ⟨fun h => by simpa only [h, add_zero] using le_add_sub a b,
   fun h => by rwa [← Ordinal.le_zero, sub_le, add_zero]⟩
Instances
When providing terms of structures or instances of classes, the where syntax should be used to avoid the need for enclosing braces, as in:

instance instOrderBot : OrderBot ℕ where
  bot := 0
  bot_le := Nat.zero_le
If there is already an instance instBot, then one can write

instance instOrderBot : OrderBot ℕ where
  __ := instBot
  bot_le := Nat.zero_le
Hypotheses Left of Colon
Generally, having arguments to the left of the colon is preferred over having arguments in universal quantifiers or implications, if the proof starts by introducing these variables. For instance:

example (n : ℝ) (h : 1 < n) : 0 < n := by linarith
is preferred over

example (n : ℝ) : 1 < n → 0 < n := fun h ↦ by linarith
and

example (n : ℕ) : 0 ≤ n := Nat.zero_le n
is preferred over

example : ∀ (n : ℕ), 0 ≤ n := Nat.zero_le
Note that pattern-matching does not count as the proof starting by introducing variables. For example, the following is a valid use case of having a hypothesis right of the column:

lemma zero_le : ∀ n : ℕ, 0 ≤ n
  | 0 => le_rfl
  | n + 1 => add_nonneg (zero_le n) zero_le_one
Binders
Use a space after binders:

example : ∀ α : Type, ∀ x : α, ∃ y, y = x :=
  fun (α : Type) (x : α) ↦ Exists.intro x rfl
Anonymous functions
Lean has several nice syntax options for declaring anonymous functions. For very simple functions, one can use the centered dot as the function argument, as in (· ^ 2) to represent the squaring function. However, sometimes it is necessary to refer to the arguments by name (e.g., if they appear in multiple places in the function body). The Lean default for this is fun x => x *x, but the ↦ arrow (inserted with \mapsto) is also valid. In mathlib the pretty printer displays ↦, and we slightly prefer this in the source as well. The lambda notation λ x ↦ x* x, while syntactically valid, is disallowed in mathlib in favor of the fun keyword.

Calculations
There is some flexibility in how you write calculational proofs, although there are some rules enforced by the syntax requirements of calc itself. However, there are some general guidelines.

As with by, the calc keyword should be placed on the line prior to the start of the calculation, with the calculation indented. Whichever relations are involved (e.g., = or ≤) should be aligned from one line to the next. The underscores _ used as placeholders for terms indicating the continuation of the calculation should be left-justified.

As for the justifications, it is not necessary to align the := symbols, but it can be nice if the expressions are short enough. The terms on either side of the first relation can either go on one line or separate lines, which may be decided by the size of the expressions.

An example of adequate style which can more easily accommodate longer expressions is:

import Init.Data.List.Basic

open List

theorem reverse_reverse : ∀ (l : List α), reverse (reverse l) = l
  | []     => rfl
  | a :: l => calc
    reverse (reverse (a :: l))
      = reverse (reverse l ++ [a]) := by rw [reverse_cons]
    _= reverse [a] ++ reverse (reverse l) := reverse_append __
    _= reverse [a] ++ l := by rw [reverse_reverse l]
    _ = a :: l := rfl
The following style has the substantial advantage of having all lines be interchangeable, which is particularly useful when editing the proof in eg VSCode:

import Init.Data.List.Basic

open List

theorem reverse_reverse : ∀ (l : List α), reverse (reverse l) = l
  | []     => rfl
  | a :: l => calc
        reverse (reverse (a :: l))
    _ = reverse (reverse l ++ [a]) := by rw [reverse_cons]
    _ = reverse [a] ++ reverse (reverse l) := reverse_append_ _
    _ = reverse [a] ++ l := by rw [reverse_reverse l]
    _ = a :: l := rfl
If the expressions and proofs are relatively short, the following style is also an option:

import Init.Data.List.Basic

open List

theorem reverse_reverse : ∀ (l : List α), reverse (reverse l) = l
  | []     => rfl
  | a :: l => calc
    reverse (reverse (a :: l)) = reverse (reverse l ++ [a])         := by rw [reverse_cons]
    _= reverse [a] ++ reverse (reverse l) := reverse_append __
    _= reverse [a] ++ l                   := by rw [reverse_reverse l]
    _                          = a :: l                             := rfl
Tactic mode
As we have already mentioned, when opening a tactic block, by is placed at the end of the line preceding the start of the tactic block, but not on its own line. Everything within the tactic block is indented, as in:

theorem continuous_uncurry_of_discreteTopology [DiscreteTopology α] {f : α → β → γ}
    (hf : ∀ a, Continuous (f a)) : Continuous (uncurry f) := by
  apply continuous_iff_continuousAt.2
  rintro ⟨a, x⟩
  change map_ _≤_
  rw [nhds_prod_eq, nhds_discrete, Filter.map_pure_prod]
  exact (hf a).continuousAt
One can mix term mode and tactic mode, as in:

theorem Units.isUnit_units_mul {M : Type*} [Monoid M] (u : Mˣ) (a : M) :
    IsUnit (↑u* a) ↔ IsUnit a :=
  Iff.intro
    (fun ⟨v, hv⟩ => by
      have : IsUnit (↑u⁻¹ *(↑u* a)) := by exists u⁻¹ * v; rw [← hv, Units.val_mul]
      rwa [← mul_assoc, Units.inv_mul, one_mul] at this)
    u.isUnit.mul
When new goals arise as side conditions or steps, they are indented and preceded by a focusing dot · (inserted as \.); the dot is not indented.

import Mathlib.Algebra.Group.Basic

theorem exists_npow_eq_one_of_zpow_eq_one' [Group G] {n : ℤ} (hn : n ≠ 0) {x : G} (h : x ^ n = 1) :
    ∃ n : ℕ, 0 < n ∧ x ^ n = 1 := by
  cases n
  · simp only [Int.ofNat_eq_coe] at h
    rw [zpow_ofNat] at h
    refine ⟨_, Nat.pos_of_ne_zero fun n0 ↦ hn ?_, h⟩
    rw [n0]
    rfl
  · rw [zpow_negSucc, inv_eq_one] at h
    refine ⟨_ + 1, Nat.succ_pos_, h⟩
Certain tactics, such as refine, can create named subgoals which can be proven in whichever order is desired using case. This feature is also useful in aiding readability. However, it is not required to use this instead of the focusing dot (·).

example {p q : Prop} (h₁ : p → q) (h₂ : q → p) : p ↔ q := by
  refine ⟨?imp, ?converse⟩
  case converse => exact h₂
  case imp => exact h₁
Often t0 <;> t1 is used to execute t0 and then t1 on all new goals. Either write the tactics in one line, or indent the following tactic.

  cases x <;>
    simp [a, b, c, d]
For single line tactic proofs (or short tactic proofs embedded in a term), it is acceptable to use by tac1; tac2; tac3 with semicolons instead of a new line with indentation.

In general, you should put a single tactic invocation per line, unless you are closing a goal with a proof that fits entirely on a single line. Short sequences of tactics that correspond to a single mathematical idea can also be put on a single line, separated by semicolons as in cases bla; clear h or induction n; simp or rw [foo]; simp_rw [bar], but even in these scenarios, newlines are preferred.

example : ... := by
  by_cases h : x = 0
  · rw [h]; exact hzero ha
  · rw [h]
    have h' : ... := H ha
    simp_rw [h', hb]
    ...
Very short goals can be closed right away using swap or pick_goal if needed, to avoid additional indentation in the rest of the proof.

example : ... := by
  rw [h]
  swap; exact h'
  ...
We generally use a blank line to separate theorems and definitions, but this can be omitted, for example, to group together a number of short definitions, or to group together a definition and notation.

Squeezing simp calls
Unless performance is particularly poor or the proof breaks otherwise, terminal simp calls (a simp call is terminal if it closes the current goal or is only followed by flexible tactics such as ring, field_simp, aesop) should not be squeezed (replaced by the output of simp?).

There are two main reasons for this:

A squeezed simp call might be several lines longer than the corresponding unsqueezed one, and therefore drown the useful information of what key lemmas were added to the unsqueezed simp call to close the goal in a sea of basic simp lemmas.
A squeezed simp call refers to many lemmas by name, meaning that it will break when one such lemma gets renamed. Lemma renamings happen often enough for this to matter on a maintenance level.
Whitespace and delimiters
Lean is whitespace-sensitive, and in general we opt for a style which avoids delimiting code. For instance, when writing tactics, it is possible to write them as tac1; tac2; tac3, separated by ;, in order to override the default whitespace sensitivity. However, as mentioned above, we generally try to avoid this except in a few special cases.

Similarly, sometimes parentheses can be avoided by judicious use of the <| operator (or its cousin |>). Note: while $ is a synonym for <|, its use in mathlib is disallowed in favor of <| for consistency as well as because of the symmetry with |>. These operators have the effect of parenthesizing everything to the right of <| (note that ( is curved the same direction as <) or to the left of |> (and ) curves the same way as >).

A common example of the usage of |> occurs with dot notation when the term preceding the . is a function applied to some arguments. For instance, ((foo a).bar b).baz can be rewritten as foo a |>.bar b |>.baz

A common example of the usage of <| is when the user provides a term which is a function applied to multiple arguments whose last argument is a proof in tactic mode, especially one that spans multiple lines. In that case, it is natural to use <| by ... instead of (by ...), as in:

import Mathlib.Tactic

example {x y : ℝ} (hxy : x ≤ y) (h : ∀ ε > 0, y - ε ≤ x) : x = y :=
  le_antisymm hxy <| le_of_forall_pos_le_add <| by
    intro ε hε
    have := h ε hε
    linarith
When using the tactics rw or simp there should be a space after the left arrow ←. For instance rw [← add_comm a b] or simp [← and_or_left]. (There should also be a space between the tactic name and its arguments, as in rw [h].) This rule applies the do notation as well: do return (← f) + (← g)

Empty lines inside declarations
Empty lines inside declarations are discouraged and there is a linter that enforces that they are not present. This helps maintaining a uniform code style throughout all of mathlib.

You are however encouraged to add comments to your code: even a short sentence communicates much more than an empty line in the middle of a proof ever will!

Normal forms
Some statements are equivalent. For instance, there are several equivalent ways to require that a subset s of a type is nonempty. For another example, given a : α, the corresponding element of Option α can be equivalently written as Some a or (a : Option α). In general, we try to settle on one standard form, called the normal form, and use it both in statements and conclusions of theorems. In the above examples, this would be s.Nonempty (which gives access to dot notation) and (a : Option α). Often, simp lemmas will be registered to convert the other equivalent forms to the normal form.

There is a special case to this rule. In types with a bottom element, it is equivalent to require hlt : ⊥ < x or hne : x ≠ ⊥, and it is not clear which one would be better as a normal form since both have their pros and cons. An analogous situation occurs with hlt : x < ⊤ and hne : x ≠ ⊤ in types with a top element. Since it is very easy to convert from hlt to hne (by using hlt.ne or hlt.ne' depending on the direction we want) while the other conversion is more lengthy, we use hne in assumptions of theorems (as this is the easier assumption to check), and hlt in conclusions of theorems (as this is the more powerful result to use). A common usage of this rule is with naturals, where ⊥ = 0.

Comments
Use module doc delimiters /-! -/ to provide section headers and separators since these get incorporated into the auto-generated docs, and use /- -/ for more technical comments (e.g. TODOs and implementation notes) or for comments in proofs. Use -- for short or in-line comments.

Documentation strings for declarations are delimited with /-- -/. When a documentation string for a declaration spans multiple lines, do not indent subsequent lines.

See our documentation requirements for more suggestions and examples.

Expressions in error or trace messages
Inside all printed messages (such as, in linters, custom elaborators or other metaprogrammes), names and interpolated data should either be

inline and surrounded by backticks (e.g., m!"{foo}must have type{bar}"), or
on their own line and indented (via e.g. indentD)
The second style produces output like the following

Could not find model with corners for domain
  src
nor codomain
  tgt
of function
  f
Not all of mathlib may comply with this rule yet; that is a bug (and PRs fixing this are welcome).

Deprecation
Deleting, renaming, or changing declarations can cause downstreams projects that rely on these definitions to fail to compile. Any publicly exposed theorems and definitions that are being removed should be gracefully transitioned by keeping the old declaration with a @[deprecated] attribute. This warns downstream projects about the change and gives them the opportunity to adjust before the declarations are deleted. Renamed definitions should use a deprecated alias to the new name. Otherwise, when the deprecated definition does not have a direct replacement, the definition should be deprecated with a message, like so:

theorem new_name : ... := ...
@[deprecated (since := "YYYY-MM-DD")] alias old_name := new_name

@[deprecated "This theorem is deprecated in favor of using ... with ..." (since := "YYYY-MM-DD")]
theorem example_thm ...
The @[deprecated] attribute requires the deprecation date, and an alias to the new declaration or a string to explain how transition away from the old definition when a new version is no longer being provided.

The deprecate to command and scripts/add_deprecations.sh script can help generate alias definitions.

Deprecations for declarations with the to_additive attribute should ensure the deprecation is also properly tagged with to_additive, like so:

@[to_additive] theorem Group_bar {G} [Group G] {a : G} : a = a := rfl

-- Two deprecations required to include the `deprecated` tag on both the additive
-- and multiplicative versions
@[deprecated (since := "YYYY-MM-DD")] alias AddGroup_foo := AddGroup_bar
@[to_additive existing, deprecated (since := "YYYY-MM-DD")] alias Group_foo := Group_bar
We allow, but discourage, contributors from simultaneously renaming declarations X to Y and W to X. In this case, no deprecation attribute is required for X, but it is for W.

Named instances do not require deprecations. Deprecated declarations can be deleted after 6 months.


---


Mathlib naming conventions
This guide is written for Lean 4.

File names
.lean files in mathlib should generally be named in UpperCamelCase. A (very rare) exception are files named after some specifically lower-cased object, e.g. lp.lean for a file specifically about the space  (and not ). Such exceptions should be discussed on Zulip first.

General conventions
Capitalization
Unlike Lean 3, in which the convention was that all declarations used snake_case, in mathlib under Lean 4 we use a combination of snake_case, lowerCamelCase and UpperCamelCase according to the following naming scheme.

Terms of Props (e.g. proofs, theorem names) use snake_case.
Props and Types (or Sort) (inductive types, structures, classes) are in UpperCamelCase. There are some rare exceptions: some fields of structures are currently wrongly lower-cased (see the example for the class LT below).
Functions are named the same way as their return values (e.g. a function of type A → B → C is named as though it is a term of type C).
All other terms of Types (basically anything else) are in lowerCamelCase.
When something named with UpperCamelCase is part of something named with snake_case, it is referenced in lowerCamelCase.
Acronyms like LE are written upper-/lowercase as a group, depending on what the first character would be.
Rules 1-6 apply to fields of a structure or constructors of an inductive type in the same way.
There are some rare exceptions to preserve local naming symmetry: e.g., we use Ne rather than NE to follow the example of Eq; outParam has a Sort output but is not UpperCamelCase. Some other exceptions include intervals (Set.Icc, Set.Iic, etc.), where the I is capitalized despite the fact that it should be lowerCamelCase according to the convention. Any such exceptions should be discussed on Zulip.

Examples
-- follows rule 2
structure OneHom (M : Type _) (N : Type_) [One M] [One N] where
  toFun : M → N -- follows rule 4 via rule 3 and rule 7
  map_one' : toFun 1 = 1 -- follows rule 1 via rule 7

-- follows rule 2 via rule 3
class CoeIsOneHom [One M] [One N] : Prop where
  coe_one : (↑(1 : M) : N) = 1 -- follows rule 1 via rule 6

-- follows rule 1 via rule 3
theorem map_one [OneHomClass F M N] (f : F) : f 1 = 1 := sorry

-- follows rules 1 and 5
theorem MonoidHom.toOneHom_injective [MulOneClass M] [MulOneClass N] :
  Function.Injective (MonoidHom.toOneHom : (M →* N) → OneHom M N) := sorry
-- manual align is needed due to `lowerCamelCase` with several words inside `snake_case`
# align monoid_hom.to_one_hom_injective MonoidHom.toOneHom_injective

-- follows rule 2
class HPow (α : Type u) (β : Type v) (γ : Type w) where
  hPow : α → β → γ -- follows rule 3 via rule 6; note that rule 5 does not apply

-- follows rules 2 and 6
class LT (α : Type u) where
  lt : α → α → Prop -- this is an exception to rule 2

-- follows rules 2 (for `Semifield`) and 4 (for `toIsField`)
theorem Semifield.toIsField (R : Type u) [Semifield R] :
    IsField R -- follows rule 2

-- follows rules 1 and 6
theorem gt_iff_lt [LT α] {a b : α} : a > b ↔ b < a := sorry

-- follows rule 2; `Ne` is an exception to rule 6
class NeZero : Prop := sorry

-- follows rules 1 and 5
theorem neZero_iff {R : Type_} [Zero R] {n : R} : NeZero n ↔ n ≠ 0 := sorry
-- manual align is needed due to `lowerCamelCase` with several words inside `snake_case`
# align ne_zero_iff neZero_iff
Spelling
Declaration names use American English spelling. So e.g. we use factorization, Localization and FiberBundle and not factorisation, Localisation or FibreBundle. Contrast this with the rule for documentation, which is allowed to use other common English spellings.

Names of symbols
When translating the statements of theorems into words, the following dictionary is often used.

Logic
symbol shortcut name notes
∨ \or or 
∧ \and and 
→ \r of / imp the conclusion is stated first and the hypotheses are often omitted
↔ \iff iff sometimes omitted along with the right hand side of the iff
¬ \n not 
∃ \ex exists / bex bex stands for "bounded exists"
∀ \fo all / forall / ball ball stands for "bounded forall"
=  eq often omitted
≠ \ne ne 
∘ \o comp 
ball and bex are still used in Lean core, but should not be used in mathlib.

Set
symbol shortcut name notes
∈ \in mem 
∉ \notin notMem 
∪ \cup union 
∩ \cap inter 
⋃ \bigcup iUnion / biUnion i for "indexed", bi for "bounded indexed"
⋂ \bigcap iInter / biInter i for "indexed", bi for "bounded indexed"
⋃₀ \bigcup\0 sUnion s for "set"
⋂₀ \bigcap\0 sInter s for "set"
\ \\ sdiff 
ᶜ \^c compl 
{x | p x}  setOf 
{x}  singleton 
{x, y}  pair 
Algebra
symbol shortcut name notes
0  zero 
-  add 

-  neg / sub neg for the unary function, sub for the binary function

1  one 
-  mul 

^  pow 
/  div 
• \bu smul 
⁻¹ \-1 inv 
⅟ \frac1 invOf 
∣ \| dvd 
∑ \sum sum 
∏ \prod prod 
Lattices
symbol shortcut name notes
<  lt / gt 
≤ \le le / ge 
⊔ \sup sup a binary operator
⊓ \inf inf a binary operator
⨆ \supr iSup / biSup / ciSup c for "conditionally complete"
⨅ \infi iInf / biInf / ciInf c for "conditionally complete"
⊥ \bot bot 
⊤ \top top 
The symbols ≤ and < have a special naming convention. In mathlib, we almost always use ≤ and < instead of ≥ and >, so we can use both le/lt and ge/gt for naming ≤ and <. There are a few reasons to use ge/gt:

We use ge/gt if the arguments to ≤ or < appear in different orders. We use le/lt for the first occurrence of ≤/< in the theorem name, and then ge/gt indicates that the arguments are swapped.
We use ge/gt to match the argument order of another relation, such as = or ≠.
We use ge/gt to describe the ≤ or < relation with its arguments swapped.
We use ge/gt if the second argument to ≤ or < is 'more variable'.
-- follows rule 1
theorem lt_iff_le_not_ge [Preorder α] {a b : α} : a < b ↔ a ≤ b ∧ ¬b ≤ a := sorry
theorem not_le_of_gt [Preorder α] {a b : α} (h : a < b) : ¬b ≤ a := sorry
theorem LT.lt.not_ge [Preorder α] {a b : α} (h : a < b) : ¬b ≤ a := sorry

-- follows rule 2
theorem Eq.ge [Preorder α] {a b : α} (h : a = b) : b ≤ a := sorry
theorem ne_of_gt [Preorder α] {a b : α} (h : b < a) : a ≠ b := sorry

-- follows rule 3
theorem ge_trans [Preorder α] {a b : α} : b ≤ a → c ≤ b → c ≤ a := sorry

-- follows rule 4
theorem le_of_forall_gt [LinearOrder α] {a b : α} (H : ∀ (c : α), a < c → b < c) : b ≤ a := sorry
Dots
Dots are used for namespaces, and also for automatically generated names like recursors, eliminators and structure projections. They can also be introduced manually, for example, where projector notation is useful. Thus they are used in all of the following situations.

Note: since And is a (binary function into) Prop, it is UpperCamelCased according to the naming conventions, and so its namespace is And.*. This may seem at odds with the dictionary ∧ --> and but because upper camel case types get lower camel cased when they appear in names of theorems, the dictionary is still valid in general. The same applies to Or, Iff, Not, Eq, HEq, Ne, etc.

Intro, elim, and destruct rules for logical connectives, whether they are automatically generated or not:

And.intro
And.elim
And.left
And.right
Or.inl
Or.inr
Or.intro_left
Or.intro_right
Iff.intro
Iff.elim
Iff.mp
Iff.mpr
Not.intro
Not.elim
Eq.refl
Eq.rec
Eq.subst
HEq.refl
HEq.rec
HEq.subst
Exists.intro
Exists.elim
True.intro
False.elim
Places where projection notation is useful, for example:

And.symm
Or.symm
Or.resolve_left
Or.resolve_right
Eq.symm
Eq.trans
HEq.symm
HEq.trans
Iff.symm
Iff.refl
It is useful to use dot notation even for types which are not inductive types. For instance, we use:

LE.trans
LT.trans_le
LE.trans_lt
Axiomatic descriptions
Some theorems are described using axiomatic names, rather than describing their conclusions.

def (for unfolding a definition)
refl
irrefl
symm
trans
antisymm
asymm
congr
comm
assoc
left_comm
right_comm
mul_left_cancel
mul_right_cancel
inj (injective)
Variable conventions
u, v, w, ... for universes
α, β, γ, ... for generic types
a, b, c, ... for propositions
x, y, z, ... for elements of a generic type
h, h₁, ... for assumptions
p, q, r, ... for predicates and relations
s, t, ... for lists
s, t, ... for sets
m, n, k, ... for natural numbers
i, j, k, ... for integers
Types with a mathematical content are expressed with the usual mathematical notation, often with an upper case letter (G for a group, R for a ring, K or 𝕜 for a field, E for a vector space, ...). This convention is not followed in older files, where greek letters are used for all types. Pull requests renaming type variables in these files are welcome.

Identifiers and theorem names
We adopt the following naming guidelines to make it easier for users to guess the name of a theorem or find it using tab completion. Common "axiomatic" properties of an operation like conjunction or disjunction are put in a namespace that begins with the name of the operation:

import Mathlib.Logic.Basic

# check And.comm
# check Or.comm
In particular, this includes intro and elim operations for logical connectives, and properties of relations:

import Mathlib.Logic.Basic

# check And.intro
# check And.elim
# check Or.intro_left
# check Or.intro_right
# check Or.elim

# check Eq.refl
# check Eq.symm
# check Eq.trans
Note however we do not do this for axiomatic logical and arithmetic operations.

import Mathlib.Algebra.Group.Basic

# check and_assoc
# check mul_comm
# check mul_assoc
# check @mul_left_cancel  -- multiplication is left cancelative
For the most part, however, we rely on descriptive names. Often the name of theorem simply describes the conclusion:

import Mathlib.Algebra.Ring.Basic
open Nat
# check succ_ne_zero
# check mul_zero
# check mul_one
# check @sub_add_eq_add_sub
# check @le_iff_lt_or_eq
If only a prefix of the description is enough to convey the meaning, the name may be made even shorter:

import Mathlib.Algebra.Ring.Basic

# check @neg_neg
# check Nat.pred_succ
When an operation is written as infix, the theorem names follow suit. For example, we write neg_mul_neg rather than mul_neg_neg to describe the pattern -a * -b.

Sometimes, to disambiguate the name of theorem or better convey the intended reference, it is necessary to describe some of the hypotheses. The word "of" is used to separate these hypotheses:

import Mathlib.Algebra.Order.Monoid.Lemmas

open Nat

# check lt_of_succ_le
# check lt_of_not_ge
# check lt_of_le_of_ne
# check add_lt_add_of_lt_of_le
The hypotheses are listed in the order they appear, not reverse order. For example, the theorem A → B → C would be named C_of_A_of_B.

Sometimes abbreviations or alternative descriptions are easier to work with. For example, we use pos, neg, nonpos, nonneg rather than zero_lt, lt_zero, le_zero, and zero_le.

import Mathlib.Algebra.Order.Monoid.Lemmas
import Mathlib.Algebra.Order.Ring.Lemmas

open Nat

# check mul_pos
# check mul_nonpos_of_nonneg_of_nonpos
# check add_lt_of_lt_of_nonpos
# check add_lt_of_nonpos_of_lt
These conventions are not perfect. They cannot distinguish compound expressions up to associativity, or repeated occurrences in a pattern. For that, we make do as best we can. For example, a + b - b = a could be named either add_sub_self or add_sub_cancel.

Sometimes the word "left" or "right" is helpful to describe variants of a theorem.

import Mathlib.Algebra.Order.Monoid.Lemmas
import Mathlib.Algebra.Order.Ring.Lemmas

open Nat

# check add_le_add_left
# check add_le_add_right
# check le_of_mul_le_mul_left
# check le_of_mul_le_mul_right
When referring to a namespaced definition in a lemma name not in the same namespace, the definition should have its namespace removed. If the definition name is unambiguous without its namespace, it can be used as is. Else, the namespace is prepended back to it in lowerCamelCase. This is to ensure that _-separated strings in a lemma name correspond to a definition name or connective.

import Mathlib.Data.Int.Cast.Basic
import Mathlib.Data.Nat.Cast.Basic
import Mathlib.Topology.Constructions

# check Prod.fst
# check continuous_fst

# check Nat.cast
# check map_natCast
# check Int.cast_natCast
Naming of structural lemmas
We are trying to standardize certain naming patterns for structural lemmas.

Extensionality
A lemma of the form (∀ x, f x = g x) → f = g should be named .ext, and labelled with the @[ext] attribute. Often this type of lemma can be generated automatically by putting the @[ext] attribute on a structure. (However an automatically generated lemma will always be written in terms of the structure projections, and often there is a better statement, e.g. using coercions, that should be written by hand then marked with @[ext].)

A lemma of the form f = g ↔ ∀ x, f x = g x should be named .ext_iff.

Injectivity
Where possible, injectivity lemmas should be written in terms of an Function.Injective f conclusion which use the full word injective, typically as f_injective. The form injective_f still appears often in mathlib.

In addition to these, a variant should usually be provided as a bidirectional implication, e.g. as f x = f y ↔ x = y, which can be obtained from Function.Injective.eq_iff. Such lemmas should be named f_inj (although if they are in an appropriate namespace .inj is good too). Bidirectional injectivity lemmas are often good candidates for @[simp]. There are still many unidirectional implications named inj in mathlib, and it is reasonable to update and replace these as you come across them.

Note however that constructors for inductive types have automatically generated unidirectional implications, named .inj, and there is no intention to change this. When such an automatically generated lemma already exists, and a bidirectional lemma is needed, it may be named .inj_iff.

An injectivity lemma that uses "left" or "right" should refer to the argument that "changes". For example, a lemma with the statement a - b = a - c ↔ b = c could be called sub_right_inj.

Induction and recursion principles
Induction/recursion principles are ways to construct data or proofs for all elements of some type T, by providing ways to construct this data or proof in more constrained specific contexts. These principles should be phrased to accept a motive argument, which declares what property we are proving or what data we are constructing for all T. When the motive eliminates into Prop, it is an induction principle, and the name should contain induction. On the other hand, when the motive eliminates into Sort u or Type u, it is a recursive principle, and the name should contain rec instead.

Additionally, the name should contain on iff in the argument order, the value comes before the constructions.

The following table summarizes these naming conventions:

motive eliminates into: Prop Sort u or Type u
value first T.induction_on T.recOn
constructions first T.induction T.rec
Variation on these names are acceptable when necessary (e.g. for disambiguation).

Predicates as suffixes
Most predicates should be added as prefixes. Eg IsClosed (Icc a b) should be called isClosed_Icc, not Icc_isClosed.

Some widely used predicates don't follow this rule. Those are the predicates that are analogous to an atom already suffixed by the naming convention. Here is a non-exhaustive list:

We use _inj for f a = f b ↔ a = b, so we also use_injective for Injective f, _surjective for Surjective f,_bijective for Bijective f...
We use _mono for a ≤ b → f a ≤ f b and_anti for a ≤ b → f b ≤ f a, so we also use _monotone for Monotone f,_antitone for Antitone f, _strictMono for StrictMono f,_strictAnti for StrictAnti f, etc...
Predicates as suffixes can be preceded by either _left or_right to signify that a binary operation is left- or right-monotone. For example, mul_left_monotone : Monotone (· * a) proves left-monotonicity of multiplication and not monotonicity of left-multiplication.

Prop-valued classes
Mathlib has many Prop-valued classes and other definitions. For example "let  be a topological ring" is written variable (R : Type*) [Ring R] [TopologicalSpace R] [IsTopologicalRing R] and "let  be a group and let  be a normal subgroup" is written variable (G : Type*) [Group G] (H : Subgroup G) [Normal H]. Here IsTopologicalRing R and Normal H are not extra data, but are extra assumptions on data we have already.

Mathlib currently strives towards the following naming convention for these Prop-valued classes. If the class is a noun then its name should begin with Is. If however is it an adjective then its name does not need to begin with an Is. So for example IsNormal would be acceptable for the "normal subgroup" typeclass, but Normal is also fine; we might say "assume the subgroup H is normal" in informal language. However IsTopologicalRing is preferred for the "topological ring" typeclass, as we do not say "assume the ring R is topological" informally.

Unexpanded and expanded forms of functions
The multiplication of two functions f and g can be denoted equivalently as f *g or fun x ↦ f x* g x. These expressions are definitionally equal, but not syntactically (and they don't share the same key in indexing trees), which means that tools like rw, fun_prop or apply? will not use a theorem with one form on an expression with the other form. Therefore, it is sometimes convenient to have variants of the statements using the two forms. If one needs to distinguish between them, statements involving the first unexpanded form are written using just mul, while statements using the second expanded form should instead use fun_mul. If there is no need to disambiguate because a lemma is given using only the expanded form, the prefix fun_ is not required.

For instance, the fact that the multiplication of two continuous functions is continuous is

theorem Continuous.fun_mul (hf : Continuous f) (hg : Continuous g) : Continuous fun x ↦ f x * g x
and

theorem Continuous.mul (hf : Continuous f) (hg : Continuous g) : Continuous (f * g)
Both theorems deserve tagging with the fun_prop attribute.

The same goes for addition, subtraction, negation, powers and compositions of functions.

-----

Documentation style
All pull requests must meet the following documentation standards. See the doc-gen repo for information about the automatically generated doc pages.

You can preview the markdown processing of a GitHub page or pull request using the Lean doc preview page.

Header comment
Each mathlib file should start with:

a header comment with copyright information (see the recommendations in our style guidelines);
the list of imports (one on each line);
a module docstring containing general documentation, written using Markdown and LaTeX.
(See the example below.)

Headers use atx-style headers (with hash signs, no underlying dash). The open and close delimiters /-! and -/ should appear on their own lines.

The mandatory title of the file is a first level header. It is followed by a summary of the content of the file.

The other sections, with second level headers are (in this order):

Main definitions (optional, can be covered in the summary)
Main statements (optional, can be covered in the summary)
Notation (omitted only if no notation is introduced in this file)
Implementation notes (description of important design decisions or interface features, including use of type classes and simp canonical form for new definitions)
References (references to textbooks or papers, or Wikipedia pages)
Tags (a list of keywords that could be useful when doing text search in mathlib to find where something is covered)
References should refer to bibtex entries in the mathlib citations file. See the Citing other works section below.

The following code block is an example of a file header.

/-
Copyright (c) 2018 Robert Y. Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Y. Lewis
-/
module

public import Mathlib.Algebra.Order.AbsoluteValue.Basic
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!

# p-adic norm

This file defines the `p`-adic norm on `ℚ`.

The `p`-adic valuation on `ℚ` is the difference of the multiplicities of `p` in the numerator and
denominator of `q`. This function obeys the standard properties of a valuation, with the appropriate
assumptions on `p`.

The valuation induces a norm on `ℚ`. This norm is a nonarchimedean absolute value.
It takes values in {0} ∪ {1/p^k | k ∈ ℤ}.

## Implementation notes

Much, but not all, of this file assumes that `p` is prime. This assumption is inferred automatically
by taking `[Fact p.Prime]` as a type class argument.

## References

- [F. Q. Gouvêa, *p-adic numbers*][gouvea1997]
- [R. Y. Lewis, *A formal proof of Hensel's lemma over the p-adic integers*][lewis2019]
- <https://en.wikipedia.org/wiki/P-adic_number>

## Tags

p-adic, p adic, padic, norm, valuation
-/
Doc strings
Every definition and major theorem is required to have a doc string. (Doc strings on lemmas are also encouraged, particularly if the lemma has any mathematical content or might be useful in another file.) These are introduced using /-- and closed by -/ above the definition, with either newlines or single spaces between the markers and the text. Subsequent lines in a doc-string should not be indented. They can contain Markdown and LaTeX as well: see the next section. If a doc string is a complete sentence, then it should end in a period. Named theorems, such as the mean value theorem should be bold faced (i.e., with two asterisks before and after).

Doc strings should convey the mathematical meaning of the definition. They are allowed to lie slightly about the actual implementation. The following is a doc string example:

/-- If `q ≠ 0`, the `p`-adic norm of a rational `q` is `p ^ (-padicValRat p q)`.
If `q = 0`, the `p`-adic norm of `q` is `0`. -/
def padicNorm (p : ℕ) (q : ℚ) : ℚ :=
  if q = 0 then 0 else (p : ℚ) ^ (-padicValRat p q)
An example that is slightly lying but still describes the mathematical content would be:

/-- `padicValRat` defines the valuation of a rational `q` to be the valuation of `q.num` minus the
valuation of `q.den`. If `q = 0` or `p = 1`, then `padicValRat p q` defaults to `0`. -/
def padicValRat (p : ℕ) (q : ℚ) : ℤ :=
  padicValInt p q.num - padicValNat p q.den
The docBlame linter lists all definitions that do not have doc strings. The docBlameThm linter will lists theorems and lemmas that do not have doc strings.

To run only the docBlame linter, add the following to the end of your lean file:

# lint only docBlame
To run only the docBlame and docBlameThm linters, add the following to the end of your lean file:

# lint only docBlame docBlameThm
To run the all default linters, including docBlame, add the following to the end of your lean file:

# lint
To run the all default linters, including docBlame and run docBlameThm, add the following to the end of your lean file:

# lint docBlameThm
LaTeX and Markdown
We generally put references to Lean declarations or variables in between backticks. Writing the fully-qualified name (e.g. finset.card_pos instead of just card_pos) will turn the name into a link on our online docs.

Raw URLs should be enclosed in angle brackets <...> to ensure that they will be clickable online. (Some URLs, especially those with parentheses or other special symbols, may not be parsed correctly by the markdown renderer.)

When talking about mathematical symbols instead, it may be preferable to use LaTeX. LaTeX can be included in doc strings in three ways:

using single dollar signs $ ... $ to render math inline,
using double dollar signs $$ ... $$ to render math in "display mode", or
using environments \begin{*} ... \end{*} (without dollar signs).
These correspond to the MathJax settings of our online docs. The interaction between the Markdown and LaTeX there is similar to that on <https://math.stackexchange.com> and <https://mathoverflow.net>, so you can paste a doc string into an editing sandbox there to preview the final result. See also the math.stackexchange MathJax tutorial.

Sectioning comments
It is common to structure a file in sections, where each section contains related declarations. By describing the sections with module documentation /-! ... -/ at the beginning, these sections can be seen in the documentation.

While these sectioning comments will often correspond to section or namespace commands, this is not required. You can use sectioning comments inside of a section or namespace, and you can have multiple sections or namespaces following one sectioning comment.

Sectioning comments are for display and readability only. They have no semantic meaning.

Third-level headers ### should be used for titles inside sectioning comments.

If the comment is more than one line long, the delimiters /-! and -/ should appear on their own lines.

See Lean/Expr/Basic.lean for an example in practice.

namespace BinderInfo

/-! ### Declarations about `BinderInfo` -/

/-- The brackets corresponding to a given `BinderInfo`. -/
def brackets : BinderInfo → String × String
  | BinderInfo.implicit => ("{", "}")
  | BinderInfo.strictImplicit => ("{{", "}}")
  | BinderInfo.instImplicit => ("[", "]")
  | _ => ("(", ")")

end BinderInfo

namespace Name

/-! ### Declarations about `name` -/

/-- Find the largest prefix `n` of a `Name` such that `f n != none`, then replace this prefix
with the value of `f n`. -/
def mapPrefix (f : Name → Option Name) (n : Name) : Name := Id.run do
  if let some n' := f n then return n'
  match n with
  | anonymous => anonymous
  | str n' s => mkStr (mapPrefix f n') s
  | num n' i => mkNum (mapPrefix f n') i
Theories documentation
In addition to documentation living in Lean files, we have theories documentation where we give overviews spanning several Lean files, and more mathematical explanations in cases where formalization requires slightly exotic points of view, see for instance the topology documentation.

Citing other works
To cite papers and books in doc strings, the references should first be added to the BibTeX file: docs/references.bib. To normalize the file with bibtool, you can run:

bibtool --preserve.key.case=on --preserve.keys=on --print.use.tab=off --pass.comments=on -s -i docs/references.bib -o docs/references.bib
To ensure that your citations become links in the online docs, you can use either of the following two styles:

First, you may enclose the citation key used in docs/references.bib in square brackets:

The proof can be found in [Boole1854].
In the online docs, this will become something like:

The proof can be found in [Boo54]

(The key will change into an alpha style label and become a link to the References page of the docs.)

Alternatively, you can use custom text for the citation by putting text in square brackets ahead of the citation key:

See [Grundlagen der Geometrie][hilbert1999] for an alternative axiomatization.
See Grundlagen der Geometrie for an alternative axiomatization.

Note that you currently cannot use the closing square bracket ] symbol in the link text. So the following will not result in a working link:

We follow [Euclid's *Elements* [Prop. 1]][heath1956a].
We follow [Euclid's Elements [Prop. 1]][heath1956a].

Language
Documentation should be written in English. Any common spelling (e.g. British, American or Australian English) is acceptable. Pull requests should not be made that only change which of these spellings are used, but it is acceptable to change the spelling as part of a PR that substantially enhances the documentation. Contrast this with the rule for declaration names, which should use American English spelling.

Examples
The following files are maintained as examples of good documentation style:

Mathlib.NumberTheory.Padics.PadicNorm
Mathlib.Topology.Basic
Analysis.Calculus.ContDiff.Basic

