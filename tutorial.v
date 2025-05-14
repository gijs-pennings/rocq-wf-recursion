Require Import Arith.       (* .none *)
Require Import ArithRing.   (* .none *)
Require Import Lia.         (* .none *)

(*|

.. raw:: html

  <style>
    .highlight.coq { background-color: #eeeeec; }

    /* hide bubbles */
    .alectryon-io label.alectryon-input       { padding-right: 0; }
    .alectryon-io label.alectryon-input:after { display: none; }
  </style>

==============================
Well-founded recursion in Rocq
==============================

.. raw:: html

  <p style="text-align: center; font-style: oblique;">Gijs Pennings, May 2025</p>

Rocq requires that all functions terminate.
That is why, by default, only structurally recursive functions are allowed: functions that recur on structural subterms of the decreasing argument.
However, not all functions are structurally recursive.
A common solution is well-founded recursion, where arguments decrease with respect to a well-founded relation.
Several plugins support well-founded recursion, and in this tutorial we compare different methods through concrete examples.
This extends a paper by `Leroy (2024)`_.

Proving properties of functions defined using well-founded recursion requires well-founded induction. Hence, this technique is introduced in the `first section <Induction_>`__.
In the `next section <Well-founded recursion_>`__, we perform well-founded recursion using various methods on a simple example: Euclid's algorithm.
Then, in the `following section <Quicksort_>`__, we use our preferred method to implement and verify quicksort.
In the `last section <Rebalancing binary search trees_>`__, we consider an algorithm on trees that requires a more specialized well-founded relation.

This tutorial was built using `Alectryon`__.
To step through the proofs, use Ctrl and the arrow keys. For this purpose, the *floating* style (selectable from the top banner) offers the best readability.
The `source file`__ is also available.

__ https://github.com/cpitclaudel/alectryon
__ tutorial.v

.. We assume familiarity with basic data structures and algorithms.



Induction
=========

Before we delve into recursive functions, we will first introduce some advanced forms of induction.
We illustrate this with a toy problem: the sum of the first :math:`k` odd numbers is equal to :math:`k^2`. We compute this sum as follows.

|*)

Fixpoint sum_odd (k : nat) : nat :=
  match k with
  | 0 => 0
  | S k' => (2*k' + 1) + sum_odd k'
  end.

(*|

Refresher: (weak) induction
---------------------------

In Rocq, we carry out induction using the eponymous `induction` tactic. It behaves like `destruct`, which performs a case analysis by generating a subgoal for each constructor of the inductive type. In addition, `induction` also introduces induction hypotheses.
Specifically, it applies an *induction principle*, by default the one that was automatically generated when the inductive type was declared.
Recall that for `nat`, the default induction principle is:

|*)

Check nat_ind.  (* .unfold *)

(*|

In plain language, it states that if some predicate :math:`P` holds for :math:`0`, and if it holds for :math:`n+1` given that it holds for :math:`n`, then :math:`P` holds for all natural numbers.

Let's apply induction to a simple example.

|*)

Lemma sum_odd_eq_square : forall k, sum_odd k = k*k.
Proof.
  induction k.
  - trivial.
  - simpl. rewrite IHk. ring.
Qed.

(*|

The two bullets correspond to the two premises of the induction principle: the *base case* and *step case*, respectively. At `rewrite IHk`, we use the induction hypothesis.

Instead of `induction k`, we could also write `induction k using nat_ind`, specifying the induction principle explicitly. Actually, we can even apply it manually:

.. You may need to provide P explicitly.

|*)

Goal forall k, sum_odd k = k*k.
Proof.
  apply nat_ind.
  - trivial.
  - intros. simpl. rewrite H. ring.
Qed.

(*|

Strong induction
----------------

We can use other induction principles as well.
One option is *strong induction*.
Compared to 'weak' induction as used above, it employs a stronger hypothesis: we prove that :math:`P\ n` under the assumption that :math:`P\ m` for all :math:`m < n`. By contrast, weak induction essentially only assumes that :math:`P\ (n-1)`.

.. strong = complete = course-of-values

Strong induction on natural numbers is formalized by the following theorem.

|*)

Theorem strong_ind_nat :
  forall P : nat -> Prop,
    (forall n, (forall m, m < n -> P m) -> P n) ->
    forall n, P n.
Proof.
  intros.
  (* We generalize the goal to strengthen the hypothesis! *)
  enough (forall a b, b <= a -> P b).
  - apply H0 with n.
    reflexivity.
  - induction a;
    intros;
    apply H;
    intros.
    + lia.  (* contradiction *)
    + apply IHa.
      lia.
Qed.

(*|

Note that we can prove the strong induction principle using weak induction! (It is also possible and easy to prove the converse.)
This means that strong induction is exactly as powerful as weak induction, even if their names suggest otherwise; 'strong' only refers to the induction hypothesis.

.. Note strong induction does not require separate base cases.

We can again prove `sum_odd_eq_square`, now using our strong induction principle.
It is not necessary to use strong induction here, but it serves as an example of how to use an alternative induction principle.

|*)

Goal forall k, sum_odd k = k*k.
Proof.
  induction k using strong_ind_nat.
  destruct k.
  - trivial.
  - simpl. rewrite H; lia.
Qed.

(*|

Well-founded induction
----------------------

Fundamentally, strong induction works because the natural numbers are well-ordered, meaning that every set of natural numbers has a least element. Hence, every 'chain of reasoning' reaches a base case, typically 0.
By contrast, the integers (with the usual ordering) are not well-ordered: :math:`\mathbb Z` has no least element, so there is no starting point for reasoning. In fact, there is an infinite descending chain, namely -1, -2, -3, etc.

The idea of strong induction can be generalized to any type equipped with a *well-founded relation*, i.e., a relation with no infinite descending chains.
Equivalently, every element must be *accessible*: there is a finite path of smaller elements leading to a least element.
This form of induction is known as *well-founded induction*.

.. a.k.a. transfinite induction

We define the notions of accessibility and well-foundedness in line with the `standard library <Init.Wf_>`__:

|*)

Set Implicit Arguments.   (* .none *)
Module MyWf.              (* .none *)
Section WfInd.

Variable A : Type.
Variable R : A -> A -> Prop.

Inductive Acc (x : A) : Prop :=
  Acc_intro : (forall y, R y x -> Acc y) -> Acc x.

Definition well_founded : Prop := forall a, Acc a.

(*|

Now, we can state and prove the well-founded induction principle.

|*)

Theorem well_founded_ind :
  well_founded ->
  forall P : A -> Prop,
    (forall x, (forall y, R y x -> P y) -> P x) ->
    forall a, P a.
Proof.
  intros Hwf P H a.
  apply Acc_ind.
  - intros.
    apply H.
    assumption.
  - apply Hwf.
Qed.

(*|

Specifically, the above theorem yields the induction principle if we provide a proof of the well-foundedness of :math:`R`.
Instead of requiring that the whole relation is well-founded, we could also restrict our induction to the 'accessible part' of :math:`R`.

|*)

Theorem well_founded_ind_alt :
  forall P : A -> Prop,
    (forall x, (forall y, R y x -> P y) -> P x) ->
    forall a, Acc a -> P a.
Proof.
  intros P H a Ha.
  apply Acc_ind.
  - intros.
    apply H.
    assumption.
  - assumption.
Qed.

End WfInd.

(*|

Unfortunately, the above theorem cannot be directly used with the `induction` tactic. Therefore, we will always use `well_founded_ind`, which requires a proof of well-foundedness.
Let's prove the well-foundedness of the most fundamental relation: the standard ordering of natural numbers.

|*)

Theorem lt_wf : well_founded lt.
Proof.
  unfold well_founded.
  induction a using strong_ind_nat.
  constructor.
  assumption.
Qed.

Definition lt_wf_ind := well_founded_ind lt_wf.

(*|

We now have all the tools we need to apply well-founded induction on our toy problem.
Also note that `lt_wf_ind`, which is the well-founded induction principle specialized to natural numbers, is precisely equal to the strong induction principle as defined earlier.

|*)

Check lt_wf_ind.  (* .unfold *)

Goal forall k, sum_odd k = k*k.
Proof.
  induction k using lt_wf_ind.
  destruct k.
  - trivial.
  - simpl. rewrite H; lia.
Qed.

(*|

To conclude this section, we present a generalization of `lt_wf`:
for any type `A`, given a function `f` that maps elements of `A` to natural numbers, the relation that compares the images under `f` is well-founded.
As we will see `later <Implementation_>`__, this result is frequently useful in practice.

|*)

Section WfNat.

Variable A : Type.
Variable f : A -> nat.

Definition ltof (a b : A) := f a < f b.

Theorem well_founded_ltof : well_founded ltof.
Proof.
  intros.
  enough (forall n a, f a < n -> Acc ltof a).
  - unfold well_founded.
    intros.
    apply H with (S (f a)).
    auto.
  - induction n;
    intros.
    + lia.  (* contradiction *)
    + constructor.
      intros.
      apply IHn.
      unfold ltof in H0.
      lia.
Qed.

End WfNat.
End MyWf.                   (* .none *)
Unset Implicit Arguments.   (* .none *)

(*|

All the above results are available in the standard library (Init.Wf_ and Arith.Wf_nat_).
In the remainder of this tutorial, we will use the declarations from the standard library.

.. This means that, in particular, strong induction (as a special case of well-founded induction) is available through the standard library, which is perhaps not widely known.
.. https://github.com/rocq-prover/rocq/issues/5343
.. https://github.com/rocq-community/coq-tricks?tab=readme-ov-file#ltac

.. _Init.Wf:      https://rocq-prover.org/doc/V8.20.1/stdlib/Coq.Init.Wf.html
.. _Arith.Wf_nat: https://rocq-prover.org/doc/V8.20.1/stdlib/Coq.Arith.Wf_nat.html



Well-founded recursion
======================

In Rocq, functions on inductive types are generally defined using `Fixpoint`.
Such definitions must terminate.
To guarantee this, the definition must satisfy (syntactical) constraints on one of the arguments, called the *decreasing argument*.
Namely, recursive calls must operate on structural subterms of this argument.
For example, a function on natural numbers may recur on the predecessor, and a function on lists may recur on the tail.

However, not all functions have this shape.
A simple counterexample is Euclid's algorithm for computing the greatest common divisor.
The following definition is not allowed in Rocq, since it is not structurally recursive. `[†]`_

.. _naive_gcd:

|*)

Fail Fixpoint gcd (a b : nat) : nat :=  (* .fails *)
  match b with
  | 0 => a
  | _ => gcd b (a mod b)
  end.

(*|

This function does terminate, of course, since the second argument strictly decreases each recursive call.
Formally, `<` is a well-founded relation on `nat` (as proven in `Well-founded induction`_), so only a finite chain of recursive calls is required.
Because it relies on well-foundedness, we refer to this method of defining recursive functions as *well-founded recursion*.

Unfortunately, Rocq cannot automatically infer the above reasoning, so we must explicitly specify and prove why the function terminates.
In this section we will compare different methods to perform well-founded recursion, using Euclid's algorithm as a running example.
This is based on a paper by `Leroy (2024)`_, which uses the same example.
Specifically, we will consider `Function`__, `Equations`__, `Program Fixpoint`__, and lastly the method proposed by Leroy, which we refer to as *Acc-recursion*.

__ https://rocq-prover.org/doc/V8.20.1/refman/using/libraries/funind.html
__ https://mattam82.github.io/Coq-Equations
__ https://rocq-prover.org/doc/V8.20.1/refman/addendum/program.html#program-fixpoint

.. _Leroy's criteria:

We will evaluate each method based on a number of criteria, similarly to Leroy:

1. Legibility of definitions.
2. Legibility of extracted code.
3. Ease of proving properties.
4. No axioms used.

.. raw:: html

  <small>

.. _[†]:

† Actually, if we define the second case as `S b' => gcd (S b') (a mod (S b'))`, the definition is accepted as structurally recursive!
This is because `a mod (S b')` simplifies to a subtraction, which 'preserves being a subterm' according to the `standard library`__.
Hence, it is not necessary to use well-founded recursion to implement Euclid's algorithm, but it functions as an uncomplicated example for our purposes.

__ https://rocq-prover.org/doc/V8.20.1/stdlib/Coq.Init.Nat.html#gcd

.. raw:: html

  </small>


Preparation
-----------

Before implementing and verifying Euclid's algorithm, we need a formal definition of the greatest common divisor.
We will also prove some properties. It is best to derive them from the definition, rather than the various implementations. This enables reuse and avoids dependence on specialized concepts like `Acc`.

The *greatest common divisor* (GCD) of two integers `a`, `b` is the largest integer `x` that divides both `a` and `b`.
Equivalently, `x` is a common divisor (CD) of `a` and `b`, and every common divisor of `a` and `b` also divides `x`.
We use `Nat.divide` from the standard library, which already provides a range of helpful lemmas.

|*)

Definition is_cd (a b x : nat) : Prop :=
  Nat.divide x a /\ Nat.divide x b.

Definition is_gcd (a b x : nat) : Prop :=
  is_cd a b x /\ forall y, is_cd a b y -> Nat.divide y x.

(*|

.. We write `Nat.divide y x` instead of the more intuitive `y <= x`, since it handles zeros more neatly.

First, let's prove some corner cases. These correspond to the base case of the algorithm.

|*)

Lemma is_cd_0 : forall x, is_cd x 0 x.
Proof.
  split.
  - reflexivity.
  - apply Nat.divide_0_r.
Qed.

Lemma is_gcd_0 : forall x, is_gcd x 0 x.
Proof.
  firstorder using is_cd_0.
Qed.

(*|

Next, we essentially prove the step case of Euclid's algorithm: `gcd(a, b)` is equal to `gcd(b, a mod b)`.
To do this, it is useful to prove some identities involving division and modulo.

|*)

Lemma divide_mod_1 : forall a b x,
  Nat.divide x a -> Nat.divide x b -> Nat.divide x (a mod b).
Proof.
  intros a b x H1 H2.
  destruct H1 as [A HA].
  destruct H2 as [B HB].
  exists (A - B * (a/b)).
  pose proof (Nat.div_mod_eq a b).
  rewrite Nat.mul_sub_distr_r.
  lia.
Qed.

Lemma divide_mod_2 : forall a b x,
  Nat.divide x (a mod b) -> Nat.divide x b -> Nat.divide x a.
Proof.
  intros a b x H1 H2.
  destruct H1 as [A HA].
  destruct H2 as [B HB].
  exists (A + B * (a/b)).
  pose proof (Nat.div_mod_eq a b).
  lia.
Qed.

Lemma is_cd_step : forall a b x,
  is_cd a b x -> is_cd b (a mod b) x.
Proof.
  split.
  2: apply divide_mod_1.
  all: firstorder.
Qed.

Lemma is_cd_step_rev : forall a b x,
  is_cd b (a mod b) x -> is_cd a b x.
Proof.
  split.
  1: apply divide_mod_2 with b.
  all: firstorder.
Qed.

Lemma is_gcd_step_rev : forall a b x,
  is_gcd b (a mod b) x -> is_gcd a b x.
Proof.
  (* exercise *)
Admitted.

(*|

Function
--------

Now, we are ready to implement `gcd`.
Our first method of choice is the functional induction plugin.
Its main command, `Function`, which behaves like `Fixpoint`, allows us to perform well-founded recursion using the `{wf R x}` annotation.
Here, `x` should be the decreasing argument, and `R` a well-founded ordering relation on the type of `x`, such that `x` decreases every recursive call.
In the case of `gcd`, the decreasing argument is `b`, and the relation is simply `lt`.

|*)

Require Import FunInd.  (* .no-messages *)
Require Import Recdef.

Function gcd_1 (a b : nat) {wf lt b} : nat :=
  match b with
  | 0 => a
  | _ => gcd_1 b (a mod b)
  end.
(* It remains to prove some obligations... *)
Proof.
  - auto using Nat.mod_upper_bound.
  - apply lt_wf.
Defined.

(*|

Unlike `Fixpoint`, after the definition, we are left with some proof obligations. We need to prove that:

* `b` is decreasing in each recursive call;
* the relation `lt` is well-founded.

In this case, instead of `{wf lt b}`, we could have used the annotation `{measure id b}`.
This uses the idea of `well_founded_ltof` as discussed earlier: it asserts that `id b` decreases with each recursive call. For our purposes, `id` suffices, though any mapping from the type of `b` to `nat` is allowed.
With `measure`, only the first obligation remains, since it is already known that `lt` is well-founded.

Note that we finish the obligations with `Defined` instead of `Qed`.
This makes the proof term transparent, enabling computation.
Try it yourself: with `Qed` instead of `Defined`, the following would not output 6.

|*)

Compute gcd_1 12 18.  (* .unfold *)

(*|

Next, we check the extracted code (OCaml), which looks clean.

|*)

Extraction gcd_1.  (* .unfold *)

(*|

Lastly, we will prove the correctness of `gcd_1`.
Importantly, if we would use `induction b`, we would get stuck.
Instead, we should use the custom tactic `functional induction`, which introduces a more relevant induction hypothesis.

|*)

Lemma gcd_1_ok : forall a b, is_gcd a b (gcd_1 a b).
Proof.
  intros.
  functional induction (gcd_1 a b).
  - apply is_gcd_0.
  - apply is_gcd_step_rev.
    assumption.
Qed.

(*|

After our preparation in the previous section, the proof is simple.
Since `is_gcd` characterizes the GCD, any further properties we want to prove can start from `is_gcd` instead of the implementation. (For example, as an exercise, try to prove that `gcd_1` is associative without `functional induction`.) This means that criterion 3 is satisfied.
Looking at the definition and extracted code, criteria 1 and 2 are also met.
Lastly, since we used no axioms, criterion 4 is also fulfilled.

There is one problem with `Function`: it is considered 'legacy functionality'.
Users are recommended to use the Equations plugin instead. That is the method we will look at next.


Equations
---------

The Equations plugin by `Sozeau and Mangin (2019)`_ boasts many features, including a different syntax for function definitions, but we will focus on well-founded recursion.
As with `Function`, an `Equations` definition supports a `wf x R` annotation to enable well-founded recursion. (Note that the arguments are swapped!)

.. Actually, in this case, we can even omit `lt`.

|*)

From Equations Require Import Equations.  (* .no-messages *)

Equations gcd_2 (a b : nat) : nat by wf b lt :=
  gcd_2 x 0 := x;
  gcd_2 x y := gcd_2 y (x mod y).
Next Obligation.
  lia.
Qed.

(*|

Again, a proof obligation was generated (corresponding to the first obligation of `gcd_1`).
The goal may look strange at first, but it is merely the (simplified) definition of `Nat.modulo`.
In contrast to `gcd_1`, even if the obligation is opaque, computation is possible:

.. However, if we were to use `Eval compute in`, we would need `Set Equations Transparent.`!

|*)

Compute gcd_2 12 18.  (* .unfold *)

(*|

It has been smooth sailing so far, but the extracted code is unfortunately not very readable.
The issue seems to be that the function is internally uncurried, and the destructuring carries over into the extracted code.

|*)

Extraction gcd_2.  (* .unfold *)

(*|

It remains to prove the correctness.
Similarly to the functional induction plugin, Equations offers a custom `funelim` tactic.
It performs a case analysis according to the function's definition, abstracting away the underlying well-founded induction. This allows for succinct proofs.

|*)

Lemma gcd_2_ok : forall a b, is_gcd a b (gcd_2 a b).
Proof.
  intros.
  funelim (gcd_2 a b).
  - apply is_gcd_0.
  - apply is_gcd_step_rev.
    assumption.
Qed.

(*|

In summary, apart from the legibility of the extracted code (#2), the Equations plugin fulfills all criteria.


Program Fixpoint
----------------

`Fixpoint` can be prefixed with `Program`, enabling 'program mode'.
Then, as with `Function`, it supports well-founded recursion through `{wf R x}` annotations.

.. or `measure`

|*)

Require Import Program.

Program Fixpoint gcd_3 (a b : nat) {wf lt b} : nat :=
  match b with
  | 0 => a
  | _ => gcd_3 b (a mod b)
  end.
Next Obligation.
  auto using Nat.mod_upper_bound.
Qed.

(*|

The extracted code (omitted) is cluttered, since proof obligations and dependent wrappers bleed into it, but there is a more pressing issue.
Whereas `Equations` automatically provides *reduction lemmas* (such as `gcd_2_equation_1`) and an elimination principle (`gcd_2_elim`), `Program Fixpoint` is much more bare-bones.

.. boilerplate-heavy, artificially verbose, non-idiomatic

|*)

Check gcd_2_equation_1.  (* generated by Equations *) (* .unfold *)

(*|

To verify `gcd_3`, we need an analogous lemma, but proving it is not easy.
Since `gcd_3` is defined using the `Fix` combinator, `simpl` is unable to unfold `gcd_3 a 0`.
Apart from a `Stack Overflow post`__, little documentation is available.
The key is the `fix_sub_eq` lemma. It is important to note that it carries a (hidden) functional extensionality hypothesis, i.e., it is axiomatic!

__ https://stackoverflow.com/q/36329256

|*)

Fact gcd_3_equation_1 : forall a, gcd_3 a 0 = a.
Proof.
  intros.
  unfold gcd_3.
  unfold gcd_3_func.
  rewrite fix_sub_eq.
  - reflexivity.
  - intros.
    destruct x as [x y].
    simpl.
    destruct y.
    + reflexivity.
    + apply H.
Qed.

Fact gcd_3_equation_2 : forall a b,
  gcd_3 a (S b) = gcd_3 (S b) (a mod S b).
Proof.
  (* identical to `gcd_3_equation_1`; omitted *)
Admitted.

(*|

Using these reduction lemmas we can prove the correctness of `gcd_3`.
Even now the proof is less elegant than with Equations.

|*)

Lemma gcd_3_ok : forall b a, is_gcd a b (gcd_3 a b).
Proof.
  induction b using (well_founded_induction lt_wf).
  (* Crucially, the IH is general over `a`. *)
  intros.
  destruct b.
  - rewrite gcd_3_equation_1.
    apply is_gcd_0.
  - rewrite gcd_3_equation_2.
    apply is_gcd_step_rev.
    apply H.
    auto using Nat.mod_upper_bound.
Qed.

(*|

In conclusion, while the definition is legible, `Program Fixpoint` fails to meet all other criteria.
It is cumbersome to work with and hence not recommended.


Acc-recursion
-------------

Finally, we study the method proposed by Leroy, which we call Acc-recursion.
They propose to 'go back to the basics' and perform structural recursion on the accessibility of the decreasing argument.
To understand what this means, let's look at a concrete example:

|*)

Fail Fixpoint gcd_rec (a b : nat) (ACC : Acc lt b)
    {struct ACC} : nat :=
  match b with
  | 0 => a
  | _ => gcd_rec b (a mod b) _
  end.

(*|

Compared to the `naive definition <naive_gcd_>`__, we added an auxiliary argument: the accessibility proof `ACC` of `b`.
With the annotation `{struct ACC}`, we indicate that we want to perform structural recursion on `ACC`.
In the recursive call, it remains to fill the hole `_` with a (transparent) proof of accessibility of `a mod b`. This proof must be a structural subterm of `ACC`.
Leroy suggests to use `Acc_inv` for this.

|*)

Check Acc_inv.  (* .unfold *)

(*|

This is the inversion principle for `Acc`, provided by the standard library.
Since `Acc` has a single constructor, `Acc lt b` only holds if `Acc lt x` for all `x` smaller than `b`. This means we can extract an accessibility proof of `a mod b` from `Acc lt b`.

|*)

Fail Fixpoint gcd_rec (a b : nat) (ACC : Acc lt b)
    {struct ACC} : nat :=
  match b with
  | 0 => a
  | _ => gcd_rec b (a mod b) (Acc_inv ACC _)
  end.

(*|

Now, the hole requires a proof of `a mod b < b` (and it can be opaque).
You can provide an explicit proof term, but it is easier to generate an obligation using `Program`:

|*)

Program Fixpoint gcd_rec (a b : nat) (ACC : Acc lt b)
    {struct ACC} : nat :=
  match b with
  | 0 => a
  | _ => gcd_rec b (a mod b) (Acc_inv ACC _)
  end.
Next Obligation.
  auto using Nat.mod_upper_bound.
Qed.

(*|

.. We have successfully implemented Euclid's algorithm without any plugins!

Note that we solely use `Program` to generate obligations for the holes!
This is entirely different from the previous section, where we used it to perform well-founded recursion. (Here, we simply perform structural recursion.)

If we extract this definition, the resulting code is flawless, since `ACC` is in `Prop`, so it is discarded during extraction.

.. 'The accessibility predicate is defined to be non-informative'

|*)

Extraction gcd_rec.  (* .unfold *)

(*|

Next, we want to prove the correctness.
You might be inclined to perform induction on `ACC`, but Leroy warns this is not effective.
Instead, we perform well-founded induction on `b`, the decreasing argument.
Then, in order to unfold `gcd_rec`, we destruct `ACC`.

.. Actually, `b` is not the decreasing argument anymore (`ACC` is), but we still refer to it as such.

|*)

Lemma gcd_rec_ok : forall b a ACC, is_gcd a b (gcd_rec a b ACC).
Proof.
  induction b using (well_founded_induction lt_wf).
  destruct ACC.
  simpl.
  destruct b.
  - apply is_gcd_0.
  - apply is_gcd_step_rev.
    apply H.
    auto using Nat.mod_upper_bound.
Qed.

(*|

The order in which we quantify over the variables is important: the induction hypothesis should be general over both `a` and `ACC`.
For the same reason, we should not `intros` before `induction`.

Even for a simple function like Euclid's algorithm, the accessibility argument in the goal becomes distractingly verbose.
A useful trick: in `VsRocq`__ for VS Code, you can Alt+Click to hide this argument in the goal. It is safe to ignore, since the induction hypothesis abstracts over `ACC`. Other editors might have similar functionality.

__ https://github.com/rocq-prover/vsrocq

Optionally, we can define a neat 'wrapper' that provides the initial accessibility proof.

|*)

Definition gcd_4 (a b : nat) : nat := gcd_rec a b (lt_wf b).

Lemma gcd_4_ok : forall a b, is_gcd a b (gcd_4 a b).
Proof.
  intros.
  apply gcd_rec_ok.
Qed.

(*|

To conclude, let's assess the criteria.
While the extracted code is pristine (#2), our definition is less readable due to the auxiliary accessibility arguments (#1).
Proving correctness is somewhat more involved than, for example, using Equations, but nevertheless every step is easy to follow (#3).
Lastly, no axioms were required (#4).


Discussion
----------

In the table below, we summarize our experience with the four methods discussed in the preceding sections.
Here ✅, 🟡, and ❌ denote 'good', 'adequate', and 'bad', respectively.
This mostly agrees with Leroy, except that Acc-recursion is graded 🟡 on the first criterion.

============================ ======== ========= ================ =============
Criteria                     Function Equations Program Fixpoint Acc-recursion
============================ ======== ========= ================ =============
Legibility of definitions    ✅        ✅         ✅                🟡
Legibility of extracted code ✅        ❌         ❌                ✅
Ease of proving properties   ✅        ✅         ❌                ✅
No axioms used               ✅        ✅         ❌                ✅
============================ ======== ========= ================ =============

Leroy mentions two more approaches to perform well-founded recursion: tactics in proof mode and the `Fix` combinator.
We did not study these since they are clearly inferior to the other four methods.
Both approaches are lower-level than, for example, Equations, and hence are generally harder to work with. Specifically, both methods suffer from poorly legible definitions and `Fix`, like `Program Fixpoint`, requires axioms.

.. http://adam.chlipala.net/cpdt/html/Cpdt.GeneralRec.html

In addition to the four criteria in the table, we could consider a fifth: *understandability*.
Function and Equations are powerful plugins with a user-friendly interface, but it can be difficult to grasp what happens inside the 'black box'.
On the other hand, Acc-recursion relies on more basic principles, making it easy to understand. The latter is especially valuable in educational contexts.

Our recommendations are as follows.
If code extraction is not a requirement, use Equations. It functions similarly to Function, but is more modern.
Otherwise, Acc-recursion offers more transparency and control.

In the remainder of this tutorial, we will apply Acc-recursion to two other problems: quicksort (on lists) and a rebalancing algorithm (on trees).
These will serve as examples of how the method performs on more complicated inductive data structures.

.. Leroy presents two more examples as well: Tarski iteration and depth-first search on acyclic graphs.

.. Leroy assumes b <= a, but this is not necessary and we simplified this.



Quicksort
=========

We have seen how Acc-recursion can be used to implement Euclid's algorithm.
Now, we want to evaluate how well this method performs on more complex algorithms and data structures.
To this end, we will study a widely used algorithm on lists: *quicksort*.
For simplicity, we restrict ourselves to lists on natural numbers.
Naively, we might implement quicksort as follows.

.. _naive_qs:

|*)

Require Import List.    (* .none *)
Import ListNotations.   (* .none *)
Definition geb (x y : nat) := Nat.leb y x.

Fail Fixpoint quicksort (l : list nat) :=  (* .fails *)
  match l with
  | [] => []
  | x :: xs =>
      let L := filter (    geb x) xs in
      let R := filter (Nat.ltb x) xs in
      quicksort L ++ x :: quicksort R
  end.

(*|

However, `L` and `R` are not structural subterms of `l`, so this definition is rejected.
Nevertheless, `quicksort` terminates, since `L` and `R` are shorter than `l` as they never contain the pivot `x`. We will formalize this using well-founded recursion.

In contrast to Euclid's algorithm, which we implemented using Acc-recursion without much groundwork, we will now systematically derive a definition of quicksort.
To this end, the next section presents a practical, general guide on using Acc-recursion.


Guide to Acc-recursion
----------------------

We have applied Acc-recursion to one concrete problem so far, but it is helpful to distill the method into a *design pattern* applicable to arbitrary algorithms.
That is the goal of this section.

For `gcd`, we started with the naive definition and gradually added accessibility arguments. This is a practical approach in general.
However, in hindsight, we can improve our approach to managing the obligations.
You may have noticed that we often wrote `auto using Nat.mod_upper_bound`, not only to prove the obligations, but also after applying the induction hypothesis. This is no coincidence.
Since these obligations are typically simple, we suggest to prove them as separate lemmas and add them to a hint database.
Then, after applying the induction hypothesis, proofs can simply be finished with `auto`. Furthermore, obligations will be automatically solved by the `default solving tactic`__.

__ https://rocq-prover.org/doc/V8.20.1/refman/addendum/program.html#coq:cmd.Obligation-Tactic

Now, combining our approach for `gcd` and the above insight, we suggest the following steps to define a well-founded recursive function:

1. Write the naive `Fixpoint` definition.
2. Determine the decreasing argument, say `x`, and the relation, say `R`, such that `x` decreases according to `R` each recursive call.
3. Add an auxiliary argument `ACC : Acc R x` to the function signature, and add an argument `Acc_inv ACC _` to each recursive call. Also, change `Fixpoint` into `Program Fixpoint`.
4. Now, obligations should be generated. For each goal, create a new lemma. Prove these lemmas and add them to a hint database. It is easiest if you add them to `core`. Otherwise, you will have to customize the obligation solving tactic.
5. Then, all obligations should be automatically solved. Check that your function definition is accepted.

In the end, we have a valid definition that is structurally recursive in the `ACC` argument.
You can make this explicit using a `{struct ACC}` annotation, but this is not necessary since it can be determined automatically.

Next, to prove properties about our new definition, we will perform well-founded induction on the decreasing argument `x`. This requires the well-founded induction principle for `R`, which in turn requires a proof that `R` is well-founded.
If `R` is a relation that compares elements via some mapping `f : A -> nat`, a proof of well-foundedness is provided by the theorem `well_founded_ltof`. Otherwise, you need to prove it manually.

To prove a property, proceed as follows:

1. State the lemma as you would for the naive definition.
2. Add the quantifier `forall ACC` and add the `ACC` argument where necessary. Make sure `ACC` is the last variable in the quantifier list.
3. Start the proof with `induction x using (well_founded_induction <proof>)`. That is, perform well-founded induction on the decreasing argument `x` using the well-foundedness of `R`.
4. Next, `destruct ACC`. Now, with `simpl`, you can unroll your function.
5. Proceed as normal. Since your function likely matches on the decreasing argument, the logical next step is `destruct x`.

At some point in the proof, you will apply the induction hypothesis.
Then, you must show that the argument it is applied to is smaller than the original `x` under `R`. If your proof follows the structure of the definition, the proof goal will precisely match an obligation. Since we added these as hints, `auto` can solve them directly.

In the remainder of this section, we will carry out these steps to implement and prove the correctness of quicksort.
Before reading on, it is highly instructive to fix the naive definition of quicksort yourself using this guide, and prove a simple property about it.


Implementation
--------------

Now, we will formulate a well-founded recursive definition of quicksort.
Since we already provided a `naive definition <naive_qs_>`__, we move on to step 2.
The list becomes shorter every recursive call, so the relation should compare lists by length.
It can be conveniently defined through `ltof` (see `Well-founded induction`_).

|*)

Definition lt_len     := ltof              _ (@length nat).
Definition lt_len_wf  := well_founded_ltof _ (@length nat).
Definition wf_ind_len := well_founded_induction lt_len_wf.

(*|

We also immediately derive the well-foundedness (`lt_len_wf`) and the induction principle (`wf_ind_len`) for later use.
Note that `@` makes all implicit arguments explicit, allowing us to specialize `lt_len` to lists of natural numbers.

Next, we skip to step 4. You are encouraged to carry out step 3 yourself, and check if `qs_oblig` is sensible.
The proof obligation generated by `Program Fixpoint` will actually be in terms of `lt_len`, but we state `qs_oblig` in its 'unfolded' form. This makes the hint applicable even if the goal is already (partially) unfolded.
To ensure the obligations are still solved automatically, we allow `lt_len` and `ltof` to be unfolded by `auto`.

|*)

Fact qs_oblig : forall f (x : nat) xs,
  length (filter f xs) < length (x :: xs).
Proof.
  intros.
  simpl.
  apply Nat.lt_succ_r.
  apply filter_length_le.
Qed.

Hint Unfold lt_len ltof : core.
Hint Resolve qs_oblig : core.

(*|

Then, combining steps 3 and 5, we see that all obligations of the definition with auxiliary arguments are solved automatically:

|*)

Program Fixpoint qs_rec (l : list nat) (ACC : Acc lt_len l) :=
  match l with
  | [] => []
  | x :: xs =>
      let L := filter (    geb x) xs in
      let R := filter (Nat.ltb x) xs in
      qs_rec L (Acc_inv ACC _) ++ x :: qs_rec R (Acc_inv ACC _)
  end.

(*|

Now, we are ready to prove that `qs_rec` is correct.
The correctness comprises two aspects: the resulting list is sorted and contains the same elements.
It is interesting and non-trivial to formalize these notions, but we take a practical approach and use the definitions of `sortedness`__ and `permutations`__ from the standard library.

__ https://rocq-prover.org/doc/V8.20.1/stdlib/Coq.Sorting.Permutation.html
__ https://rocq-prover.org/doc/V8.20.1/stdlib/Coq.Sorting.Sorted.html


Permutation
-----------

First, we will show that a quicksorted list is a permutation of the original list.
For the naive definition, the lemma would be stated as follows (step 1).

|*)

Require Import Permutation.
Print Permutation.

Fail Lemma qs_Permutation : forall l, Permutation l (qs_rec l).

(*|

Of course, `qs_rec` takes an `ACC` argument, so we add it to the quantifier list (step 2).
Now, try to prove this revised lemma. The setup for well-founded induction is already given. A helper lemma, `partition_Permutation`, may be useful.

|*)

Lemma partition_Permutation : forall p xs,
  Permutation xs (filter (geb p) xs ++ filter (Nat.ltb p) xs).
Proof.
  induction xs as [| x xs IH]. trivial.
  unfold geb.
  simpl.
  destruct (Nat.leb_spec x p).
  - apply Nat.ltb_ge in H.
    rewrite H.
    simpl.
    constructor.
    apply IH.
  - apply Nat.ltb_lt in H.
    rewrite H.
    apply Permutation_cons_app.
    apply IH.
Qed.

Lemma qs_Permutation : forall l ACC, Permutation l (qs_rec l ACC).
Proof.
  induction l as [l IH] using wf_ind_len.       (* step 3 *)
  destruct ACC.                                 (* step 4 *)
  destruct l.                                   (* step 5 *)
  (* exercise *)
Admitted.

(*|

Sorted
------

Proving that a quicksorted list is indeed sorted is more involved.
There are two notions of sortedness in the standard library: locally sorted and strongly sorted.
Since `<` is a transitive relation, they are actually equivalent, but we will use `StronglySorted` since it allows convenient use of, e.g., `Forall_app` in `Sorted_app` below.

|*)

Require Import Sorted.

Print StronglySorted.
Definition Sorted := StronglySorted le.

Lemma Sorted_app : forall xs ys,
  Sorted xs ->
  Sorted ys ->
  (forall x y, In x xs -> In y ys -> x <= y) ->
  Sorted (xs ++ ys).
Proof.
  intros xs ys Hxs Hys H.
  induction xs as [| x xs IH]. trivial.
  apply StronglySorted_inv in Hxs.
  simpl.
  constructor.
  - apply IH;
    firstorder.
  - apply Forall_app.
    split.
    + easy.
    + apply Forall_forall.
      intros y.
      apply H.
      apply in_eq.
Qed.

(*|

Next, with the goal of proving `qs_Sorted`, it is helpful to show that quicksort preserves membership: any element in the output is also in the input list.
This is formalized by `qs_In`. It follows easily from `qs_Permutation`, but, as an exercise, you can also prove it directly using well-founded induction on `l`.

|*)

Lemma qs_In : forall a l ACC, In a (qs_rec l ACC) -> In a l.
Proof.
  intros.
  apply Permutation_in with (qs_rec l ACC).
  - symmetry.
    apply qs_Permutation.
  - assumption.
Qed.

Lemma qs_filter_In : forall f a l ACC,
  In a (qs_rec (filter f l) ACC) -> f a = true.
Proof.
  intros.
  apply qs_In in H.
  apply filter_In in H.
  easy.
Qed.

Lemma qs_Sorted : forall l ACC, Sorted (qs_rec l ACC).
Proof.
  induction l as [l IH] using wf_ind_len.
  destruct ACC.
  destruct l as [| p l]. constructor.
  simpl.
  apply Sorted_app.
  2: constructor.
  - apply IH. auto.
  - apply IH. auto.
  - apply Forall_forall.
    intros.
    apply qs_filter_In, Nat.ltb_lt in H.
    lia.
  - intros x y HL HR.
    apply qs_filter_In, Nat.leb_le in HL.
    destruct HR as [Hp | HR].
    2: apply qs_filter_In, Nat.ltb_lt in HR.
    all: lia.
Qed.

(*|


Conclusion
----------

We can define a wrapper function without the accessibility argument and gather our results in a single theorem.

|*)

Definition quicksort l := qs_rec l (lt_len_wf l).

Theorem quicksort_ok : forall l, let s := quicksort l in
                                 Permutation l s /\ Sorted s.
Proof.
  split.
  - apply qs_Permutation.
  - apply qs_Sorted.
Qed.

(*|

Let's briefly assess `Leroy's criteria`_ on our implementation and verification of quicksort.
Apart from the auxiliary accessibility arguments, the definition is highly readable.
Since these accessibility arguments disappear during extraction (below), the code is arguably even easier to read.
To prove properties, there seems to be a standard design pattern, outlined in our guide. Specifically, by deriving well-foundedness using `well_founded_ltof` and adding the obligations to a hint database, we can focus on the main correctness arguments.
Lastly, no axioms were used.

|*)

Recursive Extraction quicksort.

(*|

In summary, Acc-recursion proves effective for implementing and verifying quicksort.
In the next section, we test whether Acc-recursion extends to other algorithms.



Rebalancing binary search trees
===============================

*Binary search trees* (BSTs) are most efficient when their height is minimal.
While *self-balancing BSTs* maintain a low height during updates, they are intricate.
A simpler alternative is to periodically rebalance the entire tree.
A time-optimal in-place algorithm for this was proposed by `Stout and Warren (1986)`_, building on earlier work by Day (1976).
It is known as the *Day–Stout–Warren* (DSW) algorithm.

The DSW algorithm consists of two phases.
First, the BST is flattened into a *vine*, where each parent node only has a right child.
Then, the vine is transformed into a balanced tree.
In this section, we will only examine the first phase, since the second phase is structurally recursive and hence not relevant to this tutorial.

It should be noted that, as a functional programming language, Rocq does not benefit from the algorithm's in-placeness. That is, in the worst case, our implementation requires more than :math:`O(1)` additional space.
Nevertheless, it is worthwhile to verify the correctness of the algorithm.
Moreover, the first phase is particularly relevant for this tutorial, since it uses a specialized relation to prove termination.

.. Also, although the DSW algorithm is not particularly useful in practice, it is an illustrative example of tree rotations.

In the next section, we will first define binary search trees.
Then, we will implement the first phase of the DSW algorithm, appropriately called `tree_to_vine`.
Lastly, we will prove that `tree_to_vine` is correct.


Binary search trees
-------------------

A BST is a binary tree that satisfies the following invariant: for any node with key :math:`v`, all keys in the left subtree are less than :math:`v`, and all keys in the right subtree are greater than :math:`v`.
First, we define binary trees:

|*)

Inductive tree : Type :=
  | E
  | T (l : tree) (v : nat) (r : tree).

(*|

Next, we formalize the invariant.
A definition is given in `Software Foundations`__, but instead of `Inductive`, we will define it as a predicate.
This definition enables more effective use of the powerful `firstorder` tactic, simplifying our proofs.
This is aptly illustrated by the succinct proof of `forall_tree_mono`, a lemma we will need later.

__ https://softwarefoundations.cis.upenn.edu/vfa-current/SearchTree.html#BST

|*)

Fixpoint forall_tree (P : nat -> Prop) (t : tree) : Prop :=
  match t with
  | E       => True
  | T l v r => P v /\ forall_tree P l /\ forall_tree P r
  end.

Lemma forall_tree_mono : forall P Q t,
  (forall x, P x -> Q x) ->
  forall_tree P t ->
  forall_tree Q t.
Proof.
  induction t;
  firstorder.
Qed.

Fixpoint bst (t : tree) : Prop :=
  match t with
  | E       => True
  | T l v r => forall_tree (gt v) l /\ bst l
            /\ forall_tree (lt v) r /\ bst r
  end.

(*|

For simplicity, as with quicksort, we assume that the key is a natural number (and there is no separate value).
Furthermore, `gt` and `lt` are strict, so we disallow duplicate keys.

.. Assuming we generalize the type of the key, separate values could be simulated by tupling, where the value is ignored by the relation. A similar technique can be used to add a count, allowing duplicates.


Implementation of `tree_to_vine`
--------------------------------

Now, we implement the first phase of the DSW algorithm, `tree_to_vine`.
The naive definition is given below.
Broadly speaking, we traverse down the right *spine*, and whenever the left subtree is not empty, we *rotate* one node onto the spine.
This is visualized in the following figure.
For full details, refer to the original paper.

.. image:: rotate.svg
   :alt: A (right) rotation in a graph
   :width: 600

As an aside, note how elegant the functional definition of a rotation is compared to the imperative implementation in the paper.
Essentially, only the parentheses are rearranged, so we can see at a glance that the ordering is correct.

|*)

Fail Fixpoint tree_to_vine (t : tree) : tree :=
  match t with
  (* base case: *)
  | E                  => E
  (* move down: *)
  | T E v r            => T E v (tree_to_vine r)
  (* rotate: *)
  | T (T t1 a t2) b t3 => tree_to_vine (T t1 a (T t2 b t3))
  end.

(*|

In the third case, we recur on a tree that is not a subterm of `t`, so Rocq rejects the definition.
In fact, it is non-trivial to see why `tree_to_vine` terminates.
The key observation is that the number of nodes in left subtrees 'hanging' from the spine decreases each recursive call. Here, we include leaves in the count.
This is formalized by `size_left`.

|*)

Fixpoint size (t : tree) : nat := 1 +
  match t with
  | E       => 0
  | T l _ r => size l + size r
  end.

Fixpoint size_left (t : tree) : nat :=
  match t with
  | E       => 0
  | T l _ r => size l + size_left r
  end.

(*|

In other words, `size_left t` decreases each recursive call.
Similarly to quicksort, we define a relation based on `size_left` (and derive the well-foundedness and induction principle).
Then, following our `guide <Guide to Acc-recursion_>`__, we add auxiliary arguments to `tree_to_vine` and prove the obligations as separate lemmas.
There are two distinct obligations this time, but `Hint Unfold lt_size_left` is sufficient to automatically solve the first one.

|*)

Definition lt_size_left     := ltof              _ size_left.
Definition lt_size_left_wf  := well_founded_ltof _ size_left.
Definition wf_ind_size_left := well_founded_induction lt_size_left_wf.

Fact tree_to_vine_oblig2 : forall t1 a t2 b t3,
  size_left (T t1 a (T t2 b t3)) < size_left (T (T t1 a t2) b t3).
Proof.
  intros.
  simpl.
  lia.
Qed.

Hint Unfold lt_size_left : core.
Hint Resolve tree_to_vine_oblig2 : core.

Program Fixpoint tree_to_vine (t : tree) (ACC : Acc lt_size_left t) :=
  match t with
  | E => E
  | T E v r =>
      T E v (tree_to_vine r (Acc_inv ACC _))
  | T (T t1 a t2) b t3 =>
      tree_to_vine (T t1 a (T t2 b t3)) (Acc_inv ACC _)
  end.

(*|

Previously, we used `lt` and `lt_len` as relations, which are natural choices to compare natural numbers and lists, respectively.
On the other hand, `tree_to_vine` is an example of where we need a relation tailored to the algorithm.

.. In particular, `size` as a relation would not work to show termination!

.. You can extract `tree_to_vine` and check that the code is readable.


Verification of `tree_to_vine`
------------------------------

Now, we will prove some properties of `tree_to_vine`, following our guide.
We should prove that the resulting tree is a vine and contains the same elements, similarly to quicksort.
First, we establish some supporting lemmas.
The first one, `forall_tree_to_vine`, demonstrates the proof strategy that we will repeatedly use.

|*)

Lemma forall_tree_to_vine : forall P t ACC,
  forall_tree P t -> forall_tree P (tree_to_vine t ACC).
Proof.
  induction t as [t IH] using wf_ind_size_left.
  destruct ACC.
  intros.
  destruct t.
  2: destruct t1.
  (* Now, the three cases correspond to those in the definition! *)
  3: simpl; apply IH.
  all: firstorder.
Qed.

Lemma forall_tree_lt : forall a b t,
  lt b a -> forall_tree (lt a) t -> forall_tree (lt b) t.
Proof.
  intros.
  apply forall_tree_mono with (lt a).
  1: transitivity a.
  all: assumption.
Qed.

Lemma bst_rotate : forall a b t1 t2 t3,
  bst (T (T t1 a t2) b t3) -> bst (T t1 a (T t2 b t3)).
Proof.
  firstorder using forall_tree_lt.
Qed.

(*|

We define the `vine` predicate as a special case of `bst` where all left children are `E`. Note that a vine is isomorphic to a sorted list.
Then, we prove that `tree_to_vine` outputs a `vine`.

|*)

Fixpoint vine (t : tree) : Prop :=
  match t with
  | E       => True
  | T E v r => forall_tree (lt v) r /\ vine r
  | _       => False
  end.

Lemma tree_to_vine_shape : forall t ACC,
  bst t -> vine (tree_to_vine t ACC).
Proof.
  induction t as [t IH] using wf_ind_size_left.
  destruct ACC.
  intros.
  destruct t.
  2: destruct t1.
  all: simpl.
  - trivial.
  - split.
    1: apply forall_tree_to_vine.
    2: apply IH.
    all: firstorder.
  - apply IH.
    2: apply bst_rotate.
    all: auto.
Qed.

(*|

Next, we want to prove that the output vine contains the same elements as the input tree.
Since all keys are unique, it is sufficient to show shared membership through `contains`.
The proof is left as an exercise to the reader.
Note that the condition `bst t` is not necessary.

|*)

Fixpoint contains (x : nat) (t : tree) : Prop :=
  match t with
  | E       => False
  | T l v r => x = v \/ contains x l \/ contains x r
  end.

Lemma tree_to_vine_contains : forall x t ACC,
  contains x t <-> contains x (tree_to_vine t ACC).
Proof.
  (* exercise *)
Admitted.

(*|

The combination of `tree_to_vine_shape` and `tree_to_vine_contains` verifies `tree_to_vine`.
This is only a small part of the overall correctness proof of the DSW algorithm.



Conclusion
==========

We introduced and proved the well-founded induction principle.
Then, we compared Function, Equations, Program Fixpoint, and Acc-recursion as techniques to perform well-founded recursion. We found that Acc-recursion is best if code extraction is important, and otherwise Equations is a good option.
We presented a practical guide on Acc-recursion and used it to verify a non-trivial algorithm: quicksort.
We further experimented with Acc-recursion on a tree rebalancing algorithm that requires a specialized relation to prove termination.

**Acknowledgments.**
This tutorial was developed as part of a research internship at Eindhoven University of Technology.
Thanks to `Herman Geuvers <https://www.cs.ru.nl/~herman/>`__ for his guidance in shaping the project and his enthusiastic supervision.



References
==========

.. _Leroy (2024):

Xavier Leroy. "Well-founded recursion done right". In: *The Tenth International Workshop on Coq for Programming Languages*. Jan. 2024. URL: https://popl24.sigplan.org/details/CoqPL-2024-papers/2/Well-founded-recursion-done-right.

.. _Sozeau and Mangin (2019):

Matthieu Sozeau and Cyprien Mangin. "Equations reloaded: high-level dependently-typed functional programming and proving in Coq". In: *Proceedings of the ACM on Programming Languages* 3.ICFP (July 2019), pp. 1–29. DOI: `10.1145/3341690 <https://doi.org/10.1145/3341690>`__.

.. _Stout and Warren (1986):

Quentin F. Stout and Bette L. Warren. "Tree rebalancing in optimal time and space". In: *Communications of the ACM* 29.9 (Sept. 1986), pp. 902–908. DOI: `10.1145/6592.6599 <https://doi.org/10.1145/6592.6599>`__.

|*)
