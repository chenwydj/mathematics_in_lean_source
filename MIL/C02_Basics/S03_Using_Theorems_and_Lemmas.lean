-- BOTH:
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import MIL.Common

variable (a b c d e : ℝ)
open Real

/- TEXT:
.. _using_theorems_and_lemmas:

Using Theorems and Lemmas
-------------------------

.. index:: inequalities


apply
^^^^^

Consider the library theorems ``le_refl`` and ``le_trans``:
TEXT. -/
-- QUOTE:
#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)  -- should be interpreted as ``a ≤ b → (b ≤ c → a ≤ c)``
-- P → Q → R means P → (Q → R), i.e., a function taking a proof of P and returning a function that,
-- given a proof of Q, produces a proof of R
-- QUOTE.

-- TODO:
-- /- TEXT:
-- As we explain in more detail in  :numref:`implication_and_the_universal_quantifier`,
-- the implicit parentheses in the statement of ``le_trans``
-- associate to the right, so it should be interpreted as ``a ≤ b → (b ≤ c → a ≤ c)``.
-- The library designers have set the arguments ``a``, ``b`` and ``c`` to ``le_trans`` implicit,
-- so that Lean will *not* let you provide them explicitly (unless you
-- really insist, as we will discuss later).
-- Rather, it expects to infer them from the context in which they are used.
-- For example, when hypotheses ``h : a ≤ b`` and  ``h' : b ≤ c``
-- are in the context,
-- all the following work:
-- TEXT. -/
-- section
-- -- QUOTE:
-- variable (h : a ≤ b) (h' : b ≤ c)

-- #check (le_refl : ∀ a : Real, a ≤ a)
-- #check (le_refl a : a ≤ a)
-- #check (le_trans : a ≤ b → b ≤ c → a ≤ c)
-- #check (le_trans h : b ≤ c → a ≤ c)
-- #check (le_trans h h' : a ≤ c)
-- -- QUOTE.

-- end

/- TEXT:
.. index:: apply, tactics ; apply, exact, tactics ; exact

* The ``apply`` tactic: 1) takes a statement as the argument; 2) **tries to match the statement's conclusion with your current goal**; 3) **leaves the hypotheses, if any, as new goals**.

* If the given proof matches the goal exactly (modulo *definitional* equality), you can use the ``exact`` tactic instead of ``apply``.

TEXT. -/
-- QUOTE:
example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans  -- leaves two goals
  -- · “start to focus on a new tactic block for the next goal”
  · apply h₀
  · apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans h₀
  apply h₁

example (x : ℝ) : x ≤ x := by
  apply le_refl

-- QUOTE.

/- TEXT:
Here are a few more library theorems:
TEXT. -/
-- QUOTE:
#check (le_refl : ∀ a, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)
#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_trans : a < b → b < c → a < c)
-- QUOTE.

/- TEXT:
Use them together with ``apply`` and ``exact`` to prove the following:
TEXT. -/
-- Try this.
-- QUOTE:
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  sorry
-- QUOTE.


/- TEXT:


linarith
^^^^^^^^

.. index:: linarith, tactics ; linarith

* ``linarith`` can prove the problem above automatically using equations and inequalities *in the context* by *linear arithmetic*:
TEXT. -/
-- QUOTE:
example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  linarith
-- QUOTE.

section

-- QUOTE:
example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  linarith
-- QUOTE.

end

/- TEXT:
* ``linarith`` can also use additional inequalities passed as arguments (see the example below).



Bi-Implication
^^^^^^^^^^^^^^


TEXT. -/
-- QUOTE:
example (h : 1 ≤ a) (h' : b ≤ c) : 2 + a + exp b ≤ 3 * a + exp c := by
  -- exp_le_exp: rexp x ≤ rexp y ↔ x ≤ y
  linarith [exp_le_exp.mpr h']  -- .mpr (“modus ponens reverse”) is a function derived
-- QUOTE.


/- TEXT:
* Some theorems like ``exp_le_exp``, ``exp_lt_exp`` use a *bi-implication*, implying "if and only if" (``\lr`` or ``\iff``).

* ``h.mp`` establishes the forward direction, ``A → B``, and ``h.mpr`` establishes the reverse direction, ``B → A``.

  - ``mp`` stands for "modus ponens" and ``mpr`` stands for "modus ponens reverse."

  - You can also use ``h.1`` and ``h.2`` for ``h.mp`` and ``h.mpr``.

TEXT. -/
-- QUOTE:
example (h : a ≤ b) : exp a ≤ exp b := by
  rw [exp_le_exp]
  exact h
-- QUOTE.

/- TEXT:

.. index:: exponential, logarithm

Here are some more theorems in the library that can be used to establish
inequalities on the real numbers.
TEXT. -/
-- QUOTE:
#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (log_le_log : 0 < a → a ≤ b → log a ≤ log b)
-- #check (log_lt_log : 0 < a → a < b → log a < log b)
-- #check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
-- #check (add_le_add_right : a ≤ b → ∀ c, a + c ≤ b + c)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
-- #check (add_lt_add_left : a < b → ∀ c, c + a < c + b)
-- #check (add_lt_add_right : a < b → ∀ c, a + c < b + c)
-- #check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
-- #check (add_pos : 0 < a → 0 < b → 0 < a + b)
-- #check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
#check (exp_pos : ∀ a, 0 < exp a)
-- #check add_le_add_left
-- QUOTE.

/- TEXT:
Thus the following proof works:
TEXT. -/
-- QUOTE:
example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e := by
  apply add_lt_add_of_lt_of_le
  · apply add_lt_add_of_le_of_lt h₀
    apply exp_lt_exp.mpr h₁
  apply le_refl
-- QUOTE.

/- TEXT:

norm_num
^^^^^^^^

.. index:: norm_num, tactics ; norm_num

* ``norm_num`` tactic can be used to solve concrete numeric goals.
TEXT. -/
-- QUOTE:
example : (0 : ℝ) < 1 := by norm_num  -- ``norm_num`` tactic can solve concrete numeric goals
-- QUOTE.



/- TEXT:

Search Mathlib Statements
^^^^^^^^^^^^^^^^^^^^^^^^^
TEXT. -/

-- QUOTE:
example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by sorry

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₀ : 0 < 1 + exp a := by sorry
  apply log_le_log h₀
  sorry
-- QUOTE.

/- TEXT:

As you meet more complex problems, you will find it necessary to search library theorems instead of always memorizing them.
There are a number of strategies you can use:

* Search box on Mathlib documentation
  `web pages <https://leanprover-community.github.io/mathlib4_docs/index.html>`_.

* `Loogle <https://loogle.lean-lang.org>`_ and `Lean Finder <https://www.leanfinder.org/>`_
  to search Lean and Mathlib definitions and theorems by patterns.

* You can use the ``apply?`` tactic,
  which tries to find the relevant theorem in the library.
TEXT. -/
-- QUOTE:
example : 0 ≤ a ^ 2 := by
  -- apply?
  exact sq_nonneg a
-- QUOTE.

/- TEXT:
To try out ``apply?`` in this example,
delete the ``exact`` command and uncomment the previous line.
Using these tricks,
see if you can find what you need to do the
next example:
TEXT. -/
-- QUOTE:
example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  sorry
-- QUOTE.


-- TODO:
-- /- TEXT:
-- Using the same tricks, confirm that ``linarith`` instead of ``apply?``
-- can also finish the job.

-- Here is another example of an inequality:
-- TEXT. -/
-- -- QUOTE:
-- example : 2*a*b ≤ a^2 + b^2 := by
--   have h : 0 ≤ a^2 - 2*a*b + b^2
--   calc
--     a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
--     _ ≥ 0 := by apply pow_two_nonneg

--   calc
--     2*a*b = 2*a*b + 0 := by ring
--     _ ≤ 2*a*b + (a^2 - 2*a*b + b^2) := add_le_add (le_refl _) h
--     _ = a^2 + b^2 := by ring
-- -- QUOTE.

-- /- TEXT:
-- Mathlib tends to put spaces around binary operations like ``*`` and ``^``,
-- but in this example, the more compressed format increases readability.
-- There are a number of things worth noticing.
-- First, an expression ``s ≥ t`` is definitionally equivalent to ``t ≤ s``.
-- In principle, this means one should be able to use them interchangeably.
-- But some of Lean's automation does not recognize the equivalence,
-- so Mathlib tends to favor ``≤`` over ``≥``.
-- Second, we have used the ``ring`` tactic extensively.
-- It is a real timesaver!
-- Finally, notice that in the second line of the
-- second ``calc`` proof,
-- instead of writing ``by exact add_le_add (le_refl _) h``,
-- we can simply write the proof term ``add_le_add (le_refl _) h``.

-- In fact, the only cleverness in the proof above is figuring
-- out the hypothesis ``h``.
-- Once we have it, the second calculation involves only
-- linear arithmetic, and ``linarith`` can handle it:
-- TEXT. -/
-- -- QUOTE:
-- example : 2*a*b ≤ a^2 + b^2 := by
--   have h : 0 ≤ a^2 - 2*a*b + b^2
--   calc
--     a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
--     _ ≥ 0 := by apply pow_two_nonneg
--   linarith
-- -- QUOTE.



-- TODO:
-- /- TEXT:
-- How nice! We challenge you to use these ideas to prove the
-- following theorem. You can use the theorem ``abs_le'.mpr``.
-- You will also need the ``constructor`` tactic to split a conjunction
-- to two goals; see :numref:`conjunction_and_biimplication`.
-- TEXT. -/
-- -- QUOTE:
-- example : |a*b| ≤ (a^2 + b^2)/2 := by
--   sorry

-- #check abs_le'.mpr
-- -- QUOTE.

-- -- SOLUTIONS:
-- theorem fact1 : a*b*2 ≤ a^2 + b^2 := by
--   have h : 0 ≤ a^2 - 2*a*b + b^2
--   calc
--     a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
--     _ ≥ 0 := by apply pow_two_nonneg
--   linarith

-- theorem fact2 : -(a*b)*2 ≤ a^2 + b^2 := by
--   have h : 0 ≤ a^2 + 2*a*b + b^2
--   calc
--     a^2 + 2*a*b + b^2 = (a + b)^2 := by ring
--     _ ≥ 0 := by apply pow_two_nonneg
--   linarith

-- example : |a*b| ≤ (a^2 + b^2)/2 := by
--   have h : (0 : ℝ) < 2 := by norm_num
--   apply abs_le'.mpr
--   constructor
--   · rw [le_div_iff₀ h]
--     apply fact1
--   rw [le_div_iff₀ h]
--   apply fact2

-- /- TEXT:
-- If you managed to solve this, congratulations!
-- You are well on your way to becoming a master formalizer.
-- TEXT. -/
