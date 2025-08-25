import MIL.Common
import Mathlib.Data.Real.Basic
/- TEXT:
Calculating Proof Steps via Rewriting
-------------------------------------

.. index:: rewrite, rw, tactics ; rw and rewrite



Proof State
^^^^^^^^^^^

.. index:: proof state, local context, goal

* Lean reports on the current *proof state* in the *Lean Infoview* window (click ∀ button on the top-right of VS Code, then "Toggle InfoView").

* Move cursor to see state at each proof step.


.. code-block::

    1 goal
    x y : ℕ,
    h₁ : Prime x,
    h₂ : ¬Even x,
    h₃ : y > x
    ⊢ y ≥ 4

* ``⊢``: current proof goal to be proved.

* Lines before ``⊢``: all current *context*, including objects (``x``, ``y``), assumptions/hypotheses (``h₁``, ``h₂``, ``h₃``). Everything in the context is labelled with an identifier.

  - Type subscripted labels as ``h\1``, ``h\2``, ``h\3``.




Scope via ```section ... end```
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

We can declare variables once within a scope defined in a ``section ... end`` block.
TEXT. -/
-- QUOTE:
section
variable (a b c : ℝ)

#check a
#check a + b
#check (a : ℝ)
#check mul_comm a b
#check (mul_comm a b : a * b = b * a)
#check mul_assoc c a b
#check mul_comm a
#check mul_comm

end
-- QUOTE.


/- TEXT:
rw \[``thm`` arg₁ arg₂\]
^^^^^^^^^^^^^^^^^^^^^^^^

* Use the left-hand side of ``thm``'s identity to match patterns in your current proof goal, and replace matched patterns with the right-hand side of ``thm``.

* You can use a left arrow (``\l``) to reverse an identity (i.e. go from right to left in the ``thm`` provided).

  - For example, ``rw [← mul_assoc a b c]`` replaces ``a * (b * c)`` by ``a * b * c`` in the current goal.

.. index:: real numbers
TEXT. -/
-- An example.
-- QUOTE:
example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]  -- ``mul_comm a b`` implies ``a * b = b * a``
  rw [mul_assoc b a c]  -- ``mul_assoc a b c`` implies ``a * b * c = a * (b * c)``
-- QUOTE.

/- TEXT:



TEXT. -/
-- Try these.
-- QUOTE:
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  sorry

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry
-- QUOTE.

/- TEXT:
* If you just use ``rw [thm]`` without providing arguments ``arg₁`` ``arg₂``, ``rw`` will try to match its left-hand side with the first pattern it can match in the goal.
TEXT. -/
-- An example.
-- QUOTE:
example (a b c : ℝ) : a * b * c = b * c * a := by
  rw [mul_assoc]
  rw [mul_comm]
-- QUOTE.

/- TEXT:
* You can also provide *partial* arguments. For example, ``mul_comm a`` matches any pattern of the form ``a * ?`` and rewrites it to ``? * a``.
TEXT. -/
/- Try doing the first of these without providing any arguments at all,
   and the second with only one argument. -/
-- QUOTE:
example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  sorry  -- without providing any arguments at all

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  sorry  -- with only one argument
-- QUOTE.

/- TEXT:
* ``rw`` can also take facts from the local context.
TEXT. -/
-- Using facts from the local context.
-- QUOTE:
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h']
  rw [← mul_assoc]
  rw [h]
  rw [mul_assoc]
-- QUOTE.


/- TEXT:
* Multiple rewrite commands can be chained and carried out in a single command, by listing identities separated by commas.
TEXT. -/
-- QUOTE:
example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
  rw [h', ← mul_assoc, h, mul_assoc]
-- QUOTE.


/- TEXT:
.. index:: rw, tactics ; rw and rewrite

* Rewrite in a specific assumption via ``rw [thm arg] at hyp``.
TEXT. -/
-- Examples.

section
variable (a b c d : ℝ)
-- QUOTE:
example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp  -- ``hyp`` matches the goal exactly
-- QUOTE.
end



/- TEXT:
* ``nth_rw`` : replace only particular instances of an expression in the goal. Possible matches are enumerated starting with 1.
TEXT. -/
-- Examples.
-- QUOTE:
example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]  -- replaces the second occurrence of ``a + b`` with ``c``
  rw [add_mul]
-- QUOTE.



/- TEXT:

calc (Proof Term)
^^^^^^^^^^^^^^^^^

Chained ``rw`` could make the proof progress hard to read:

.. index:: calc, tactics ; calc

TEXT. -/
section
variable (a b : ℝ)

-- QUOTE:
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  rw [mul_add, add_mul, add_mul]  -- distributivity of multiplication over addition
  rw [← add_assoc, add_assoc (a * a)]  -- associativity of addition
  rw [mul_comm b a, ← two_mul]  -- ``2 * a = a + a``
-- QUOTE.

/- TEXT:

* Lean provides a more structured way of writing proofs using the ``calc`` *proof term*.

* ``calc`` is not a tactic: no need ``by`` after ``:=``.

* Lean uses indentation to determine the begin and end of a block (tactics, ``calc``, etc.).

TEXT. -/
-- QUOTE:
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      rw [mul_add, add_mul, add_mul]
    _ = a * a + (b * a + a * b) + b * b := by  -- _ is a placehold for the RHS in previous step
      rw [← add_assoc, add_assoc (a * a)]
    _ = a * a + 2 * (a * b) + b * b := by
      rw [mul_comm b a, ← two_mul]
-- QUOTE.

/- TEXT:
* ``calc`` helps first outline with ``sorry``, then justify individual steps using tactics.
TEXT. -/
-- QUOTE:
example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
  calc
    (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
      sorry
    _ = a * a + (b * a + a * b) + b * b := by
      sorry
    _ = a * a + 2 * (a * b) + b * b := by
      sorry
-- QUOTE.
