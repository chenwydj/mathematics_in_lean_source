-- BOTH:
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import MIL.Common

/- TEXT:
.. _proving_identities_in_algebraic_structures:

Proving Basic Identities in Ring Algebraic Structure
----------------------------------------------------



Namespace
^^^^^^^^^

.. index:: namespace, open, command ; open

* When a definition or theorem ``foo`` is introduced in a *namespace* ``bar``, its full name is ``bar.foo``.

* ``open bar`` later *opens* the namespace and allows us to use the shorter name ``foo``.
TEXT. -/
-- QUOTE:
namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_neg_cancel (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

#check MyRing.add_zero
#check add_zero

end MyRing

#check add_zero
-- QUOTE.



/- TEXT:

Implicit and Explicit Arguments
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

.. index:: implicit argument


* "Parentheses" (R : Type*) — explicit parameter; you must supply R when you use the enclosing definition.
TEXT. -/

-- QUOTE:
def idR (R : Type*) (x : R) : R := x
#check idR Nat 3                   -- R given positionally
#check idR (List String) ["hi"]    -- R given positionally
#check idR (R := Nat) 3            -- R given by name (same effect)
-- QUOTE.


/- TEXT:
* "Curly Braces" {R : Type*} — implicit parameter; Lean will try to infer it from later arguments.
TEXT. -/

-- QUOTE:
def dup {R : Type*} (x : R) : R × R := (x, x)

#check dup 5                       -- infers R = Nat
#check dup (R := String) "hi"      -- give the implicit explicitly
-- QUOTE.
-- #check @dup String "hi"            -- `@` reveals/supplies all implicits
-- @f means “treat all implicits as explicit right now.”



/- TEXT:
* "Square brackets" [Ring R] — instance-implicit; Lean must find via type-class search.
TEXT. -/

-- QUOTE:
-- needs +, *, 0, 1, etc., so we ask for a (semi)ring instance
def square {R : Type*} [Semiring R] (x : R) : R := x * x

#check square 5                    -- R = Nat; uses the built-in Semiring Nat
#check square (R := Int) 7         -- pick the type; instance found automatically

-- If Lean can't find an instance, provide one locally:
section
  structure Weird where n : Nat
  instance : Semiring Weird := by
    sorry
  #check square (R := Weird) ⟨3⟩
end
-- QUOTE.




/- TEXT:


Ring and ring
^^^^^^^^^^^^^

.. index:: ring (algebraic structure)

**Ring** consists of:
a collection of objects :math:`R`,
operations :math:`+` :math:`\times`,
constants :math:`0` :math:`1`,
and the negation operation :math:`x \mapsto -x` such that:

* :math:`R` with :math:`+` is an *abelian group*, with :math:`0`
  as the additive identity and negation as inverse.
* Multiplication is associative with identity :math:`1`,
  and multiplication distributes over addition.

If we define a collection of objects of a *type* ``R`` and a generic ring structure on ``R``,
the ring axioms are as follows:
TEXT. -/
section
-- QUOTE:
variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (neg_add_cancel : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)
-- QUOTE.

end

/- TEXT:

Any theorem about rings can be applied to concrete rings (e.g. integers, ``ℤ``, rational numbers, ``ℚ``,
complex numbers ``ℂ``),
and any instance of an abstract structure that extends rings (e.g. any ordered ring or any field).

.. index:: commutative ring

* ``ring`` tactic proves equivalence b/w LHS and RHS by operations supported by Ring.

  - The ``ring`` tactic is imported indirectly when we import ``Mathlib.Data.Real.Basic``. It can be imported explicitly with the command ``import Mathlib.Tactic``.

If we further declare ``R`` to be a *commutative* ring via ``CommRing``,
then we can support commutative multiplication on ``ℝ``:
TEXT. -/
section
-- QUOTE:
variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring
-- QUOTE.

end

/- TEXT:

Here is a useful theorem:
TEXT. -/
-- BOTH:
namespace MyRing
variable {R : Type*} [Ring R]

-- EXAMPLES:
-- QUOTE:
theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, neg_add_cancel, zero_add]
-- QUOTE.

/- TEXT:
Prove the companion version:
TEXT. -/
-- Prove these:
-- QUOTE:
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  sorry
-- QUOTE.



/- TEXT:
Use these to prove the following:
TEXT. -/
-- QUOTE:
theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  sorry

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  sorry
-- QUOTE.




/- TEXT:

have
^^^^

* ``have`` introduce a new (intermediate, auxiliary) hypothesis h during the proof

  - After we prove this intermediate hypothesis, we can feel free to use it for further proofs

.. index:: apply, tactics ; apply, exact, tactics ; exact
.. index:: have, tactics ; have

let us show that ``a * 0 = 0``
follows from the ring axioms.
TEXT. -/
-- QUOTE:
theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by  -- ``have`` introduce a new (intermediate) hypothesis h
    rw [← mul_add, add_zero, add_zero]  -- indentation: sub-proof for the new goal.
  -- we now feel free to use h
  rw [add_left_cancel h]  -- ``apply add_left_cancel h`` or ``exact add_left_cancel h`` also works
-- QUOTE.


-- QUOTE:
theorem zero_mul (a : R) : 0 * a = 0 := by  -- multiplication is not assumed to be commutative
  sorry
-- QUOTE.

-- QUOTE:
theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  sorry

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  sorry

theorem neg_zero : (-0 : R) = 0 := by  -- have to distinguish -0 in the arg by specifying its type
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  sorry
-- QUOTE.


-- BOTH:
end MyRing




/- TEXT:

rfl
^^^

In Lean, subtraction in a ring is provably equal to
addition of the additive inverse.
TEXT. -/
-- Examples.
section
variable {R : Type*} [Ring R]

-- QUOTE:
example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b
-- QUOTE.

end

/- TEXT:
On the real numbers, it is *defined* that way:
TEXT. -/
-- QUOTE:
example (a b : ℝ) : a - b = a + -b := by
  rfl
-- QUOTE.

/- TEXT:
.. index:: rfl, reflexivity, tactics ; refl and reflexivity, definitional equality

The proof term ``rfl`` is short for "reflexivity".
The ``rfl`` tactic forces Lean
to unfold the definition and recognize both sides as being the same, i.e. *definitional equality*.
TEXT. -/


-- TODO:
-- /- TEXT:
-- .. index:: group (algebraic structure)

-- We close this section by noting that some of the facts about
-- addition and negation that we established above do not
-- need the full strength of the ring axioms, or even
-- commutativity of addition. The weaker notion of a *group*
-- can be axiomatized as follows:
-- TEXT. -/
-- section
-- -- QUOTE:
-- variable (A : Type*) [AddGroup A]

-- #check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
-- #check (zero_add : ∀ a : A, 0 + a = a)
-- #check (neg_add_cancel : ∀ a : A, -a + a = 0)
-- -- QUOTE.

-- end

-- /- TEXT:
-- It is conventional to use additive notation when
-- the group operation is commutative,
-- and multiplicative notation otherwise.
-- So Lean defines a multiplicative version as well as the
-- additive version (and also their abelian variants,
-- ``AddCommGroup`` and ``CommGroup``).
-- TEXT. -/
-- -- BOTH:
-- section
-- -- QUOTE:
-- variable {G : Type*} [Group G]

-- -- EXAMPLES:
-- #check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
-- #check (one_mul : ∀ a : G, 1 * a = a)
-- #check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)
-- -- QUOTE.

-- /- TEXT:
-- If you are feeling cocky, try proving the following facts about
-- groups, using only these axioms.
-- You will need to prove a number of helper lemmas along the way.
-- The proofs we have carried out in this section provide some hints.
-- TEXT. -/
-- -- BOTH:
-- namespace MyGroup

-- -- EXAMPLES:
-- -- QUOTE:
-- theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
--   sorry

-- theorem mul_one (a : G) : a * 1 = a := by
--   sorry

-- theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
--   sorry
-- -- QUOTE.

-- -- SOLUTIONS:
-- theorem mul_inv_cancelαα (a : G) : a * a⁻¹ = 1 := by
--   have h : (a * a⁻¹)⁻¹ * (a * a⁻¹ * (a * a⁻¹)) = 1 := by
--     rw [mul_assoc, ← mul_assoc a⁻¹ a, inv_mul_cancel, one_mul, inv_mul_cancel]
--   rw [← h, ← mul_assoc, inv_mul_cancel, one_mul]

-- theorem mul_oneαα (a : G) : a * 1 = a := by
--   rw [← inv_mul_cancel a, ← mul_assoc, mul_inv_cancel, one_mul]

-- theorem mul_inv_revαα (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
--   rw [← one_mul (b⁻¹ * a⁻¹), ← inv_mul_cancel (a * b), mul_assoc, mul_assoc, ← mul_assoc b b⁻¹,
--     mul_inv_cancel, one_mul, mul_inv_cancel, mul_one]

-- -- BOTH:
-- end MyGroup

-- end

-- /- TEXT:
-- .. index:: group (tactic), tactics ; group, tactics ; noncomm_ring, tactics ; abel

-- Explicitly invoking those lemmas is tedious, so Mathlib provides
-- tactics similar to `ring` in order to cover most uses: `group`
-- is for non-commutative multiplicative groups, `abel` for abelian
-- additive groups, and `noncomm_ring` for non-commutative rings.
-- It may seem odd that the algebraic structures are called
-- `Ring` and `CommRing` while the tactics are named
-- `noncomm_ring` and `ring`. This is partly for historical reasons,
-- but also for the convenience of using a shorter name for the
-- tactic that deals with commutative rings, since it is used more often.
-- TEXT. -/
