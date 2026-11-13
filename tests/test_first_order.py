#!/usr/bin/env python3
"""
Comprehensive Unit Tests for First-Order Logic (FOL) in MathLogic.
"""

import unittest
import sys
import os

REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if REPO_ROOT not in sys.path:
    sys.path.insert(0, REPO_ROOT)

from FirstOrder import (
    Var, Const, Fn, Pred, Eq, FoBot, FoTop, FoNot, FoConj, FoDisj, FoImpl, FoIff,
    Forall, Exists, unify_terms, unify_predicates, Structure,
    FoLiteral, FoClause, resolve_clauses, factor_clause, prove_by_resolution
)


class TestFirstOrderCore(unittest.TestCase):
    def test_term_construction_and_vars(self):
        x = Var("x")
        y = Var("y")
        c = Const("c")
        f = Fn("f", [x, Fn("g", [y, c])])

        self.assertEqual(str(f), "f(x, g(y, c))")
        self.assertEqual(f.vars(), {"x", "y"})
        self.assertEqual(c.vars(), set())

    def test_term_substitution(self):
        x = Var("x")
        y = Var("y")
        c = Const("c")
        t = Fn("f", [x, y])

        t_sub = t.subst({"x": c, "y": Fn("h", [c])})
        self.assertEqual(str(t_sub), "f(c, h(c))")

    def test_formula_free_and_bound_vars(self):
        x = Var("x")
        y = Var("y")
        z = Var("z")

        # P(x, y) & forall z. Q(y, z)
        f1 = Pred("P", [x, y]) & Forall("z", Pred("Q", [y, z]))
        self.assertEqual(f1.free_vars(), {"x", "y"})
        self.assertEqual(f1.bound_vars(), {"z"})
        self.assertFalse(f1.is_sentence())

        # forall x. exists y. P(x, y)
        f2 = Forall("x", Exists("y", Pred("P", [x, y])))
        self.assertEqual(f2.free_vars(), set())
        self.assertEqual(f2.bound_vars(), {"x", "y"})
        self.assertTrue(f2.is_sentence())

    def test_capture_avoiding_substitution(self):
        # forall y. P(x, y)
        # substitute x -> y
        # Must rename y to y_1 to avoid capturing y
        x = Var("x")
        y = Var("y")
        f = Forall("y", Pred("P", [x, y]))

        f_sub = f.subst({"x": y})
        self.assertIsInstance(f_sub, Forall)
        self.assertNotEqual(f_sub.var, "y")
        self.assertIn("y", f_sub.free_vars())
        self.assertNotIn("x", f_sub.free_vars())

    def test_unification_basic(self):
        x = Var("x")
        y = Var("y")
        a = Const("a")
        b = Const("b")

        # unify f(x, a) with f(b, y) => x=b, y=a
        t1 = Fn("f", [x, a])
        t2 = Fn("f", [b, y])
        mgu = unify_terms(t1, t2)
        self.assertIsNotNone(mgu)
        self.assertEqual(mgu["x"], b)
        self.assertEqual(mgu["y"], a)

    def test_unification_occurs_check(self):
        x = Var("x")
        # unify x with f(x) must fail due to occurs-check
        t1 = x
        t2 = Fn("f", [x])
        mgu = unify_terms(t1, t2)
        self.assertIsNone(mgu)

    def test_predicate_unification(self):
        x = Var("x")
        y = Var("y")
        c = Const("c")

        p1 = Pred("P", [x, Fn("f", [x])])
        p2 = Pred("P", [c, y])
        mgu = unify_predicates(p1, p2)
        self.assertIsNotNone(mgu)
        self.assertEqual(mgu["x"], c)
        self.assertEqual(mgu["y"], Fn("f", [c]))

    def test_finite_structure_evaluation(self):
        # Domain {0, 1, 2}
        domain = {0, 1, 2}
        constants = {"zero": 0, "two": 2}
        functions = {
            "succ": lambda a: (a + 1) % 3,
            "add": lambda a, b: (a + b) % 3,
        }
        predicates = {
            "Even": lambda a: a % 2 == 0,
            "Lt": lambda a, b: a < b,
        }
        struct = Structure(domain, constants, functions, predicates)

        x = Var("x")
        y = Var("y")
        zero = Const("zero")

        # forall x. add(x, zero) = x
        comm_zero = Forall("x", Eq(Fn("add", [x, zero]), x))
        self.assertTrue(struct.eval_formula(comm_zero))

        # exists x. Even(x) & Lt(zero, x)
        # Even numbers in {0, 1, 2} are 0 and 2. 0 < 2 holds for x=2.
        f_exists = Exists("x", Pred("Even", [x]) & Pred("Lt", [zero, x]))
        self.assertTrue(struct.eval_formula(f_exists))

        # forall x. Even(x) is False since 1 is not even
        f_all_even = Forall("x", Pred("Even", [x]))
        self.assertFalse(struct.eval_formula(f_all_even))

    def test_resolution_prover_syllogism(self):
        # All men are mortal: ~Man(x) | Mortal(x)
        # Socrates is a man: Man(socrates)
        # Goal: Mortal(socrates)
        # Negated goal: ~Mortal(socrates)
        x = Var("x")
        socrates = Const("socrates")

        c1 = FoClause([
            FoLiteral(Pred("Man", [x]), False),
            FoLiteral(Pred("Mortal", [x]), True),
        ])
        c2 = FoClause([
            FoLiteral(Pred("Man", [socrates]), True),
        ])
        c3 = FoClause([
            FoLiteral(Pred("Mortal", [socrates]), False),
        ])

        proved, log = prove_by_resolution([c1, c2, c3])
        self.assertTrue(proved)
        self.assertTrue(any("[]" in entry or "Contradiction" in entry for entry in log))

    def test_resolution_prover_transitivity(self):
        # R(a, b), R(b, c), ~R(x, y) | ~R(y, z) | R(x, z), Negated goal: ~R(a, c)
        a, b, c = Const("a"), Const("b"), Const("c")
        x, y, z = Var("x"), Var("y"), Var("z")

        c_ab = FoClause([FoLiteral(Pred("R", [a, b]), True)])
        c_bc = FoClause([FoLiteral(Pred("R", [b, c]), True)])
        c_trans = FoClause([
            FoLiteral(Pred("R", [x, y]), False),
            FoLiteral(Pred("R", [y, z]), False),
            FoLiteral(Pred("R", [x, z]), True),
        ])
        c_goal = FoClause([FoLiteral(Pred("R", [a, c]), False)])

        proved, log = prove_by_resolution([c_ab, c_bc, c_trans, c_goal])
        self.assertTrue(proved)


if __name__ == "__main__":
    unittest.main()
