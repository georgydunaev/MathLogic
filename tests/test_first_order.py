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
    FoLiteral, FoClause, resolve_clauses, factor_clause, prove_by_resolution,
    to_nnf, standardize_apart_formula, to_prenex, skolemize,
    to_cnf_matrix, formula_to_clauses, prove_validity_by_resolution,
    SignedFormula, TableauBranch, SemanticTableau, prove_by_tableau
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

    def test_to_nnf_and_prenex(self):
        x = Var("x")
        y = Var("y")
        p = Pred("P", [x])
        q = Pred("Q", [y])

        # ~(forall x. P(x)) => exists x. ~P(x)
        f1 = ~Forall("x", p)
        nnf1 = to_nnf(f1)
        self.assertIsInstance(nnf1, Exists)
        self.assertEqual(nnf1.var, "x")
        self.assertIsInstance(nnf1.body, FoNot)

        # ~(exists x. P(x)) => forall x. ~P(x)
        f2 = ~Exists("x", p)
        nnf2 = to_nnf(f2)
        self.assertIsInstance(nnf2, Forall)
        self.assertEqual(nnf2.var, "x")

        # Prenex normal form for (forall x. P(x)) & (exists y. Q(y))
        f_conj = Forall("x", p) & Exists("y", q)
        prenex = to_prenex(f_conj)
        self.assertIsInstance(prenex, (Forall, Exists))

    def test_skolemization(self):
        x = Var("x")
        y = Var("y")
        z = Var("z")

        # forall x. exists y. P(x, y) => forall x. P(x, sk_f_1(x))
        f = Forall("x", Exists("y", Pred("P", [x, y])))
        sk = skolemize(f)
        self.assertIsInstance(sk, Forall)
        self.assertIsInstance(sk.body, Pred)
        self.assertEqual(sk.body.args[0], x)
        self.assertIsInstance(sk.body.args[1], Fn)
        self.assertTrue(sk.body.args[1].name.startswith("sk_f_"))

        # Quantifier-free matrix option
        sk_mat = skolemize(f, drop_universal=True)
        self.assertIsInstance(sk_mat, Pred)

        # exists z. Q(z) with no universal quantifiers => Q(sk_c_1)
        f_const = Exists("z", Pred("Q", [z]))
        sk_c = skolemize(f_const)
        self.assertIsInstance(sk_c, Pred)
        self.assertIsInstance(sk_c.args[0], Const)
        self.assertTrue(sk_c.args[0].name.startswith("sk_c_"))

    def test_formula_to_clauses(self):
        x = Var("x")
        c = Const("c")
        # forall x. (P(x) | ~Q(x)) & R(c)
        f = Forall("x", (Pred("P", [x]) | ~Pred("Q", [x])) & Pred("R", [c]))
        clauses = formula_to_clauses(f)
        self.assertEqual(len(clauses), 2)

    def test_resolution_prover_validity(self):
        x = Var("x")
        c = Const("c")

        # Universal Instantiation: (forall x. P(x)) >> P(c) is valid
        f_ui = Forall("x", Pred("P", [x])) >> Pred("P", [c])
        proved, log = prove_validity_by_resolution(f_ui)
        self.assertTrue(proved)

        # Syllogism validity:
        # ((forall x. (Man(x) >> Mortal(x))) & Man(socrates)) >> Mortal(socrates)
        soc = Const("socrates")
        f_syl = (
            Forall("x", Pred("Man", [x]) >> Pred("Mortal", [x])) & Pred("Man", [soc])
        ) >> Pred("Mortal", [soc])
        proved_syl, _ = prove_validity_by_resolution(f_syl)
        self.assertTrue(proved_syl)

        # Invalid formula: P(a) >> P(b)
        a = Const("a")
        b = Const("b")
        f_invalid = Pred("P", [a]) >> Pred("P", [b])
        proved_inv, _ = prove_validity_by_resolution(f_invalid)
        self.assertFalse(proved_inv)

    def test_semantic_tableau_validity(self):
        x = Var("x")
        c = Const("c")

        # 1. Identity / Tautology: P(c) >> P(c)
        f_id = Pred("P", [c]) >> Pred("P", [c])
        proved_id, _ = prove_by_tableau(f_id)
        self.assertTrue(proved_id)

        # 2. Universal Instantiation: (forall x. P(x)) >> P(c)
        f_ui = Forall("x", Pred("P", [x])) >> Pred("P", [c])
        proved_ui, _ = prove_by_tableau(f_ui)
        self.assertTrue(proved_ui)

        # 3. Forall implies Exists: (forall x. P(x)) >> (exists x. P(x))
        f_ae = Forall("x", Pred("P", [x])) >> Exists("x", Pred("P", [x]))
        proved_ae, _ = prove_by_tableau(f_ae)
        self.assertTrue(proved_ae)

        # 4. De Morgan quantifier duality: ~(exists x. P(x)) <-> (forall x. ~P(x))
        f_dm = (~Exists("x", Pred("P", [x]))).iff(Forall("x", ~Pred("P", [x])))
        proved_dm, _ = prove_by_tableau(f_dm)
        self.assertTrue(proved_dm)

        # 5. Invalid formula: (exists x. P(x)) >> (forall x. P(x))
        f_non_valid = Exists("x", Pred("P", [x])) >> Forall("x", Pred("P", [x]))
        proved_nv, _ = prove_by_tableau(f_non_valid)
        self.assertFalse(proved_nv)


if __name__ == "__main__":
    unittest.main()
