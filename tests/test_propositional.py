#!/usr/bin/env python3
"""
Comprehensive Unit Tests for Propositional Logic in MathLogic.
"""

import unittest
import sys
import os

# Ensure MathLogic is in PYTHONPATH
REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if REPO_ROOT not in sys.path:
    sys.path.insert(0, REPO_ROOT)

from Propositional import (
    AtomVars, nat, Atom, Bot, Top, Not, Conj, Disj, Impl, Iff,
    foIb, truth_table, is_tautology, is_contradiction, is_satisfiable,
    find_model, to_nnf, to_cnf_formula, to_dnf_formula, formula_to_clauses,
    dpll_solve, sat_solve
)


class TestPropositionalCore(unittest.TestCase):
    def test_legacy_types(self):
        """Test backwards compatibility with Coq AtomVars and nat types."""
        self.assertEqual(AtomVars, nat)
        self.assertEqual(AtomVars, int)

    def test_ast_construction_and_str(self):
        p = Atom("P")
        q = Atom("Q")
        self.assertEqual(str(p), "P")
        self.assertEqual(str(Bot()), "Bot")
        self.assertEqual(str(Top()), "Top")
        self.assertEqual(str(~p), "~P")
        self.assertEqual(str(p & q), "(P & Q)")
        self.assertEqual(str(p | q), "(P | Q)")
        self.assertEqual(str(p >> q), "(P >> Q)")
        self.assertEqual(str(p.iff(q)), "(P <-> Q)")

    def test_ast_equality_and_hash(self):
        p1 = Atom("P")
        p2 = Atom("P")
        q = Atom("Q")
        self.assertEqual(p1, p2)
        self.assertNotEqual(p1, q)
        self.assertEqual(hash(p1), hash(p2))
        self.assertEqual(p1 & q, p2 & q)

    def test_atoms_extraction(self):
        p = Atom("P")
        q = Atom(1)
        r = Atom(2)
        form = (p >> q) | (~r & Bot())
        self.assertEqual(form.atoms(), {"P", 1, 2})

    def test_evaluation_and_foIb(self):
        p = Atom("P")
        q = Atom("Q")
        f = p & ~q

        # Valuation 1: P=True, Q=False => f is True
        v1 = {"P": True, "Q": False}
        self.assertTrue(f.evaluate(v1))
        self.assertTrue(foIb(v1, f))

        # Valuation 2: P=True, Q=True => f is False
        v2 = {"P": True, "Q": True}
        self.assertFalse(f.evaluate(v2))
        self.assertFalse(foIb(v2, f))

        # Test Implication evaluation
        impl = p >> q
        self.assertTrue(impl.evaluate({"P": False, "Q": False}))
        self.assertTrue(impl.evaluate({"P": False, "Q": True}))
        self.assertFalse(impl.evaluate({"P": True, "Q": False}))
        self.assertTrue(impl.evaluate({"P": True, "Q": True}))

    def test_truth_table(self):
        p = Atom("P")
        table = truth_table(p | ~p)
        self.assertEqual(len(table), 2)
        for val, res in table:
            self.assertTrue(res)

    def test_tautologies(self):
        p = Atom("P")
        q = Atom("Q")
        r = Atom("R")

        # Law of excluded middle: P | ~P
        self.assertTrue(is_tautology(p | ~p))

        # Modus Ponens valid implication: (P & (P >> Q)) >> Q
        modus_ponens = (p & (p >> q)) >> q
        self.assertTrue(is_tautology(modus_ponens))

        # De Morgan's Law 1: ~(P & Q) <-> (~P | ~Q)
        de_morgan_1 = (~(p & q)).iff(~p | ~q)
        self.assertTrue(is_tautology(de_morgan_1))

        # De Morgan's Law 2: ~(P | Q) <-> (~P & ~Q)
        de_morgan_2 = (~(p | q)).iff(~p & ~q)
        self.assertTrue(is_tautology(de_morgan_2))

        # Peirce's Law: ((P >> Q) >> P) >> P
        peirces_law = ((p >> q) >> p) >> p
        self.assertTrue(is_tautology(peirces_law))

        # Hypothetical Syllogism: ((P >> Q) & (Q >> R)) >> (P >> R)
        hyp_syl = ((p >> q) & (q >> r)) >> (p >> r)
        self.assertTrue(is_tautology(hyp_syl))

        # Non-tautology: P >> Q
        self.assertFalse(is_tautology(p >> q))

    def test_contradictions(self):
        p = Atom("P")
        q = Atom("Q")

        self.assertTrue(is_contradiction(p & ~p))
        self.assertTrue(is_contradiction(Bot()))
        self.assertFalse(is_contradiction(p | ~p))
        self.assertFalse(is_contradiction(p & q))

    def test_satisfiability_and_model_finding(self):
        p = Atom("P")
        q = Atom("Q")

        sat_form = p & ~q
        self.assertTrue(is_satisfiable(sat_form))
        model = find_model(sat_form)
        self.assertIsNotNone(model)
        self.assertTrue(model["P"])
        self.assertFalse(model["Q"])

        unsat_form = p & ~p
        self.assertFalse(is_satisfiable(unsat_form))
        self.assertIsNone(find_model(unsat_form))

    def test_normal_forms_nnf(self):
        p = Atom("P")
        q = Atom("Q")

        # Double negation
        self.assertEqual(to_nnf(~(~p)), p)

        # Implication to NNF
        nnf_impl = to_nnf(p >> q)
        self.assertEqual(nnf_impl, ~p | q)

        # Equivalence preservation of NNF
        complex_form = ~(p >> (q & ~p))
        nnf_complex = to_nnf(complex_form)
        self.assertTrue(is_tautology(complex_form.iff(nnf_complex)))

    def test_normal_forms_cnf_dnf(self):
        p = Atom("P")
        q = Atom("Q")
        r = Atom("R")

        f = (p & q) | r
        cnf = to_cnf_formula(f)
        dnf = to_dnf_formula(f)

        # CNF and DNF must be semantically equivalent to f
        self.assertTrue(is_tautology(f.iff(cnf)))
        self.assertTrue(is_tautology(f.iff(dnf)))

    def test_dpll_sat_solver(self):
        p = Atom("P")
        q = Atom("Q")
        r = Atom("R")

        # Satisfiable problem: (P | Q) & (~P | R) & (~Q | ~R)
        f_sat = (p | q) & (~p | r) & (~q | ~r)
        model = sat_solve(f_sat)
        self.assertIsNotNone(model)
        self.assertTrue(f_sat.evaluate(model))

        # Unsatisfiable problem: P & ~P
        f_unsat = p & ~p
        self.assertIsNone(sat_solve(f_unsat))

        # 3-variable unsatisfiable CNF:
        # (P) & (Q) & (~P | ~Q)
        f_unsat2 = p & q & (~p | ~q)
        self.assertIsNone(sat_solve(f_unsat2))


if __name__ == "__main__":
    unittest.main()
