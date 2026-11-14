#!/usr/bin/env python3
"""
Comprehensive Unit Tests for First-Order Equational Reasoning,
Congruence Closure, Paramodulation, and Knuth-Bendix Completion in MathLogic.
"""

import unittest
import sys
import os

REPO_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if REPO_ROOT not in sys.path:
    sys.path.insert(0, REPO_ROOT)

from FirstOrder import (
    Var, Const, Fn, Pred, Eq, Forall, Exists, FoImpl, FoConj, FoDisj, FoNot,
    FoLiteral, FoClause
)
from Equational import (
    get_subterm, replace_subterm, all_subterm_positions,
    all_literal_positions, replace_literal_subterm,
    is_equality_literal, make_equality_literal,
    equality_reflexivity_axiom, equality_symmetry_axiom, equality_transitivity_axiom,
    function_congruence_axiom, predicate_congruence_axiom,
    extract_signature_from_formulas, extract_signature_from_clauses,
    generate_equality_axioms, generate_equality_clauses,
    CongruenceClosure, check_ground_validity, check_ground_satisfiability,
    paramodulate, equality_resolution, prove_by_paramodulation, prove_equational_validity,
    RewriteRule, match_term, rewrite_step, normalize_term,
    lpo_greater, critical_pairs, knuth_bendix_completion, solve_word_problem
)


class TestSubtermPositions(unittest.TestCase):
    def test_term_navigation_and_replacement(self):
        x = Var("x")
        y = Var("y")
        c = Const("c")
        t = Fn("f", [x, Fn("g", [y, c])])

        # Root position ()
        self.assertEqual(get_subterm(t, ()), t)

        # Position (0,) -> x
        self.assertEqual(get_subterm(t, (0,)), x)

        # Position (1,) -> g(y, c)
        self.assertEqual(get_subterm(t, (1,)), Fn("g", [y, c]))

        # Position (1, 1) -> c
        self.assertEqual(get_subterm(t, (1, 1)), c)

        # Replace (1, 0) y with Const("d")
        d = Const("d")
        t_repl = replace_subterm(t, (1, 0), d)
        self.assertEqual(str(t_repl), "f(x, g(d, c))")

    def test_all_subterm_positions(self):
        a = Const("a")
        b = Const("b")
        t = Fn("f", [a, Fn("g", [b])])
        positions = all_subterm_positions(t)
        pos_indices = [p for p, _ in positions]
        self.assertIn((), pos_indices)
        self.assertIn((0,), pos_indices)
        self.assertIn((1,), pos_indices)
        self.assertIn((1, 0), pos_indices)

    def test_literal_positions_and_replacement(self):
        a = Const("a")
        b = Const("b")
        lit = FoLiteral(Pred("P", [Fn("f", [a]), b]), is_positive=True)

        lit_positions = all_literal_positions(lit, non_variable_only=True)
        subterms = [sub for _, sub in lit_positions]
        self.assertIn(Fn("f", [a]), subterms)
        self.assertIn(a, subterms)
        self.assertIn(b, subterms)

        # Replace subterm 'a' at (0, 0) with 'c'
        c = Const("c")
        lit_repl = replace_literal_subterm(lit, (0, 0), c)
        self.assertEqual(str(lit_repl), "P(f(c), b)")


class TestEqualityAxioms(unittest.TestCase):
    def test_basic_equality_axioms(self):
        refl = equality_reflexivity_axiom()
        symm = equality_symmetry_axiom()
        trans = equality_transitivity_axiom()

        self.assertTrue(refl.is_sentence())
        self.assertTrue(symm.is_sentence())
        self.assertTrue(trans.is_sentence())

    def test_congruence_axioms(self):
        fn_cong = function_congruence_axiom("f", 2)
        self.assertTrue(fn_cong.is_sentence())

        pred_cong = predicate_congruence_axiom("P", 1)
        self.assertTrue(pred_cong.is_sentence())

    def test_generate_equality_axioms_and_clauses(self):
        sig = ({"f": 1, "g": 2}, {"P": 1})
        axioms = generate_equality_axioms(sig)
        # refl, symm, trans, f-cong, g-cong, P-cong = 6 axioms
        self.assertEqual(len(axioms), 6)

        clauses = generate_equality_clauses(sig)
        self.assertEqual(len(clauses), 6)
        self.assertTrue(all(isinstance(c, FoClause) for c in clauses))


class TestCongruenceClosure(unittest.TestCase):
    def test_ground_equivalence_and_symmetry(self):
        cc = CongruenceClosure()
        a = Const("a")
        b = Const("b")
        cc.merge(a, b)
        self.assertTrue(cc.are_equal(a, b))
        self.assertTrue(cc.are_equal(b, a))

    def test_ground_transitivity_chain(self):
        cc = CongruenceClosure()
        a = Const("a")
        b = Const("b")
        c = Const("c")
        d = Const("d")
        cc.merge(a, b)
        cc.merge(b, c)
        cc.merge(c, d)
        self.assertTrue(cc.are_equal(a, d))
        self.assertEqual(len(cc.get_classes()), 1)

    def test_function_congruence_basic(self):
        cc = CongruenceClosure()
        a = Const("a")
        b = Const("b")
        fa = Fn("f", [a])
        fb = Fn("f", [b])
        cc.merge(a, b)
        self.assertTrue(cc.are_equal(fa, fb))

    def test_nested_function_congruence_classic(self):
        # f^3(a) = a and f^5(a) = a => f(a) = a
        cc = CongruenceClosure()
        a = Const("a")
        fa = Fn("f", [a])
        ffa = Fn("f", [fa])
        fffa = Fn("f", [ffa])
        ffffa = Fn("f", [fffa])
        fffffa = Fn("f", [ffffa])

        cc.merge(fffa, a)
        cc.merge(fffffa, a)
        self.assertTrue(cc.are_equal(fa, a))

    def test_multi_argument_congruence(self):
        # a = b, b = c, d = e, f(a, d) = g(c, e) => f(b, e) = g(a, d)
        a = Const("a")
        b = Const("b")
        c = Const("c")
        d = Const("d")
        e = Const("e")
        fad = Fn("f", [a, d])
        gce = Fn("g", [c, e])
        fbe = Fn("f", [b, e])
        gad = Fn("g", [a, d])

        hypotheses = [(a, b), (b, c), (d, e), (fad, gce)]
        self.assertTrue(check_ground_validity(hypotheses, (fbe, gad)))

    def test_ground_satisfiability_with_disequalities(self):
        a = Const("a")
        b = Const("b")
        c = Const("c")

        # Satisfiable: {a = b}, {a != c}
        self.assertTrue(check_ground_satisfiability([(a, b)], [(a, c)]))

        # Unsatisfiable: {a = b, b = c}, {a != c}
        self.assertFalse(check_ground_satisfiability([(a, b), (b, c)], [(a, c)]))


class TestParamodulationAndProver(unittest.TestCase):
    def test_paramodulation_step(self):
        a = Const("a")
        b = Const("b")
        fa = Fn("f", [a])
        c1 = FoClause([FoLiteral(Pred("=", [fa, b]), is_positive=True)])
        c2 = FoClause([FoLiteral(Pred("P", [fa]), is_positive=True)])

        paramodulants = paramodulate(c1, c2)
        expected = FoClause([FoLiteral(Pred("P", [b]), is_positive=True)])
        self.assertIn(expected, paramodulants)

    def test_equality_resolution_rule(self):
        a = Const("a")
        x = Var("x")
        # Clause [x != a, Q(x)]
        c = FoClause([
            FoLiteral(Pred("=", [x, a]), is_positive=False),
            FoLiteral(Pred("Q", [x]), is_positive=True)
        ])
        resolvents = equality_resolution(c)
        expected = FoClause([FoLiteral(Pred("Q", [a]), is_positive=True)])
        self.assertIn(expected, resolvents)

    def test_prove_by_paramodulation_refutation(self):
        a = Const("a")
        b = Const("b")
        fa = Fn("f", [a])

        # Axioms: f(a) = b, P(f(a))
        # Goal: P(b)
        # Negated goal: ~P(b)
        c1 = FoClause([FoLiteral(Pred("=", [fa, b]), is_positive=True)])
        c2 = FoClause([FoLiteral(Pred("P", [fa]), is_positive=True)])
        c3 = FoClause([FoLiteral(Pred("P", [b]), is_positive=False)])

        proved, log = prove_by_paramodulation([c1, c2, c3])
        self.assertTrue(proved)

    def test_prove_equational_validity_formulas(self):
        x = Var("x")
        y = Var("y")
        z = Var("z")

        # Symmetry: forall x y. (x = y -> y = x)
        symm = Forall("x", Forall("y", Eq(x, y) >> Eq(y, x)))
        proved, _ = prove_equational_validity(symm)
        self.assertTrue(proved)

        # Transitivity: forall x y z. ((x = y & y = z) -> x = z)
        trans = Forall("x", Forall("y", Forall("z", (Eq(x, y) & Eq(y, z)) >> Eq(x, z))))
        proved, _ = prove_equational_validity(trans)
        self.assertTrue(proved)

        # Function congruence: forall x y. (x = y -> f(x) = f(y))
        cong = Forall("x", Forall("y", Eq(x, y) >> Eq(Fn("f", [x]), Fn("f", [y]))))
        proved, _ = prove_equational_validity(cong)
        self.assertTrue(proved)


class TestTermRewritingSystem(unittest.TestCase):
    def test_rewrite_rule_validation(self):
        x = Var("x")
        y = Var("y")
        # Valid: f(x) ==> x
        r = RewriteRule(Fn("f", [x]), x)
        self.assertEqual(str(r), "f(x) ==> x")

        # Invalid: LHS is a variable
        with self.assertRaises(ValueError):
            RewriteRule(x, Fn("f", [x]))

        # Invalid: RHS has unbound variable y
        with self.assertRaises(ValueError):
            RewriteRule(Fn("f", [x]), y)

    def test_match_term(self):
        x = Var("x")
        y = Var("y")
        c = Const("c")
        d = Const("d")

        # Match f(x, c) with f(d, c) => {x: d}
        pat = Fn("f", [x, c])
        tgt = Fn("f", [d, c])
        subst = match_term(pat, tgt)
        self.assertIsNotNone(subst)
        self.assertEqual(subst["x"], d)

        # Match f(x, x) with f(c, d) must fail (x cannot bind to both c and d)
        pat2 = Fn("f", [x, x])
        tgt2 = Fn("f", [c, d])
        self.assertIsNone(match_term(pat2, tgt2))

    def test_term_normalization(self):
        x = Var("x")
        a = Const("a")
        # Rules: f(x) ==> x, g(x) ==> f(x)
        r1 = RewriteRule(Fn("f", [x]), x)
        r2 = RewriteRule(Fn("g", [x]), Fn("f", [x]))

        # g(g(a)) normalizes to a
        t = Fn("g", [Fn("g", [a])])
        norm = normalize_term(t, [r1, r2])
        self.assertEqual(norm, a)

    def test_lexicographic_path_ordering(self):
        x = Var("x")
        y = Var("y")
        z = Var("z")
        e = Const("e")
        def mul(a, b): return Fn("*", [a, b])
        def inv(a): return Fn("i", [a])

        precedence = {"i": 3, "*": 2, "e": 1}

        # Associativity: (x * y) * z > x * (y * z)
        s = mul(mul(x, y), z)
        t = mul(x, mul(y, z))
        self.assertTrue(lpo_greater(s, t, precedence))

        # Identity: e * x > x
        self.assertTrue(lpo_greater(mul(e, x), x, precedence))

        # Inverse: i(x) * x > e
        self.assertTrue(lpo_greater(mul(inv(x), x), e, precedence))

    def test_knuth_bendix_group_completion(self):
        x = Var("x")
        y = Var("y")
        z = Var("z")
        e = Const("e")
        def mul(a, b): return Fn("*", [a, b])
        def inv(a): return Fn("i", [a])

        precedence = {"i": 3, "*": 2, "e": 1}
        axioms = [
            (mul(e, x), x),
            (mul(inv(x), x), e),
            (mul(mul(x, y), z), mul(x, mul(y, z)))
        ]

        rules = knuth_bendix_completion(axioms, precedence=precedence, max_iterations=150)
        self.assertIsNotNone(rules)
        self.assertGreaterEqual(len(rules), 10)

        # Word problem solving:
        # 1. x * e = x (right identity)
        self.assertTrue(solve_word_problem(axioms, (mul(x, e), x), precedence=precedence))

        # 2. x * i(x) = e (right inverse)
        self.assertTrue(solve_word_problem(axioms, (mul(x, inv(x)), e), precedence=precedence))

        # 3. i(i(x)) = x (double inverse)
        self.assertTrue(solve_word_problem(axioms, (inv(inv(x)), x), precedence=precedence))


if __name__ == "__main__":
    unittest.main()
