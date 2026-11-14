"""
Unit tests for First-Order Prenex Conversion, Skolemization, Herbrand Universe,
Herbrand Expansion Prover, Robinson Unification, and Free-Variable Semantic Tableaux.
"""

import unittest
from FirstOrder import (
    Var, Const, Fn, Pred, Eq, FoBot, FoTop, FoNot, FoConj, FoDisj, FoImpl, FoIff,
    Forall, Exists, FoLiteral, FoClause,
)
from Herbrand import (
    robinson_unify, robinson_unify_all, robinson_unify_predicates, robinson_unify_atoms,
    FolSignature, extract_fol_signature,
    is_prenex, split_prenex, to_prenex_by_movement, prenex_normal_form,
    skolemize_formula, herbrandize_formula, skolemize_to_clauses,
    herbrand_universe_level, herbrand_universe_strata, herbrand_universe_stream, herbrand_universe,
    herbrand_base_level, herbrand_base,
    ground_instances_of_clause, ground_instances_of_clauses,
    HerbrandExpansionProver, prove_by_herbrand_expansion,
    FvSignedFormula, FvTableauBranch, FreeVariableTableau, prove_by_free_variable_tableau,
)


class TestPrenexConversion(unittest.TestCase):
    """Test Prenex Normal Form conversion and quantifier movement rules."""

    def test_already_prenex(self):
        f1 = Pred("P", [Var("x")])
        self.assertTrue(is_prenex(f1))
        quants, matrix = split_prenex(f1)
        self.assertEqual(quants, [])
        self.assertEqual(matrix, f1)

        f2 = Forall("x", Exists("y", Pred("R", [Var("x"), Var("y")])))
        self.assertTrue(is_prenex(f2))
        quants, matrix = split_prenex(f2)
        self.assertEqual(quants, [("forall", "x"), ("exists", "y")])
        self.assertEqual(matrix, Pred("R", [Var("x"), Var("y")]))

    def test_quantifier_movement_negation(self):
        # ~forall x. P(x)  ===  exists x. ~P(x)
        f1 = FoNot(Forall("x", Pred("P", [Var("x")])))
        pnf1 = prenex_normal_form(f1)
        self.assertTrue(is_prenex(pnf1))
        self.assertIsInstance(pnf1, Exists)
        self.assertEqual(pnf1.var, "x")
        self.assertIsInstance(pnf1.body, FoNot)

        # ~exists x. P(x)  ===  forall x. ~P(x)
        f2 = FoNot(Exists("x", Pred("P", [Var("x")])))
        pnf2 = prenex_normal_form(f2)
        self.assertTrue(is_prenex(pnf2))
        self.assertIsInstance(pnf2, Forall)
        self.assertEqual(pnf2.var, "x")

    def test_quantifier_movement_conjunction_and_disjunction(self):
        p = Pred("P", [Var("x")])
        q = Pred("Q", [Const("a")])

        # (forall x. P(x)) & Q  ===  forall x. (P(x) & Q)
        f1 = FoConj(Forall("x", p), q)
        pnf1 = prenex_normal_form(f1)
        self.assertTrue(is_prenex(pnf1))
        self.assertIsInstance(pnf1, Forall)

        # P | (exists x. Q(x))  ===  exists x. (P | Q(x))
        f2 = FoDisj(q, Exists("x", p))
        pnf2 = prenex_normal_form(f2)
        self.assertTrue(is_prenex(pnf2))
        self.assertIsInstance(pnf2, Exists)

    def test_quantifier_movement_implication_polarity_flip(self):
        p = Pred("P", [Var("x")])
        q = Pred("Q", [Const("a")])

        # Antecedent flips: (forall x. P(x)) >> Q  ===  exists x. (P(x) >> Q)
        f1 = FoImpl(Forall("x", p), q)
        pnf1 = prenex_normal_form(f1)
        self.assertTrue(is_prenex(pnf1))
        self.assertIsInstance(pnf1, Exists)

        # Antecedent flips: (exists x. P(x)) >> Q  ===  forall x. (P(x) >> Q)
        f2 = FoImpl(Exists("x", p), q)
        pnf2 = prenex_normal_form(f2)
        self.assertTrue(is_prenex(pnf2))
        self.assertIsInstance(pnf2, Forall)

        # Consequent keeps quantifier: P >> (forall x. Q(x))  ===  forall x. (P >> Q(x))
        f3 = FoImpl(q, Forall("x", p))
        pnf3 = prenex_normal_form(f3)
        self.assertTrue(is_prenex(pnf3))
        self.assertIsInstance(pnf3, Forall)

    def test_variable_capture_avoidance(self):
        # (forall x. P(x)) & (exists x. Q(x))
        f = FoConj(Forall("x", Pred("P", [Var("x")])), Exists("x", Pred("Q", [Var("x")])))
        pnf = prenex_normal_form(f)
        self.assertTrue(is_prenex(pnf))
        quants, matrix = split_prenex(pnf)
        self.assertEqual(len(quants), 2)
        var_names = [v for _, v in quants]
        # Variables must be distinct
        self.assertEqual(len(set(var_names)), 2)


class TestSkolemizationAndHerbrandization(unittest.TestCase):
    """Test Skolemization, Herbrandization, and SNF clause generation."""

    def test_top_level_existential_skolem_constant(self):
        # exists x. P(x)  =>  P(sk_c_1)
        f = Exists("x", Pred("P", [Var("x")]))
        sk = skolemize_formula(f)
        self.assertIsInstance(sk, Pred)
        self.assertEqual(len(sk.args), 1)
        self.assertIsInstance(sk.args[0], Const)
        self.assertTrue(sk.args[0].name.startswith("sk_c_"))

    def test_governed_existential_skolem_function(self):
        # forall x. exists y. R(x, y)  =>  forall x. R(x, sk_f_1(x))
        f = Forall("x", Exists("y", Pred("R", [Var("x"), Var("y")])))
        sk = skolemize_formula(f)
        self.assertIsInstance(sk, Forall)
        matrix = sk.body
        self.assertIsInstance(matrix, Pred)
        self.assertEqual(matrix.args[0], Var("x"))
        self.assertIsInstance(matrix.args[1], Fn)
        self.assertEqual(matrix.args[1].args, (Var("x"),))

    def test_multiple_governing_universals(self):
        # forall x. forall y. exists z. T(x, y, z)
        f = Forall("x", Forall("y", Exists("z", Pred("T", [Var("x"), Var("y"), Var("z")]))))
        sk = skolemize_formula(f, drop_universal=True)
        self.assertIsInstance(sk, Pred)
        self.assertIsInstance(sk.args[2], Fn)
        self.assertEqual(len(sk.args[2].args), 2)

    def test_herbrandize_dual_validity(self):
        # forall x. P(x)  =>  P(hb_c_1) (Herbrand constant replaces universal)
        f1 = Forall("x", Pred("P", [Var("x")]))
        hb1 = herbrandize_formula(f1)
        self.assertIsInstance(hb1, Pred)
        self.assertIsInstance(hb1.args[0], Const)
        self.assertTrue(hb1.args[0].name.startswith("hb_c_"))

        # exists x. forall y. R(x, y)  =>  exists x. R(x, hb_f_1(x))
        f2 = Exists("x", Forall("y", Pred("R", [Var("x"), Var("y")])))
        hb2 = herbrandize_formula(f2)
        self.assertIsInstance(hb2, Exists)
        matrix = hb2.body
        self.assertIsInstance(matrix.args[1], Fn)
        self.assertEqual(matrix.args[1].args, (Var("x"),))

    def test_skolemize_to_clauses(self):
        f = Forall("x", FoConj(Pred("P", [Var("x")]), Pred("Q", [Var("x")])))
        clauses = skolemize_to_clauses(f)
        self.assertEqual(len(clauses), 2)
        all_preds = {next(iter(c.literals)).pred.name for c in clauses}
        self.assertEqual(all_preds, {"P", "Q"})


class TestHerbrandUniverseAndBase(unittest.TestCase):
    """Test signature extraction, Herbrand Universe levels/strata/streams, and Herbrand Base."""

    def test_signature_extraction(self):
        f = FoImpl(Pred("P", [Const("a"), Fn("f", [Var("x")])]), Pred("Q", [Const("b")]))
        sig = extract_fol_signature(f)
        const_names = {c.name for c in sig.constants}
        self.assertEqual(const_names, {"a", "b"})
        self.assertEqual(sig.functions, {"f": 1})
        self.assertEqual(sig.predicates, {"P": 2, "Q": 1})

    def test_signature_default_constant(self):
        # Formula with no constants
        f = Forall("x", Pred("P", [Var("x")]))
        sig = extract_fol_signature(f, default_constant="c_0")
        const_names = {c.name for c in sig.constants}
        self.assertEqual(const_names, {"c_0"})

    def test_herbrand_universe_constants_only(self):
        consts = {Const("a"), Const("b")}
        funcs = {}
        h0 = herbrand_universe_level(consts, funcs, level=0)
        h1 = herbrand_universe_level(consts, funcs, level=2)
        self.assertEqual(len(h0), 2)
        self.assertEqual(len(h1), 2)
        self.assertEqual(h0, h1)

    def test_herbrand_universe_unary_function(self):
        consts = {Const("a")}
        funcs = {"f": 1}
        h0 = herbrand_universe_level(consts, funcs, level=0)
        self.assertEqual([str(t) for t in h0], ["a"])

        h1 = herbrand_universe_level(consts, funcs, level=1)
        self.assertEqual([str(t) for t in h1], ["a", "f(a)"])

        h2 = herbrand_universe_level(consts, funcs, level=2)
        self.assertEqual([str(t) for t in h2], ["a", "f(a)", "f(f(a))"])

    def test_herbrand_universe_binary_function(self):
        consts = {Const("a")}
        funcs = {"g": 2}
        h0 = herbrand_universe_level(consts, funcs, level=0)
        self.assertEqual([str(t) for t in h0], ["a"])

        h1 = herbrand_universe_level(consts, funcs, level=1)
        self.assertEqual([str(t) for t in h1], ["a", "g(a, a)"])

    def test_herbrand_universe_strata(self):
        consts = {Const("a")}
        funcs = {"f": 1}
        strata = herbrand_universe_strata(consts, funcs, max_level=2)
        self.assertEqual(len(strata), 3)
        self.assertEqual([str(t) for t in strata[0]], ["a"])
        self.assertEqual([str(t) for t in strata[1]], ["f(a)"])
        self.assertEqual([str(t) for t in strata[2]], ["f(f(a))"])

    def test_herbrand_universe_stream(self):
        consts = {Const("a")}
        funcs = {"f": 1}
        stream = herbrand_universe_stream(consts, funcs)
        first_four = [next(stream) for _ in range(4)]
        self.assertEqual([str(t) for t in first_four], ["a", "f(a)", "f(f(a))", "f(f(f(a)))"])

    def test_herbrand_base_generation(self):
        terms = [Const("a"), Const("b")]
        preds = {"P": 1, "R": 2}
        base = herbrand_base_level(preds, terms)
        base_strs = {str(a) for a in base}
        expected = {
            "P(a)", "P(b)",
            "R(a, a)", "R(a, b)", "R(b, a)", "R(b, b)"
        }
        self.assertEqual(base_strs, expected)


class TestRobinsonUnification(unittest.TestCase):
    """Test Robinson Syntactic Unification with Occurs-Check."""

    def test_identical_terms(self):
        x = Var("x")
        self.assertEqual(robinson_unify(x, x), {})
        c = Const("c")
        self.assertEqual(robinson_unify(c, c), {})
        fn = Fn("f", [x, c])
        self.assertEqual(robinson_unify(fn, fn), {})

    def test_variable_with_constant_and_term(self):
        x = Var("x")
        a = Const("a")
        self.assertEqual(robinson_unify(x, a), {"x": a})

        y = Var("y")
        fy = Fn("f", [y])
        self.assertEqual(robinson_unify(x, fy), {"x": fy})

    def test_compound_unification(self):
        x, y = Var("x"), Var("y")
        a, b = Const("a"), Const("b")
        t1 = Fn("f", [x, b])
        t2 = Fn("f", [a, y])
        mgu = robinson_unify(t1, t2)
        self.assertEqual(mgu, {"x": a, "y": b})

    def test_nested_unification(self):
        x, y, z = Var("x"), Var("y"), Var("z")
        t1 = Fn("h", [x, Fn("f", [x])])
        t2 = Fn("h", [Fn("g", [y]), z])
        mgu = robinson_unify(t1, t2)
        self.assertIsNotNone(mgu)
        self.assertEqual(t1.subst(mgu), t2.subst(mgu))

    def test_occurs_check(self):
        x = Var("x")
        fx = Fn("f", [x])
        # Direct occurs check: x cannot unify with f(x)
        self.assertIsNone(robinson_unify(x, fx))
        self.assertIsNone(robinson_unify(fx, x))

        # Deep occurs check: x cannot unify with g(y, f(x))
        y = Var("y")
        deep = Fn("g", [y, Fn("f", [x])])
        self.assertIsNone(robinson_unify(x, deep))

    def test_clashing_function_names_or_arities(self):
        x = Var("x")
        self.assertIsNone(robinson_unify(Fn("f", [x]), Fn("g", [x])))
        self.assertIsNone(robinson_unify(Fn("f", [x]), Fn("f", [x, x])))

    def test_predicate_and_atom_unification(self):
        x, y = Var("x"), Var("y")
        a = Const("a")
        p1 = Pred("P", [x, Fn("f", [x])])
        p2 = Pred("P", [a, y])
        mgu = robinson_unify_predicates(p1, p2)
        self.assertEqual(mgu, {"x": a, "y": Fn("f", [a])})

        eq1 = Eq(x, a)
        eq2 = Eq(Const("b"), y)
        mgu_eq = robinson_unify_atoms(eq1, eq2)
        self.assertEqual(mgu_eq, {"x": Const("b"), "y": a})

    def test_robinson_unify_all(self):
        x, y, z = Var("x"), Var("y"), Var("z")
        a = Const("a")
        terms = [x, y, z, a]
        mgu = robinson_unify_all(terms)
        self.assertEqual(mgu, {"x": a, "y": a, "z": a})


class TestHerbrandExpansionProver(unittest.TestCase):
    """Test Herbrand Expansion Prover and ground instance refutations."""

    def test_ground_instance_generation(self):
        x = Var("x")
        clause = FoClause([FoLiteral(Pred("P", [x]), True)])
        terms = [Const("a"), Const("b")]
        instances = ground_instances_of_clause(clause, terms)
        self.assertEqual(len(instances), 2)
        inst_strs = {str(c) for c in instances}
        self.assertEqual(inst_strs, {"P(a)", "P(b)"})

    def test_herbrand_expansion_level_0_refutation(self):
        # Clauses:
        # C1: P(a)
        # C2: ~P(x) | Q(x)
        # C3: ~Q(a)
        a = Const("a")
        x = Var("x")
        c1 = FoClause([FoLiteral(Pred("P", [a]), True)])
        c2 = FoClause([FoLiteral(Pred("P", [x]), False), FoLiteral(Pred("Q", [x]), True)])
        c3 = FoClause([FoLiteral(Pred("Q", [a]), False)])

        prover = HerbrandExpansionProver([c1, c2, c3])
        proved, log = prover.prove(max_level=0)
        self.assertTrue(proved)

    def test_herbrand_expansion_level_1_refutation(self):
        # Requires ground term f(a):
        # C1: P(a)
        # C2: ~P(x) | P(f(x))
        # C3: ~P(f(a))
        a = Const("a")
        x = Var("x")
        c1 = FoClause([FoLiteral(Pred("P", [a]), True)])
        c2 = FoClause([FoLiteral(Pred("P", [x]), False), FoLiteral(Pred("P", [Fn("f", [x])]), True)])
        c3 = FoClause([FoLiteral(Pred("P", [Fn("f", [a])]), False)])

        prover = HerbrandExpansionProver([c1, c2, c3])
        proved, log = prover.prove(max_level=1)
        self.assertTrue(proved)

    def test_herbrand_expansion_validity_syllogism(self):
        # (forall x. Man(x) >> Mortal(x)) & Man(socrates) >> Mortal(socrates)
        x = Var("x")
        s = Const("socrates")
        man = lambda t: Pred("Man", [t])
        mortal = lambda t: Pred("Mortal", [t])

        premise1 = Forall("x", FoImpl(man(x), mortal(x)))
        premise2 = man(s)
        conclusion = mortal(s)
        syllogism = FoImpl(FoConj(premise1, premise2), conclusion)

        proved, log = prove_by_herbrand_expansion(syllogism)
        self.assertTrue(proved)

    def test_herbrand_expansion_transitivity(self):
        # Transitivity of R:
        # (forall x y z. R(x,y) & R(y,z) >> R(x,z)) & R(a,b) & R(b,c) >> R(a,c)
        x, y, z = Var("x"), Var("y"), Var("z")
        a, b, c = Const("a"), Const("b"), Const("c")
        r = lambda t1, t2: Pred("R", [t1, t2])

        trans_ax = Forall("x", Forall("y", Forall("z", FoImpl(FoConj(r(x, y), r(y, z)), r(x, z)))))
        hyp = FoConj(trans_ax, FoConj(r(a, b), r(b, c)))
        goal = FoImpl(hyp, r(a, c))

        proved, log = prove_by_herbrand_expansion(goal)
        self.assertTrue(proved)


class TestFreeVariableSemanticTableaux(unittest.TestCase):
    """Test Free-Variable Semantic Tableaux with Robinson Unification."""

    def test_tableau_simple_validity(self):
        # forall x. P(x)  >>  P(a)
        x = Var("x")
        a = Const("a")
        goal = FoImpl(Forall("x", Pred("P", [x])), Pred("P", [a]))
        proved, log = prove_by_free_variable_tableau(goal)
        self.assertTrue(proved)

    def test_tableau_syllogism(self):
        x = Var("x")
        s = Const("socrates")
        man = lambda t: Pred("Man", [t])
        mortal = lambda t: Pred("Mortal", [t])

        syllogism = FoImpl(
            FoConj(Forall("x", FoImpl(man(x), mortal(x))), man(s)),
            mortal(s)
        )
        proved, log = prove_by_free_variable_tableau(syllogism)
        self.assertTrue(proved)

    def test_tableau_existential_generalization(self):
        # P(a)  >>  exists x. P(x)
        a = Const("a")
        goal = FoImpl(Pred("P", [a]), Exists("x", Pred("P", [Var("x")])))
        proved, log = prove_by_free_variable_tableau(goal)
        self.assertTrue(proved)

    def test_tableau_valid_quantifier_swap(self):
        # (exists x. forall y. R(x, y))  >>  (forall y. exists x. R(x, y))
        x, y = Var("x"), Var("y")
        r = lambda t1, t2: Pred("R", [t1, t2])
        goal = FoImpl(
            Exists("x", Forall("y", r(x, y))),
            Forall("y", Exists("x", r(x, y)))
        )
        proved, log = prove_by_free_variable_tableau(goal)
        self.assertTrue(proved)

    def test_tableau_invalid_quantifier_swap_fails(self):
        # (forall x. exists y. R(x, y))  >>  (exists y. forall x. R(x, y)) is NOT valid!
        # Occurs check prevents closing!
        x, y = Var("x"), Var("y")
        r = lambda t1, t2: Pred("R", [t1, t2])
        invalid_goal = FoImpl(
            Forall("x", Exists("y", r(x, y))),
            Exists("y", Forall("x", r(x, y)))
        )
        proved, log = prove_by_free_variable_tableau(invalid_goal, max_steps=20)
        self.assertFalse(proved)

    def test_tableau_drinker_paradox(self):
        # exists x. (D(x) >> forall y. D(y))
        x, y = Var("x"), Var("y")
        d = lambda t: Pred("D", [t])
        drinker = Exists("x", FoImpl(d(x), Forall("y", d(y))))
        proved, log = prove_by_free_variable_tableau(drinker, max_gamma_instances=2)
        self.assertTrue(proved)

    def test_tableau_branching_and_unification(self):
        # (P(a) | P(b)) & (forall x. P(x) >> Q(x))  >>  (Q(a) | Q(b))
        x = Var("x")
        a, b = Const("a"), Const("b")
        p = lambda t: Pred("P", [t])
        q = lambda t: Pred("Q", [t])

        hyp = FoConj(FoDisj(p(a), p(b)), Forall("x", FoImpl(p(x), q(x))))
        conc = FoDisj(q(a), q(b))
        goal = FoImpl(hyp, conc)

        proved, log = prove_by_free_variable_tableau(goal, max_gamma_instances=2)
        self.assertTrue(proved)

    def test_tableau_equality_reflexivity(self):
        # forall x. (x = x)
        x = Var("x")
        goal = Forall("x", Eq(x, x))
        proved, log = prove_by_free_variable_tableau(goal)
        self.assertTrue(proved)


if __name__ == "__main__":
    unittest.main()
