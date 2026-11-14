"""
First-Order Equational Reasoning, Congruence Closure, Paramodulation,
and Knuth-Bendix Term Rewriting System (TRS) Engine.

This module provides:
1. Subterm position navigation and term/literal replacement.
2. Formal equality predicate axioms (Reflexivity, Symmetry, Transitivity)
   and Congruence axioms for arbitrary first-order signatures.
3. Polynomial-time ground Congruence Closure decision procedure
   using Union-Find with signature tables and parent use lists.
4. Paramodulation inference rule and Equality Resolution (reflexivity resolution)
   for refutational first-order equational resolution theorem proving.
5. Term Rewriting System (TRS):
   - Syntactic pattern matching
   - Term simplification and normalization
   - Lexicographic Path Ordering (LPO) well-founded reduction ordering
   - Critical pair generation
   - Knuth-Bendix critical pair completion for solving equational word problems
"""

from typing import Union, Dict, Set, List, Tuple, Optional, Any
from FirstOrder import (
    Term, Var, Const, Fn, Pred, Eq, FoFormula, FoBot, FoTop, FoNot,
    FoConj, FoDisj, FoImpl, FoIff, Forall, Exists,
    FoLiteral, FoClause, resolve_clauses, factor_clause,
    unify_terms, unify_predicates, formula_to_clauses
)


# -------------------------------------------------------------
# Section 1: Subterm Position Navigation and Manipulation
# -------------------------------------------------------------

def get_subterm(term: Term, pos: Tuple[int, ...]) -> Term:
    """Retrieve the subterm at tree position pos."""
    if not pos:
        return term
    if not isinstance(term, Fn):
        raise IndexError(f"Cannot navigate position {pos} in non-function term {term}")
    arg_idx = pos[0]
    if arg_idx < 0 or arg_idx >= len(term.args):
        raise IndexError(f"Argument index {arg_idx} out of range in {term}")
    return get_subterm(term.args[arg_idx], pos[1:])


def replace_subterm(term: Term, pos: Tuple[int, ...], replacement: Term) -> Term:
    """Return a new term with the subterm at position pos replaced by replacement."""
    if not pos:
        return replacement
    if not isinstance(term, Fn):
        raise IndexError(f"Cannot replace at position {pos} in non-function term {term}")
    arg_idx = pos[0]
    if arg_idx < 0 or arg_idx >= len(term.args):
        raise IndexError(f"Argument index {arg_idx} out of range in {term}")
    new_args = list(term.args)
    new_args[arg_idx] = replace_subterm(new_args[arg_idx], pos[1:], replacement)
    return Fn(term.name, new_args)


def all_subterm_positions(term: Term, non_variable_only: bool = False) -> List[Tuple[Tuple[int, ...], Term]]:
    """
    Return all (position, subterm) pairs for term.
    If non_variable_only is True, skip positions corresponding to variables.
    """
    positions: List[Tuple[Tuple[int, ...], Term]] = []

    def _traverse(t: Term, current_pos: Tuple[int, ...]):
        if not (non_variable_only and isinstance(t, Var)):
            positions.append((current_pos, t))
        if isinstance(t, Fn):
            for i, arg in enumerate(t.args):
                _traverse(arg, current_pos + (i,))

    _traverse(term, ())
    return positions


def all_literal_positions(lit: FoLiteral, non_variable_only: bool = True) -> List[Tuple[Tuple[int, ...], Term]]:
    """
    Return all (position, subterm) pairs in literal lit.
    Positions are formatted as (arg_idx, *subterm_pos).
    """
    positions: List[Tuple[Tuple[int, ...], Term]] = []
    for arg_idx, arg in enumerate(lit.pred.args):
        for term_pos, sub in all_subterm_positions(arg, non_variable_only=non_variable_only):
            positions.append(((arg_idx,) + term_pos, sub))
    return positions


def replace_literal_subterm(lit: FoLiteral, pos: Tuple[int, ...], replacement: Term) -> FoLiteral:
    """Return a new FoLiteral with subterm at pos replaced by replacement."""
    if not pos:
        raise ValueError("Cannot replace entire literal with a term")
    arg_idx = pos[0]
    term_pos = pos[1:]
    if arg_idx < 0 or arg_idx >= len(lit.pred.args):
        raise IndexError(f"Literal argument index {arg_idx} out of range in {lit}")
    new_args = list(lit.pred.args)
    new_args[arg_idx] = replace_subterm(new_args[arg_idx], term_pos, replacement)
    new_pred = Pred(lit.pred.name, new_args)
    return FoLiteral(new_pred, lit.is_positive)


def is_equality_literal(lit: FoLiteral) -> Tuple[bool, Optional[Term], Optional[Term]]:
    """
    Check if a literal is an equality literal (positive or negative).
    Returns (is_eq, left_term, right_term).
    """
    if lit.pred.name == "=" and len(lit.pred.args) == 2:
        return True, lit.pred.args[0], lit.pred.args[1]
    return False, None, None


def make_equality_literal(left: Term, right: Term, is_positive: bool = True) -> FoLiteral:
    """Construct an equality FoLiteral."""
    return FoLiteral(Pred("=", [left, right]), is_positive)


# -------------------------------------------------------------
# Section 2: Formal Equality Axioms and Congruence Generators
# -------------------------------------------------------------

def equality_reflexivity_axiom() -> FoFormula:
    """Return formal reflexivity axiom: forall x. (x = x)."""
    x = Var("x")
    return Forall("x", Eq(x, x))


def equality_symmetry_axiom() -> FoFormula:
    """Return formal symmetry axiom: forall x y. (x = y -> y = x)."""
    x = Var("x")
    y = Var("y")
    return Forall("x", Forall("y", Eq(x, y) >> Eq(y, x)))


def equality_transitivity_axiom() -> FoFormula:
    """Return formal transitivity axiom: forall x y z. ((x = y & y = z) -> x = z)."""
    x = Var("x")
    y = Var("y")
    z = Var("z")
    return Forall("x", Forall("y", Forall("z", (Eq(x, y) & Eq(y, z)) >> Eq(x, z))))


def function_congruence_axiom(func_name: str, arity: int) -> FoFormula:
    """
    Return congruence axiom for an n-ary function symbol f:
    forall x_1..x_n y_1..y_n. (x_1 = y_1 & ... & x_n = y_n) -> f(x_1..x_n) = f(y_1..y_n).
    """
    if arity <= 0:
        raise ValueError(f"Function congruence requires arity >= 1, got {arity}")

    xs = [Var(f"x_{i}") for i in range(1, arity + 1)]
    ys = [Var(f"y_{i}") for i in range(1, arity + 1)]

    antecedent: Optional[FoFormula] = None
    for x_i, y_i in zip(xs, ys):
        eq_i = Eq(x_i, y_i)
        antecedent = eq_i if antecedent is None else (antecedent & eq_i)

    consequent = Eq(Fn(func_name, xs), Fn(func_name, ys))
    body = antecedent >> consequent

    res = body
    for v in reversed(xs + ys):
        res = Forall(v.name, res)
    return res


def predicate_congruence_axiom(pred_name: str, arity: int) -> FoFormula:
    """
    Return congruence axiom for an n-ary predicate symbol P (where P != '='):
    forall x_1..x_n y_1..y_n. (x_1 = y_1 & ... & x_n = y_n & P(x_1..x_n)) -> P(y_1..y_n).
    """
    if arity <= 0:
        raise ValueError(f"Predicate congruence requires arity >= 1, got {arity}")

    xs = [Var(f"x_{i}") for i in range(1, arity + 1)]
    ys = [Var(f"y_{i}") for i in range(1, arity + 1)]

    antecedent: Optional[FoFormula] = None
    for x_i, y_i in zip(xs, ys):
        eq_i = Eq(x_i, y_i)
        antecedent = eq_i if antecedent is None else (antecedent & eq_i)

    p_xs = Pred(pred_name, xs)
    antecedent = p_xs if antecedent is None else (antecedent & p_xs)

    consequent = Pred(pred_name, ys)
    body = antecedent >> consequent

    res = body
    for v in reversed(xs + ys):
        res = Forall(v.name, res)
    return res


def extract_signature_from_formulas(formulas: List[FoFormula]) -> Tuple[Dict[str, int], Dict[str, int]]:
    """
    Extract function and predicate signatures (name to arity) occurring in a list of formulas.
    Ignores the equality predicate '=' in predicate signatures.
    """
    functions: Dict[str, int] = {}
    predicates: Dict[str, int] = {}

    def _collect_term(t: Term):
        if isinstance(t, Fn):
            functions[t.name] = len(t.args)
            for a in t.args:
                _collect_term(a)

    def _collect_form(f: FoFormula):
        if isinstance(f, Pred):
            if f.name != "=" and f.args:
                predicates[f.name] = len(f.args)
            for a in f.args:
                _collect_term(a)
        elif isinstance(f, Eq):
            _collect_term(f.left)
            _collect_term(f.right)
        elif isinstance(f, FoNot):
            _collect_form(f.inner)
        elif isinstance(f, (FoConj, FoDisj, FoImpl, FoIff)):
            _collect_form(f.left)
            _collect_form(f.right)
        elif isinstance(f, (Forall, Exists)):
            _collect_form(f.body)

    for form in formulas:
        _collect_form(form)
    return functions, predicates


def extract_signature_from_clauses(clauses: List[FoClause]) -> Tuple[Dict[str, int], Dict[str, int]]:
    """Extract function and predicate signatures occurring in a list of FoClauses."""
    functions: Dict[str, int] = {}
    predicates: Dict[str, int] = {}

    def _collect_term(t: Term):
        if isinstance(t, Fn):
            functions[t.name] = len(t.args)
            for a in t.args:
                _collect_term(a)

    for c in clauses:
        for lit in c.literals:
            p = lit.pred
            if p.name != "=" and p.args:
                predicates[p.name] = len(p.args)
            for a in p.args:
                _collect_term(a)

    return functions, predicates


def generate_equality_axioms(signature: Tuple[Dict[str, int], Dict[str, int]]) -> List[FoFormula]:
    """
    Generate all first-order equality axioms for a given signature (functions, predicates):
    1. Reflexivity: forall x. x = x
    2. Symmetry: forall x y. x = y -> y = x
    3. Transitivity: forall x y z. (x = y & y = z) -> x = z
    4. Function congruence for each function symbol f
    5. Predicate congruence for each predicate symbol P != '='
    """
    functions, predicates = signature
    axioms = [
        equality_reflexivity_axiom(),
        equality_symmetry_axiom(),
        equality_transitivity_axiom()
    ]
    for fn_name, arity in functions.items():
        if arity > 0:
            axioms.append(function_congruence_axiom(fn_name, arity))
    for pred_name, arity in predicates.items():
        if arity > 0 and pred_name != "=":
            axioms.append(predicate_congruence_axiom(pred_name, arity))
    return axioms


def generate_equality_clauses(signature: Tuple[Dict[str, int], Dict[str, int]]) -> List[FoClause]:
    """
    Generate the clausal forms of the equality axioms for a given signature.
    """
    clauses: List[FoClause] = []

    # Reflexivity: [x = x]
    x = Var("x")
    clauses.append(FoClause([make_equality_literal(x, x, is_positive=True)]))

    # Symmetry: [x != y | y = x]
    y = Var("y")
    clauses.append(FoClause([
        make_equality_literal(x, y, is_positive=False),
        make_equality_literal(y, x, is_positive=True)
    ]))

    # Transitivity: [x != y | y != z | x = z]
    z = Var("z")
    clauses.append(FoClause([
        make_equality_literal(x, y, is_positive=False),
        make_equality_literal(y, z, is_positive=False),
        make_equality_literal(x, z, is_positive=True)
    ]))

    functions, predicates = signature

    # Function congruence
    for fn_name, arity in functions.items():
        if arity > 0:
            xs = [Var(f"x_{i}") for i in range(1, arity + 1)]
            ys = [Var(f"y_{i}") for i in range(1, arity + 1)]
            lits = [make_equality_literal(xi, yi, is_positive=False) for xi, yi in zip(xs, ys)]
            lits.append(make_equality_literal(Fn(fn_name, xs), Fn(fn_name, ys), is_positive=True))
            clauses.append(FoClause(lits))

    # Predicate congruence
    for pred_name, arity in predicates.items():
        if arity > 0 and pred_name != "=":
            xs = [Var(f"x_{i}") for i in range(1, arity + 1)]
            ys = [Var(f"y_{i}") for i in range(1, arity + 1)]
            lits = [make_equality_literal(xi, yi, is_positive=False) for xi, yi in zip(xs, ys)]
            lits.append(FoLiteral(Pred(pred_name, xs), is_positive=False))
            lits.append(FoLiteral(Pred(pred_name, ys), is_positive=True))
            clauses.append(FoClause(lits))

    return clauses


# -------------------------------------------------------------
# Section 3: Polynomial-Time Ground Congruence Closure Algorithm
# -------------------------------------------------------------

class CongruenceClosure:
    """
    Polynomial-time ground Congruence Closure decision procedure.
    Maintains equivalence classes of ground terms with Union-Find,
    signature tables, and use lists to propagate functional congruences.
    """

    def __init__(self):
        self.node_to_term: Dict[int, Term] = {}
        self.term_to_node: Dict[Term, int] = {}
        self.parent: Dict[int, int] = {}
        self.size: Dict[int, int] = {}
        self.node_name: Dict[int, str] = {}
        self.node_args: Dict[int, Tuple[int, ...]] = {}
        self.signature_table: Dict[Tuple[str, Tuple[int, ...]], int] = {}
        self.use_list: Dict[int, Set[int]] = {}
        self.node_sig: Dict[int, Tuple[str, Tuple[int, ...]]] = {}
        self.next_id: int = 0

    def find(self, u: int) -> int:
        """Find representative with path compression."""
        path = []
        while self.parent[u] != u:
            path.append(u)
            u = self.parent[u]
        for p in path:
            self.parent[p] = u
        return u

    def get_sig(self, u: int) -> Tuple[str, Tuple[int, ...]]:
        """Compute current signature for node u based on argument representatives."""
        return (self.node_name[u], tuple(self.find(a) for a in self.node_args[u]))

    def add_term(self, term: Term) -> int:
        """Register a term and its subterms in the congruence closure DAG."""
        if term in self.term_to_node:
            return self.term_to_node[term]

        if isinstance(term, (Const, Var)):
            u = self.next_id
            self.next_id += 1
            self.node_to_term[u] = term
            self.term_to_node[term] = u
            self.parent[u] = u
            self.size[u] = 1
            self.node_name[u] = term.name
            self.node_args[u] = ()
            self.use_list[u] = set()

            sig = (term.name, ())
            self.node_sig[u] = sig
            if sig in self.signature_table:
                existing = self.signature_table[sig]
                self.parent[u] = existing
            else:
                self.signature_table[sig] = u
            return u

        elif isinstance(term, Fn):
            arg_ids = tuple(self.add_term(arg) for arg in term.args)
            u = self.next_id
            self.next_id += 1
            self.node_to_term[u] = term
            self.term_to_node[term] = u
            self.parent[u] = u
            self.size[u] = 1
            self.node_name[u] = term.name
            self.node_args[u] = arg_ids
            self.use_list[u] = set()

            for aid in arg_ids:
                r = self.find(aid)
                self.use_list[r].add(u)

            sig = self.get_sig(u)
            self.node_sig[u] = sig
            if sig in self.signature_table:
                existing = self.signature_table[sig]
                self.merge_ids(u, existing)
            else:
                self.signature_table[sig] = u
            return u
        else:
            raise TypeError(f"Unsupported term type: {type(term)}")

    def merge_ids(self, id1: int, id2: int) -> None:
        """Merge equivalence classes of node id1 and node id2 and propagate congruences."""
        queue: List[Tuple[int, int]] = [(id1, id2)]
        while queue:
            u, v = queue.pop(0)
            ru = self.find(u)
            rv = self.find(v)
            if ru == rv:
                continue

            if self.size[ru] < self.size[rv]:
                ru, rv = rv, ru

            parents_rv = list(self.use_list[rv])
            self.parent[rv] = ru
            self.size[ru] += self.size[rv]

            for p in parents_rv:
                old_sig = self.node_sig.get(p)
                if old_sig and self.signature_table.get(old_sig) == p:
                    del self.signature_table[old_sig]

                new_sig = self.get_sig(p)
                self.node_sig[p] = new_sig
                if new_sig in self.signature_table:
                    target = self.signature_table[new_sig]
                    if self.find(target) != self.find(p):
                        queue.append((p, target))
                else:
                    self.signature_table[new_sig] = p
                self.use_list[ru].add(p)

            self.use_list[rv].clear()

    def merge(self, t1: Term, t2: Term) -> None:
        """Assert equality between terms t1 and t2 in the congruence closure."""
        u = self.add_term(t1)
        v = self.add_term(t2)
        self.merge_ids(u, v)

    def are_equal(self, t1: Term, t2: Term) -> bool:
        """Check if terms t1 and t2 belong to the same congruence equivalence class."""
        u = self.add_term(t1)
        v = self.add_term(t2)
        return self.find(u) == self.find(v)

    def get_representative(self, term: Term) -> Term:
        """Return the canonical term representative for term."""
        u = self.add_term(term)
        r = self.find(u)
        return self.node_to_term[r]

    def get_classes(self) -> List[Set[Term]]:
        """Return all congruence equivalence classes of registered terms."""
        groups: Dict[int, Set[Term]] = {}
        for term, node_id in self.term_to_node.items():
            r = self.find(node_id)
            groups.setdefault(r, set()).add(term)
        return list(groups.values())


def check_ground_validity(hypotheses: List[Tuple[Term, Term]], query: Tuple[Term, Term]) -> bool:
    """
    Check if hypotheses |= (query[0] = query[1]) in first-order equational logic.
    Polynomial-time decision procedure via Congruence Closure.
    """
    cc = CongruenceClosure()
    for s, t in hypotheses:
        cc.merge(s, t)
    return cc.are_equal(query[0], query[1])


def check_ground_satisfiability(equations: List[Tuple[Term, Term]], disequations: List[Tuple[Term, Term]]) -> bool:
    """
    Check if the conjunction of equations (s_i = t_i) and disequations (u_j != v_j)
    is satisfiable in first-order logic with equality.
    """
    cc = CongruenceClosure()
    for s, t in equations:
        cc.merge(s, t)
    for u, v in disequations:
        if cc.are_equal(u, v):
            return False
    return True


# -------------------------------------------------------------
# Section 4: Paramodulation and First-Order Equational Resolution Prover
# -------------------------------------------------------------

def paramodulate(c1: FoClause, c2: FoClause, step: int = 0) -> List[FoClause]:
    """
    Compute all paramodulants between from-clause c1 and into-clause c2.
    For each positive equality s = t in c1, unifies s (or t) with a non-variable
    subterm u in c2 at position p, deriving:
      ((c1 \\ {s = t}) | (c2 \\ {L}) | L[p := t]) sigma.
    """
    c1_std = c1.standardize_apart(f"PM1_{step}")
    c2_std = c2.standardize_apart(f"PM2_{step}")

    results: List[FoClause] = []
    for eq_lit in c1_std.literals:
        is_eq, s_left, s_right = is_equality_literal(eq_lit)
        if is_eq and eq_lit.is_positive and s_left is not None and s_right is not None:
            # Test both directions: s -> t and t -> s
            for s, t in [(s_left, s_right), (s_right, s_left)]:
                for tgt_lit in c2_std.literals:
                    for pos, u in all_literal_positions(tgt_lit, non_variable_only=True):
                        mgu = unify_terms(s, u)
                        if mgu is not None:
                            new_tgt = replace_literal_subterm(tgt_lit, pos, t)
                            rem1 = {l for l in c1_std.literals if l != eq_lit}
                            rem2 = {l for l in c2_std.literals if l != tgt_lit}
                            unified = {l.subst(mgu) for l in (rem1 | rem2 | {new_tgt})}
                            results.append(FoClause(unified))
    return results


def equality_resolution(clause: FoClause) -> List[FoClause]:
    """
    Reflexivity resolution rule:
    Given a clause C containing a negative equality ~(s = t),
    if s and t unify with mgu sigma, derive (C \\ {~(s = t)}) sigma.
    """
    results: List[FoClause] = []
    for lit in clause.literals:
        is_eq, s, t = is_equality_literal(lit)
        if is_eq and not lit.is_positive and s is not None and t is not None:
            mgu = unify_terms(s, t)
            if mgu is not None:
                rem = {l for l in clause.literals if l != lit}
                unified = {l.subst(mgu) for l in rem}
                results.append(FoClause(unified))
    return results


def prove_by_paramodulation(clauses: List[FoClause], max_steps: int = 150) -> Tuple[bool, List[str]]:
    """
    First-order resolution refutation theorem prover with paramodulation and equality resolution.
    Returns (proved: bool, derivation_log: List[str]).
    """
    clause_set = set(clauses)
    log = [f"Initial clause: {c}" for c in clauses]

    if any(c.is_empty() for c in clause_set):
        log.append("Contradiction immediately present.")
        return True, log

    for step in range(max_steps):
        new_clauses = set()
        c_list = list(clause_set)

        # 1. Equality resolution (reflexivity resolution on negative equalities)
        for c in c_list:
            for eq_res in equality_resolution(c):
                if eq_res not in clause_set:
                    new_clauses.add(eq_res)
                    log.append(f"Equality resolution on {c} => {eq_res}")
                    if eq_res.is_empty():
                        return True, log

        # 2. Factoring
        for c in c_list:
            for factor in factor_clause(c):
                if factor not in clause_set:
                    new_clauses.add(factor)
                    log.append(f"Factoring {c} => {factor}")
                    if factor.is_empty():
                        return True, log

        # 3. Binary resolution and paramodulation between pairs
        for i in range(len(c_list)):
            for j in range(i, len(c_list)):
                c1, c2 = c_list[i], c_list[j]

                # Binary resolution
                for res in resolve_clauses(c1, c2, step):
                    if res not in clause_set:
                        new_clauses.add(res)
                        log.append(f"Resolved ({c1}) and ({c2}) => ({res})")
                        if res.is_empty():
                            return True, log

                # Paramodulation: c1 into c2 and c2 into c1
                pms = paramodulate(c1, c2, step)
                if i != j:
                    pms.extend(paramodulate(c2, c1, step))

                for pm in pms:
                    if pm not in clause_set:
                        new_clauses.add(pm)
                        log.append(f"Paramodulated ({c1}) into ({c2}) => ({pm})")
                        if pm.is_empty():
                            return True, log

        if not new_clauses:
            return False, log

        clause_set.update(new_clauses)

    return False, log


def prove_equational_validity(formula: FoFormula, max_steps: int = 150) -> Tuple[bool, List[str]]:
    """
    Attempt to prove the validity of a first-order formula with equality
    by refuting its negation using Skolemization, CNF conversion,
    and paramodulation resolution refutation.
    """
    negation = ~formula
    clauses = formula_to_clauses(negation)
    return prove_by_paramodulation(clauses, max_steps=max_steps)


# -------------------------------------------------------------
# Section 5: Term Rewriting System (TRS) and Knuth-Bendix Completion
# -------------------------------------------------------------

class RewriteRule:
    """An oriented term rewrite rule: lhs ==> rhs."""

    def __init__(self, lhs: Term, rhs: Term):
        if isinstance(lhs, Var):
            raise ValueError(f"Left-hand side of rewrite rule cannot be a variable: {lhs}")
        if not (rhs.vars() <= lhs.vars()):
            raise ValueError(f"Variables in RHS ({rhs.vars()}) must be subset of LHS ({lhs.vars()}) in {lhs} ==> {rhs}")
        self.lhs = lhs
        self.rhs = rhs

    def vars(self) -> Set[str]:
        return self.lhs.vars() | self.rhs.vars()

    def subst(self, mapping: Dict[str, Term]) -> "RewriteRule":
        return RewriteRule(self.lhs.subst(mapping), self.rhs.subst(mapping))

    def standardize_apart(self, suffix: str) -> "RewriteRule":
        mapping = {v: Var(f"{v}_{suffix}") for v in self.vars()}
        return self.subst(mapping)

    def canonicalize(self) -> "RewriteRule":
        """Rename variables to standard x0, x1, ... in order of first appearance."""
        ordered_vars: List[str] = []

        def _scan(t: Term):
            if isinstance(t, Var):
                if t.name not in ordered_vars:
                    ordered_vars.append(t.name)
            elif isinstance(t, Fn):
                for a in t.args:
                    _scan(a)

        _scan(self.lhs)
        _scan(self.rhs)
        mapping = {v: Var(f"x_{i}") for i, v in enumerate(ordered_vars)}
        return self.subst(mapping)

    def __str__(self) -> str:
        return f"{self.lhs} ==> {self.rhs}"

    def __repr__(self) -> str:
        return f"RewriteRule({self.lhs} ==> {self.rhs})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, RewriteRule) and self.lhs == other.lhs and self.rhs == other.rhs

    def __hash__(self) -> int:
        return hash(("RewriteRule", self.lhs, self.rhs))


def match_term(pattern: Term, target: Term, subst: Optional[Dict[str, Term]] = None) -> Optional[Dict[str, Term]]:
    """
    Syntactic term matching: find substitution sigma such that pattern.subst(sigma) == target.
    Variables in target are treated as rigid symbols.
    """
    if subst is None:
        subst = {}

    if isinstance(pattern, Var):
        if pattern.name in subst:
            return subst if subst[pattern.name] == target else None
        new_subst = dict(subst)
        new_subst[pattern.name] = target
        return new_subst

    elif isinstance(pattern, Const):
        return subst if isinstance(target, Const) and target.name == pattern.name else None

    elif isinstance(pattern, Fn):
        if not (isinstance(target, Fn) and target.name == pattern.name and len(target.args) == len(pattern.args)):
            return None
        cur = dict(subst)
        for p_arg, t_arg in zip(pattern.args, target.args):
            cur = match_term(p_arg, t_arg, cur)
            if cur is None:
                return None
        return cur

    return None


def rewrite_step(term: Term, rules: List[RewriteRule]) -> Optional[Term]:
    """Find the first applicable redex in term and apply the matching rewrite rule."""
    for pos, sub in all_subterm_positions(term):
        for rule in rules:
            sigma = match_term(rule.lhs, sub)
            if sigma is not None:
                replacement = rule.rhs.subst(sigma)
                return replace_subterm(term, pos, replacement)
    return None


def normalize_term(term: Term, rules: List[RewriteRule], max_steps: int = 1000) -> Term:
    """Normalize a term with respect to a set of rewrite rules until no rule applies."""
    current = term
    for _ in range(max_steps):
        next_term = rewrite_step(current, rules)
        if next_term is None or next_term == current:
            break
        current = next_term
    return current


def lpo_greater(s: Term, t: Term, precedence: Optional[Dict[str, int]] = None) -> bool:
    """
    Lexicographic Path Ordering (LPO).
    Returns True if s >_lpo t under symbol precedence dictionary.
    Precedence maps function/constant names to integers (higher integer = higher precedence).
    """
    if precedence is None:
        precedence = {}

    if s == t:
        return False
    if isinstance(s, Var):
        return False
    if isinstance(t, Var):
        return t.name in s.vars()

    s_name = s.name
    s_args = s.args if isinstance(s, Fn) else ()
    t_name = t.name
    t_args = t.args if isinstance(t, Fn) else ()

    # Case 1: exists s_i such that s_i >=_lpo t
    for s_i in s_args:
        if s_i == t or lpo_greater(s_i, t, precedence):
            return True

    # Case 2: s >_lpo t_j for all arguments t_j of t
    if all(lpo_greater(s, t_j, precedence) for t_j in t_args):
        prec_s = precedence.get(s_name, 0)
        prec_t = precedence.get(t_name, 0)

        # 2a: precedence(s) > precedence(t)
        if prec_s > prec_t:
            return True

        # 2b: same function symbol and lexicographic argument comparison
        elif prec_s == prec_t and s_name == t_name and len(s_args) == len(t_args):
            for s_i, t_i in zip(s_args, t_args):
                if s_i == t_i:
                    continue
                return lpo_greater(s_i, t_i, precedence)

    return False


def critical_pairs(rule1: RewriteRule, rule2: RewriteRule, step: int = 0) -> List[Tuple[Term, Term]]:
    """
    Compute all critical pairs between rule1 and rule2.
    Variables of rule2 are standardized apart.
    """
    rule2_std = rule2.standardize_apart(f"CP_{step}")
    pairs: List[Tuple[Term, Term]] = []

    for pos, sub in all_subterm_positions(rule1.lhs, non_variable_only=True):
        # Skip trivial overlap of rule with itself at the root
        if not pos and rule1 == rule2:
            continue

        mgu = unify_terms(sub, rule2_std.lhs)
        if mgu is not None:
            c1 = rule1.rhs.subst(mgu)
            c2 = replace_subterm(rule1.lhs, pos, rule2_std.rhs).subst(mgu)
            pairs.append((c1, c2))

    return pairs


def knuth_bendix_completion(
    equations: List[Tuple[Term, Term]],
    precedence: Optional[Dict[str, int]] = None,
    max_iterations: int = 200
) -> Optional[List[RewriteRule]]:
    """
    Knuth-Bendix critical pair completion algorithm.
    Takes an equational theory and attempts to produce a confluent,
    terminating Term Rewriting System (TRS) using Lexicographic Path Ordering.
    Returns list of completed rewrite rules, or None if an equation cannot be oriented.
    """
    eq_worklist = list(equations)
    rules: List[RewriteRule] = []
    step = 0

    while eq_worklist and step < max_iterations:
        step += 1
        s, t = eq_worklist.pop(0)

        s_norm = normalize_term(s, rules)
        t_norm = normalize_term(t, rules)

        if s_norm == t_norm:
            continue

        # Attempt to orient using LPO
        if lpo_greater(s_norm, t_norm, precedence) and t_norm.vars() <= s_norm.vars():
            new_rule = RewriteRule(s_norm, t_norm)
        elif lpo_greater(t_norm, s_norm, precedence) and s_norm.vars() <= t_norm.vars():
            new_rule = RewriteRule(t_norm, s_norm)
        else:
            # Cannot orient
            return None

        # Inter-reduce existing rules with the new rule
        new_rules: List[RewriteRule] = []
        for old_rule in rules:
            # If old LHS can be reduced, re-add to equation worklist
            lhs_reduced = rewrite_step(old_rule.lhs, [new_rule])
            if lhs_reduced is not None:
                eq_worklist.append((lhs_reduced, old_rule.rhs))
            else:
                rhs_norm = normalize_term(old_rule.rhs, [new_rule] + rules)
                new_rules.append(RewriteRule(old_rule.lhs, rhs_norm))

        rules = new_rules + [new_rule]

        # Generate critical pairs between new_rule and all rules in TRS
        for r in rules:
            cps1 = critical_pairs(new_rule, r, step)
            cps2 = critical_pairs(r, new_rule, step)
            for c1, c2 in cps1 + cps2:
                eq_worklist.append((c1, c2))

    return rules


def solve_word_problem(
    equations: List[Tuple[Term, Term]],
    query: Tuple[Term, Term],
    precedence: Optional[Dict[str, int]] = None,
    max_iterations: int = 200
) -> Optional[bool]:
    """
    Solve the equational word problem: equations |= (query[0] = query[1]).
    Runs Knuth-Bendix completion to obtain a convergent TRS, then checks
    if both terms in the query normalize to the identical normal form.
    Returns True/False, or None if Knuth-Bendix completion cannot orient.
    """
    trs = knuth_bendix_completion(equations, precedence=precedence, max_iterations=max_iterations)
    if trs is None:
        return None
    s_norm = normalize_term(query[0], trs)
    t_norm = normalize_term(query[1], trs)
    return s_norm == t_norm
