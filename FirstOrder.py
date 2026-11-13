"""
First-Order Logic (FOL) Engine in Python.

This module provides:
- First-Order Term representation (Var, Const, Fn)
- First-Order Formula AST (Pred, Eq, FoBot, FoTop, FoNot, FoConj, FoDisj, FoImpl, FoIff, Forall, Exists)
- Free variables, bound variables, and sentence checks (closed formulas)
- Capture-avoiding substitution with alpha-renaming
- Robinson's first-order syntactic unification algorithm with occurs-check
- First-order semantic structures / finite model evaluation
- First-order clausal resolution refutation theorem prover
"""

from typing import Union, Dict, Set, List, Tuple, Optional, Any, Callable
import copy


class Term:
    """Base class for first-order logic terms."""

    def vars(self) -> Set[str]:
        """Return the set of variable names occurring in this term."""
        raise NotImplementedError

    def subst(self, mapping: Dict[str, "Term"]) -> "Term":
        """Apply term substitution mapping variable names to terms."""
        raise NotImplementedError

    def __eq__(self, other: Any) -> bool:
        raise NotImplementedError

    def __hash__(self) -> int:
        raise NotImplementedError

    def __repr__(self) -> str:
        return str(self)


class Var(Term):
    """First-order individual variable."""

    def __init__(self, name: str):
        self.name = str(name)

    def vars(self) -> Set[str]:
        return {self.name}

    def subst(self, mapping: Dict[str, Term]) -> Term:
        return mapping.get(self.name, self)

    def __str__(self) -> str:
        return self.name

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Var) and self.name == other.name

    def __hash__(self) -> int:
        return hash(("Var", self.name))


class Const(Term):
    """First-order constant symbol (individual constant)."""

    def __init__(self, name: str):
        self.name = str(name)

    def vars(self) -> Set[str]:
        return set()

    def subst(self, mapping: Dict[str, Term]) -> Term:
        return self

    def __str__(self) -> str:
        return self.name

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Const) and self.name == other.name

    def __hash__(self) -> int:
        return hash(("Const", self.name))


class Fn(Term):
    """Function application: f(t_1, ..., t_n)."""

    def __init__(self, name: str, args: Union[List[Term], Tuple[Term, ...]]):
        self.name = str(name)
        self.args = tuple(args)

    def vars(self) -> Set[str]:
        res = set()
        for a in self.args:
            res |= a.vars()
        return res

    def subst(self, mapping: Dict[str, Term]) -> Term:
        return Fn(self.name, [a.subst(mapping) for a in self.args])

    def __str__(self) -> str:
        args_str = ", ".join(str(a) for a in self.args)
        return f"{self.name}({args_str})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Fn) and self.name == other.name and self.args == other.args

    def __hash__(self) -> int:
        return hash(("Fn", self.name, self.args))


class FoFormula:
    """Base class for first-order logic formulas."""

    def free_vars(self) -> Set[str]:
        """Return the set of free variables occurring in this formula."""
        raise NotImplementedError

    def bound_vars(self) -> Set[str]:
        """Return the set of bound variables occurring in this formula."""
        raise NotImplementedError

    def all_vars(self) -> Set[str]:
        """Return all variables (free and bound)."""
        return self.free_vars() | self.bound_vars()

    def is_sentence(self) -> bool:
        """A sentence is a closed formula with no free variables."""
        return len(self.free_vars()) == 0

    def subst(self, mapping: Dict[str, Term]) -> "FoFormula":
        """Capture-avoiding substitution."""
        raise NotImplementedError

    def __invert__(self) -> "FoFormula":
        return FoNot(self)

    def __and__(self, other: "FoFormula") -> "FoFormula":
        return FoConj(self, other)

    def __or__(self, other: "FoFormula") -> "FoFormula":
        return FoDisj(self, other)

    def __rshift__(self, other: "FoFormula") -> "FoFormula":
        return FoImpl(self, other)

    def iff(self, other: "FoFormula") -> "FoFormula":
        return FoIff(self, other)

    def __repr__(self) -> str:
        return str(self)


class Pred(FoFormula):
    """Predicate application: P(t_1, ..., t_n)."""

    def __init__(self, name: str, args: Union[List[Term], Tuple[Term, ...]]):
        self.name = str(name)
        self.args = tuple(args)

    def free_vars(self) -> Set[str]:
        res = set()
        for a in self.args:
            res |= a.vars()
        return res

    def bound_vars(self) -> Set[str]:
        return set()

    def subst(self, mapping: Dict[str, Term]) -> FoFormula:
        return Pred(self.name, [a.subst(mapping) for a in self.args])

    def __str__(self) -> str:
        if not self.args:
            return self.name
        args_str = ", ".join(str(a) for a in self.args)
        return f"{self.name}({args_str})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Pred) and self.name == other.name and self.args == other.args

    def __hash__(self) -> int:
        return hash(("Pred", self.name, self.args))


class Eq(FoFormula):
    """First-order equality predicate: t_1 = t_2."""

    def __init__(self, left: Term, right: Term):
        self.left = left
        self.right = right

    def free_vars(self) -> Set[str]:
        return self.left.vars() | self.right.vars()

    def bound_vars(self) -> Set[str]:
        return set()

    def subst(self, mapping: Dict[str, Term]) -> FoFormula:
        return Eq(self.left.subst(mapping), self.right.subst(mapping))

    def __str__(self) -> str:
        return f"({self.left} = {self.right})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Eq) and self.left == other.left and self.right == other.right

    def __hash__(self) -> int:
        return hash(("Eq", self.left, self.right))


class FoBot(FoFormula):
    """First-order contradiction."""

    def free_vars(self) -> Set[str]:
        return set()

    def bound_vars(self) -> Set[str]:
        return set()

    def subst(self, mapping: Dict[str, Term]) -> FoFormula:
        return self

    def __str__(self) -> str:
        return "Bot"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, FoBot)

    def __hash__(self) -> int:
        return hash("FoBot")


class FoTop(FoFormula):
    """First-order tautology."""

    def free_vars(self) -> Set[str]:
        return set()

    def bound_vars(self) -> Set[str]:
        return set()

    def subst(self, mapping: Dict[str, Term]) -> FoFormula:
        return self

    def __str__(self) -> str:
        return "Top"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, FoTop)

    def __hash__(self) -> int:
        return hash("FoTop")


class FoNot(FoFormula):
    """Negation in first-order logic."""

    def __init__(self, inner: FoFormula):
        self.inner = inner

    def free_vars(self) -> Set[str]:
        return self.inner.free_vars()

    def bound_vars(self) -> Set[str]:
        return self.inner.bound_vars()

    def subst(self, mapping: Dict[str, Term]) -> FoFormula:
        return FoNot(self.inner.subst(mapping))

    def __str__(self) -> str:
        return f"~({self.inner})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, FoNot) and self.inner == other.inner

    def __hash__(self) -> int:
        return hash(("FoNot", self.inner))


class FoConj(FoFormula):
    """Conjunction in first-order logic."""

    def __init__(self, left: FoFormula, right: FoFormula):
        self.left = left
        self.right = right

    def free_vars(self) -> Set[str]:
        return self.left.free_vars() | self.right.free_vars()

    def bound_vars(self) -> Set[str]:
        return self.left.bound_vars() | self.right.bound_vars()

    def subst(self, mapping: Dict[str, Term]) -> FoFormula:
        return FoConj(self.left.subst(mapping), self.right.subst(mapping))

    def __str__(self) -> str:
        return f"({self.left} & {self.right})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, FoConj) and self.left == other.left and self.right == other.right

    def __hash__(self) -> int:
        return hash(("FoConj", self.left, self.right))


class FoDisj(FoFormula):
    """Disjunction in first-order logic."""

    def __init__(self, left: FoFormula, right: FoFormula):
        self.left = left
        self.right = right

    def free_vars(self) -> Set[str]:
        return self.left.free_vars() | self.right.free_vars()

    def bound_vars(self) -> Set[str]:
        return self.left.bound_vars() | self.right.bound_vars()

    def subst(self, mapping: Dict[str, Term]) -> FoFormula:
        return FoDisj(self.left.subst(mapping), self.right.subst(mapping))

    def __str__(self) -> str:
        return f"({self.left} | {self.right})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, FoDisj) and self.left == other.left and self.right == other.right

    def __hash__(self) -> int:
        return hash(("FoDisj", self.left, self.right))


class FoImpl(FoFormula):
    """Implication in first-order logic."""

    def __init__(self, left: FoFormula, right: FoFormula):
        self.left = left
        self.right = right

    def free_vars(self) -> Set[str]:
        return self.left.free_vars() | self.right.free_vars()

    def bound_vars(self) -> Set[str]:
        return self.left.bound_vars() | self.right.bound_vars()

    def subst(self, mapping: Dict[str, Term]) -> FoFormula:
        return FoImpl(self.left.subst(mapping), self.right.subst(mapping))

    def __str__(self) -> str:
        return f"({self.left} >> {self.right})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, FoImpl) and self.left == other.left and self.right == other.right

    def __hash__(self) -> int:
        return hash(("FoImpl", self.left, self.right))


class FoIff(FoFormula):
    """Equivalence in first-order logic."""

    def __init__(self, left: FoFormula, right: FoFormula):
        self.left = left
        self.right = right

    def free_vars(self) -> Set[str]:
        return self.left.free_vars() | self.right.free_vars()

    def bound_vars(self) -> Set[str]:
        return self.left.bound_vars() | self.right.bound_vars()

    def subst(self, mapping: Dict[str, Term]) -> FoFormula:
        return FoIff(self.left.subst(mapping), self.right.subst(mapping))

    def __str__(self) -> str:
        return f"({self.left} <-> {self.right})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, FoIff) and self.left == other.left and self.right == other.right

    def __hash__(self) -> int:
        return hash(("FoIff", self.left, self.right))


def _fresh_var(base: str, forbidden: Set[str]) -> str:
    """Generate a variable name derived from base that is not in forbidden."""
    idx = 1
    candidate = f"{base}_{idx}"
    while candidate in forbidden:
        idx += 1
        candidate = f"{base}_{idx}"
    return candidate


class Forall(FoFormula):
    """Universal quantifier: forall var. body."""

    def __init__(self, var: str, body: FoFormula):
        self.var = str(var)
        self.body = body

    def free_vars(self) -> Set[str]:
        return self.body.free_vars() - {self.var}

    def bound_vars(self) -> Set[str]:
        return self.body.bound_vars() | {self.var}

    def subst(self, mapping: Dict[str, Term]) -> FoFormula:
        # If mapping does not affect free variables of body, return self
        relevant_keys = set(mapping.keys()) & self.free_vars()
        if not relevant_keys:
            return self

        # The bound variable cannot be replaced by outer substitution
        filtered_mapping = {k: v for k, v in mapping.items() if k != self.var}

        # Check for variable capture:
        # Does any term in filtered_mapping contain self.var free?
        terms_vars = set().union(*(v.vars() for v in filtered_mapping.values())) if filtered_mapping else set()
        if self.var in terms_vars:
            # Alpha-renaming required
            forbidden = self.body.all_vars() | terms_vars | set(mapping.keys())
            fresh = _fresh_var(self.var, forbidden)
            renamed_body = self.body.subst({self.var: Var(fresh)})
            return Forall(fresh, renamed_body.subst(filtered_mapping))
        else:
            return Forall(self.var, self.body.subst(filtered_mapping))

    def __str__(self) -> str:
        return f"(forall {self.var}. {self.body})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Forall) and self.var == other.var and self.body == other.body

    def __hash__(self) -> int:
        return hash(("Forall", self.var, self.body))


class Exists(FoFormula):
    """Existential quantifier: exists var. body."""

    def __init__(self, var: str, body: FoFormula):
        self.var = str(var)
        self.body = body

    def free_vars(self) -> Set[str]:
        return self.body.free_vars() - {self.var}

    def bound_vars(self) -> Set[str]:
        return self.body.bound_vars() | {self.var}

    def subst(self, mapping: Dict[str, Term]) -> FoFormula:
        relevant_keys = set(mapping.keys()) & self.free_vars()
        if not relevant_keys:
            return self

        filtered_mapping = {k: v for k, v in mapping.items() if k != self.var}
        terms_vars = set().union(*(v.vars() for v in filtered_mapping.values())) if filtered_mapping else set()
        if self.var in terms_vars:
            forbidden = self.body.all_vars() | terms_vars | set(mapping.keys())
            fresh = _fresh_var(self.var, forbidden)
            renamed_body = self.body.subst({self.var: Var(fresh)})
            return Exists(fresh, renamed_body.subst(filtered_mapping))
        else:
            return Exists(self.var, self.body.subst(filtered_mapping))

    def __str__(self) -> str:
        return f"(exists {self.var}. {self.body})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Exists) and self.var == other.var and self.body == other.body

    def __hash__(self) -> int:
        return hash(("Exists", self.var, self.body))


# -------------------------------------------------------------
# Robinson's Syntactic Unification Algorithm
# -------------------------------------------------------------

def compose_substitutions(subst1: Dict[str, Term], subst2: Dict[str, Term]) -> Dict[str, Term]:
    """Compose two substitutions: theta = subst1 o subst2 (apply subst1 then subst2)."""
    res: Dict[str, Term] = {}
    for v, t in subst1.items():
        res[v] = t.subst(subst2)
    for v, t in subst2.items():
        if v not in res:
            res[v] = t
    return res


def unify_terms(t1: Term, t2: Term, subst: Optional[Dict[str, Term]] = None) -> Optional[Dict[str, Term]]:
    """
    Syntactic term unification with occurs-check.
    Returns the Most General Unifier (MGU) as a substitution dict, or None if not unifiable.
    """
    if subst is None:
        subst = {}

    # Apply existing substitution
    t1 = t1.subst(subst)
    t2 = t2.subst(subst)

    if t1 == t2:
        return subst

    if isinstance(t1, Var):
        return _unify_var(t1.name, t2, subst)

    if isinstance(t2, Var):
        return _unify_var(t2.name, t1, subst)

    if isinstance(t1, Const) and isinstance(t2, Const):
        return subst if t1.name == t2.name else None

    if isinstance(t1, Fn) and isinstance(t2, Fn):
        if t1.name != t2.name or len(t1.args) != len(t2.args):
            return None
        cur_subst = subst
        for a1, a2 in zip(t1.args, t2.args):
            new_subst = unify_terms(a1, a2, cur_subst)
            if new_subst is None:
                return None
            cur_subst = new_subst
        return cur_subst

    return None


def _unify_var(var_name: str, term: Term, subst: Dict[str, Term]) -> Optional[Dict[str, Term]]:
    """Helper to bind variable to term with occurs-check."""
    if isinstance(term, Var) and term.name == var_name:
        return subst

    # Occurs-check: does var_name occur in term?
    if var_name in term.vars():
        return None  # Cycle detected

    new_binding = {var_name: term}
    return compose_substitutions(subst, new_binding)


def unify_predicates(p1: Pred, p2: Pred, subst: Optional[Dict[str, Term]] = None) -> Optional[Dict[str, Term]]:
    """Unify two atomic predicates P(t_1, ..., t_n) and Q(s_1, ..., s_n)."""
    if p1.name != p2.name or len(p1.args) != len(p2.args):
        return None
    cur_subst = subst or {}
    for a1, a2 in zip(p1.args, p2.args):
        new_subst = unify_terms(a1, a2, cur_subst)
        if new_subst is None:
            return None
        cur_subst = new_subst
    return cur_subst


# -------------------------------------------------------------
# First-Order Model / Structure Semantics
# -------------------------------------------------------------

class Structure:
    """
    A first-order interpretation structure M = (D, I):
    - domain: non-empty set of individuals
    - constants: mapping from constant names to domain elements
    - functions: mapping from function names to callables (D^n -> D)
    - predicates: mapping from predicate names to callables (D^n -> bool)
    """

    def __init__(
        self,
        domain: Set[Any],
        constants: Optional[Dict[str, Any]] = None,
        functions: Optional[Dict[str, Callable[..., Any]]] = None,
        predicates: Optional[Dict[str, Callable[..., bool]]] = None,
    ):
        if not domain:
            raise ValueError("First-order structure domain must be non-empty.")
        self.domain = domain
        self.constants = constants or {}
        self.functions = functions or {}
        self.predicates = predicates or {}

    def eval_term(self, term: Term, assignment: Dict[str, Any]) -> Any:
        if isinstance(term, Var):
            if term.name not in assignment:
                raise ValueError(f"Unassigned variable: {term.name}")
            return assignment[term.name]
        elif isinstance(term, Const):
            if term.name not in self.constants:
                raise ValueError(f"Uninterpreted constant: {term.name}")
            return self.constants[term.name]
        elif isinstance(term, Fn):
            if term.name not in self.functions:
                raise ValueError(f"Uninterpreted function: {term.name}")
            args_vals = [self.eval_term(a, assignment) for a in term.args]
            return self.functions[term.name](*args_vals)
        raise ValueError(f"Unknown term type: {type(term)}")

    def eval_formula(self, formula: FoFormula, assignment: Optional[Dict[str, Any]] = None) -> bool:
        if assignment is None:
            assignment = {}

        if isinstance(formula, FoBot):
            return False
        if isinstance(formula, FoTop):
            return True
        if isinstance(formula, Eq):
            return self.eval_term(formula.left, assignment) == self.eval_term(formula.right, assignment)
        if isinstance(formula, Pred):
            if formula.name not in self.predicates:
                raise ValueError(f"Uninterpreted predicate: {formula.name}")
            args_vals = [self.eval_term(a, assignment) for a in formula.args]
            return self.predicates[formula.name](*args_vals)
        if isinstance(formula, FoNot):
            return not self.eval_formula(formula.inner, assignment)
        if isinstance(formula, FoConj):
            return self.eval_formula(formula.left, assignment) and self.eval_formula(formula.right, assignment)
        if isinstance(formula, FoDisj):
            return self.eval_formula(formula.left, assignment) or self.eval_formula(formula.right, assignment)
        if isinstance(formula, FoImpl):
            return (not self.eval_formula(formula.left, assignment)) or self.eval_formula(formula.right, assignment)
        if isinstance(formula, FoIff):
            return self.eval_formula(formula.left, assignment) == self.eval_formula(formula.right, assignment)
        if isinstance(formula, Forall):
            for d in self.domain:
                extended = dict(assignment)
                extended[formula.var] = d
                if not self.eval_formula(formula.body, extended):
                    return False
            return True
        if isinstance(formula, Exists):
            for d in self.domain:
                extended = dict(assignment)
                extended[formula.var] = d
                if self.eval_formula(formula.body, extended):
                    return True
            return False
        raise ValueError(f"Unknown formula type: {type(formula)}")


# -------------------------------------------------------------
# First-Order Clause & Resolution Engine
# -------------------------------------------------------------

class FoLiteral:
    """A first-order literal: either Pred or ~Pred."""

    def __init__(self, pred: Pred, is_positive: bool = True):
        self.pred = pred
        self.is_positive = is_positive

    def vars(self) -> Set[str]:
        return self.pred.free_vars()

    def subst(self, mapping: Dict[str, Term]) -> "FoLiteral":
        return FoLiteral(self.pred.subst(mapping), self.is_positive)

    def negate(self) -> "FoLiteral":
        return FoLiteral(self.pred, not self.is_positive)

    def __str__(self) -> str:
        return str(self.pred) if self.is_positive else f"~{self.pred}"

    def __repr__(self) -> str:
        return str(self)

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, FoLiteral) and self.pred == other.pred and self.is_positive == other.is_positive

    def __hash__(self) -> int:
        return hash(("FoLiteral", self.pred, self.is_positive))


class FoClause:
    """A first-order clause: a disjunction of literals."""

    def __init__(self, literals: Union[Set[FoLiteral], List[FoLiteral]]):
        self.literals = frozenset(literals)

    def is_empty(self) -> bool:
        return len(self.literals) == 0

    def vars(self) -> Set[str]:
        res = set()
        for lit in self.literals:
            res |= lit.vars()
        return res

    def subst(self, mapping: Dict[str, Term]) -> "FoClause":
        return FoClause({lit.subst(mapping) for lit in self.literals})

    def standardize_apart(self, suffix: str) -> "FoClause":
        mapping = {v: Var(f"{v}_{suffix}") for v in self.vars()}
        return self.subst(mapping)

    def __str__(self) -> str:
        if self.is_empty():
            return "[]"
        return " | ".join(str(lit) for lit in self.literals)

    def __repr__(self) -> str:
        return f"Clause({str(self)})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, FoClause) and self.literals == other.literals

    def __hash__(self) -> int:
        return hash(self.literals)


def resolve_clauses(c1: FoClause, c2: FoClause, step: int = 0) -> List[FoClause]:
    """
    Compute all binary resolvents between clauses c1 and c2.
    Variables are standardized apart to avoid accidental variable collision.
    """
    c1_std = c1.standardize_apart(f"L{step}")
    c2_std = c2.standardize_apart(f"R{step}")

    resolvents = []
    for l1 in c1_std.literals:
        for l2 in c2_std.literals:
            # Must have opposite polarities and unify predicates
            if l1.is_positive != l2.is_positive:
                mgu = unify_predicates(l1.pred, l2.pred)
                if mgu is not None:
                    rem1 = {lit for lit in c1_std.literals if lit != l1}
                    rem2 = {lit for lit in c2_std.literals if lit != l2}
                    unified_literals = {lit.subst(mgu) for lit in (rem1 | rem2)}
                    resolvents.append(FoClause(unified_literals))
    return resolvents


def factor_clause(clause: FoClause) -> List[FoClause]:
    """Compute factors of a clause (unifying two literals of same polarity)."""
    factors = []
    lits = list(clause.literals)
    for i in range(len(lits)):
        for j in range(i + 1, len(lits)):
            l1, l2 = lits[i], lits[j]
            if l1.is_positive == l2.is_positive:
                mgu = unify_predicates(l1.pred, l2.pred)
                if mgu is not None:
                    factored = {lit.subst(mgu) for lit in clause.literals}
                    factors.append(FoClause(factored))
    return factors


def prove_by_resolution(clauses: List[FoClause], max_steps: int = 100) -> Tuple[bool, List[str]]:
    """
    Attempt to find a refutation proof (deriving the empty clause [])
    using first-order resolution and factoring.
    Returns (proved: bool, derivation_log: List[str]).
    """
    clause_set = set(clauses)
    log = [f"Initial clause: {c}" for c in clauses]

    # Check if empty clause is already present
    if any(c.is_empty() for c in clause_set):
        log.append("Contradiction immediately present.")
        return True, log

    for step in range(max_steps):
        new_clauses = set()
        clause_list = list(clause_set)

        # Factor existing clauses
        for c in clause_list:
            for factor in factor_clause(c):
                if factor not in clause_set:
                    new_clauses.add(factor)
                    log.append(f"Factoring {c} => {factor}")
                    if factor.is_empty():
                        return True, log

        # Resolve pairs of clauses
        for i in range(len(clause_list)):
            for j in range(i, len(clause_list)):
                c1, c2 = clause_list[i], clause_list[j]
                resolvents = resolve_clauses(c1, c2, step)
                for res in resolvents:
                    if res not in clause_set:
                        new_clauses.add(res)
                        log.append(f"Resolved ({c1}) and ({c2}) => ({res})")
                        if res.is_empty():
                            return True, log

        if not new_clauses:
            # Saturation reached without contradiction
            return False, log

        clause_set.update(new_clauses)

    return False, log
