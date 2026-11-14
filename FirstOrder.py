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


# -------------------------------------------------------------
# First-Order Normal Forms and Skolemization
# -------------------------------------------------------------

def to_nnf(formula: FoFormula) -> FoFormula:
    """
    Convert a first-order formula to Negation Normal Form (NNF).
    In NNF, negations appear only immediately before atomic formulas,
    and implications/biconditionals are eliminated.
    """
    if isinstance(formula, (FoBot, FoTop, Pred, Eq)):
        return formula
    elif isinstance(formula, FoImpl):
        return to_nnf(FoDisj(FoNot(formula.left), formula.right))
    elif isinstance(formula, FoIff):
        left_impl = FoDisj(FoNot(formula.left), formula.right)
        right_impl = FoDisj(FoNot(formula.right), formula.left)
        return to_nnf(FoConj(left_impl, right_impl))
    elif isinstance(formula, FoConj):
        return FoConj(to_nnf(formula.left), to_nnf(formula.right))
    elif isinstance(formula, FoDisj):
        return FoDisj(to_nnf(formula.left), to_nnf(formula.right))
    elif isinstance(formula, Forall):
        return Forall(formula.var, to_nnf(formula.body))
    elif isinstance(formula, Exists):
        return Exists(formula.var, to_nnf(formula.body))
    elif isinstance(formula, FoNot):
        inner = formula.inner
        if isinstance(inner, FoBot):
            return FoTop()
        elif isinstance(inner, FoTop):
            return FoBot()
        elif isinstance(inner, (Pred, Eq)):
            return FoNot(inner)
        elif isinstance(inner, FoNot):
            return to_nnf(inner.inner)
        elif isinstance(inner, FoConj):
            return FoDisj(to_nnf(FoNot(inner.left)), to_nnf(FoNot(inner.right)))
        elif isinstance(inner, FoDisj):
            return FoConj(to_nnf(FoNot(inner.left)), to_nnf(FoNot(inner.right)))
        elif isinstance(inner, FoImpl):
            return FoConj(to_nnf(inner.left), to_nnf(FoNot(inner.right)))
        elif isinstance(inner, FoIff):
            return to_nnf(FoDisj(FoConj(inner.left, FoNot(inner.right)),
                                 FoConj(FoNot(inner.left), inner.right)))
        elif isinstance(inner, Forall):
            return Exists(inner.var, to_nnf(FoNot(inner.body)))
        elif isinstance(inner, Exists):
            return Forall(inner.var, to_nnf(FoNot(inner.body)))
        else:
            raise ValueError(f"Unknown formula type in negation: {type(inner)}")
    else:
        raise ValueError(f"Unknown formula type: {type(formula)}")


def standardize_apart_formula(formula: FoFormula) -> FoFormula:
    """
    Rename bound variables so that every quantifier has a unique variable name,
    and no bound variable shares a name with any free variable.
    """
    used_vars = set(formula.free_vars())

    def _std(f: FoFormula) -> FoFormula:
        nonlocal used_vars
        if isinstance(f, (FoBot, FoTop, Pred, Eq)):
            return f
        elif isinstance(f, FoNot):
            return FoNot(_std(f.inner))
        elif isinstance(f, FoConj):
            return FoConj(_std(f.left), _std(f.right))
        elif isinstance(f, FoDisj):
            return FoDisj(_std(f.left), _std(f.right))
        elif isinstance(f, FoImpl):
            return FoImpl(_std(f.left), _std(f.right))
        elif isinstance(f, FoIff):
            return FoIff(_std(f.left), _std(f.right))
        elif isinstance(f, Forall):
            v = f.var
            new_v = _fresh_var(v, used_vars) if v in used_vars else v
            used_vars.add(new_v)
            body_renamed = f.body.subst({v: Var(new_v)}) if new_v != v else f.body
            return Forall(new_v, _std(body_renamed))
        elif isinstance(f, Exists):
            v = f.var
            new_v = _fresh_var(v, used_vars) if v in used_vars else v
            used_vars.add(new_v)
            body_renamed = f.body.subst({v: Var(new_v)}) if new_v != v else f.body
            return Exists(new_v, _std(body_renamed))
        else:
            raise ValueError(f"Unknown formula type: {type(f)}")

    return _std(formula)


def to_prenex(formula: FoFormula) -> FoFormula:
    """
    Convert a first-order formula into Prenex Normal Form (PNF):
    Q1 x1. Q2 x2. ... Qn xn. Matrix
    where Matrix is quantifier-free.
    """
    nnf = to_nnf(formula)
    std = standardize_apart_formula(nnf)

    def _pull(f: FoFormula) -> Tuple[List[Tuple[str, str]], FoFormula]:
        if isinstance(f, Forall):
            quants, matrix = _pull(f.body)
            return [("forall", f.var)] + quants, matrix
        elif isinstance(f, Exists):
            quants, matrix = _pull(f.body)
            return [("exists", f.var)] + quants, matrix
        elif isinstance(f, FoConj):
            q_left, m_left = _pull(f.left)
            q_right, m_right = _pull(f.right)
            return q_left + q_right, FoConj(m_left, m_right)
        elif isinstance(f, FoDisj):
            q_left, m_left = _pull(f.left)
            q_right, m_right = _pull(f.right)
            return q_left + q_right, FoDisj(m_left, m_right)
        elif isinstance(f, FoNot):
            return [], f
        elif isinstance(f, (FoBot, FoTop, Pred, Eq)):
            return [], f
        else:
            raise ValueError(f"Unexpected formula type in prenex extraction: {type(f)}")

    quants, matrix = _pull(std)
    res = matrix
    for q_kind, q_var in reversed(quants):
        if q_kind == "forall":
            res = Forall(q_var, res)
        else:
            res = Exists(q_var, res)
    return res


def skolemize(formula: FoFormula, drop_universal: bool = False) -> FoFormula:
    """
    Convert a first-order formula to Skolem Normal Form (SNF).
    Existential variables are replaced with Skolem functions depending on
    the universally quantified variables in whose scope they appear.
    If drop_universal is True, returns the quantifier-free matrix with
    implicit universal quantification.
    """
    prenex = to_prenex(formula)

    univ_vars: List[str] = []
    subst_map: Dict[str, Term] = {}
    skolem_id = 1

    cur = prenex
    while isinstance(cur, (Forall, Exists)):
        if isinstance(cur, Forall):
            univ_vars.append(cur.var)
            cur = cur.body
        elif isinstance(cur, Exists):
            if not univ_vars:
                sk_term: Term = Const(f"sk_c_{skolem_id}")
            else:
                sk_term = Fn(f"sk_f_{skolem_id}", [Var(v) for v in univ_vars])
            skolem_id += 1
            subst_map[cur.var] = sk_term
            cur = cur.body

    # Matrix is quantifier-free
    skolemized_matrix = cur.subst(subst_map)

    if drop_universal or not univ_vars:
        return skolemized_matrix

    res = skolemized_matrix
    for v in reversed(univ_vars):
        res = Forall(v, res)
    return res


def to_cnf_matrix(formula: FoFormula) -> FoFormula:
    """
    Convert a quantifier-free first-order formula in NNF into Conjunctive Normal Form (CNF).
    """
    def _distribute_disj(left: FoFormula, right: FoFormula) -> FoFormula:
        if isinstance(left, FoConj):
            return FoConj(_distribute_disj(left.left, right), _distribute_disj(left.right, right))
        if isinstance(right, FoConj):
            return FoConj(_distribute_disj(left, right.left), _distribute_disj(left, right.right))
        return FoDisj(left, right)

    def _cnf(f: FoFormula) -> FoFormula:
        if isinstance(f, FoConj):
            return FoConj(_cnf(f.left), _cnf(f.right))
        elif isinstance(f, FoDisj):
            return _distribute_disj(_cnf(f.left), _cnf(f.right))
        else:
            return f

    return _cnf(formula)


def formula_to_clauses(formula: FoFormula) -> List[FoClause]:
    """
    Convert a first-order formula to a list of first-order clauses (FoClause).
    The formula is skolemized, converted to CNF, and decomposed into clauses.
    """
    matrix = skolemize(formula, drop_universal=True)
    nnf_matrix = to_nnf(matrix)
    cnf_matrix = to_cnf_matrix(nnf_matrix)

    def _extract_conjs(f: FoFormula) -> List[FoFormula]:
        if isinstance(f, FoConj):
            return _extract_conjs(f.left) + _extract_conjs(f.right)
        return [f]

    def _extract_disjs(f: FoFormula) -> List[FoLiteral]:
        if isinstance(f, FoDisj):
            return _extract_disjs(f.left) + _extract_disjs(f.right)
        elif isinstance(f, Pred):
            return [FoLiteral(f, is_positive=True)]
        elif isinstance(f, Eq):
            return [FoLiteral(Pred("=", [f.left, f.right]), is_positive=True)]
        elif isinstance(f, FoNot):
            if isinstance(f.inner, Pred):
                return [FoLiteral(f.inner, is_positive=False)]
            elif isinstance(f.inner, Eq):
                return [FoLiteral(Pred("=", [f.inner.left, f.inner.right]), is_positive=False)]
            raise ValueError(f"Unexpected negated formula in CNF clause: {f}")
        elif isinstance(f, FoBot):
            return []
        elif isinstance(f, FoTop):
            return []
        else:
            raise ValueError(f"Unexpected subformula in CNF clause: {f}")

    clauses: List[FoClause] = []
    for conj in _extract_conjs(cnf_matrix):
        if isinstance(conj, FoTop):
            continue
        lits = _extract_disjs(conj)
        clauses.append(FoClause(lits))

    return clauses


def prove_validity_by_resolution(formula: FoFormula, max_steps: int = 100) -> Tuple[bool, List[str]]:
    """
    Prove validity of a first-order formula via resolution refutation of its negation.
    Returns (proved: bool, derivation_log: List[str]).
    """
    negated_formula = FoNot(formula)
    clauses = formula_to_clauses(negated_formula)
    proved, log = prove_by_resolution(clauses, max_steps=max_steps)
    return proved, log


# -------------------------------------------------------------
# First-Order Semantic Tableau Prover
# -------------------------------------------------------------

class SignedFormula:
    """A signed first-order formula: (sign: bool, formula: FoFormula)."""

    def __init__(self, formula: FoFormula, sign: bool):
        self.formula = formula
        self.sign = sign

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, SignedFormula) and self.sign == other.sign and self.formula == other.formula

    def __hash__(self) -> int:
        return hash(("SignedFormula", self.sign, self.formula))

    def __str__(self) -> str:
        s = "T" if self.sign else "F"
        return f"{s}({self.formula})"

    def __repr__(self) -> str:
        return str(self)


class TableauBranch:
    """
    A single branch of a Semantic Tableau.
    Contains signed formulas and tracks closed / open status.
    """

    def __init__(
        self,
        formulas: Optional[List[SignedFormula]] = None,
        constants: Optional[Set[Term]] = None,
        instantiated_gamma: Optional[Dict[SignedFormula, Set[Term]]] = None,
    ):
        self.formulas: List[SignedFormula] = list(formulas or [])
        self.is_closed: bool = False
        self.closure_reason: Optional[str] = None
        self.constants: Set[Term] = set(constants or [])
        self.instantiated_gamma: Dict[SignedFormula, Set[Term]] = {
            sf: set(terms) for sf, terms in (instantiated_gamma or {}).items()
        }
        self._collect_constants()

    def _collect_constants(self) -> None:
        for sf in self.formulas:
            for v in sf.formula.free_vars():
                self.constants.add(Var(v))
            self._extract_terms_from_formula(sf.formula)

    def _extract_terms_from_formula(self, f: FoFormula) -> None:
        if isinstance(f, Pred):
            for a in f.args:
                if isinstance(a, (Const, Fn)):
                    self.constants.add(a)
        elif isinstance(f, Eq):
            for a in (f.left, f.right):
                if isinstance(a, (Const, Fn)):
                    self.constants.add(a)
        elif isinstance(f, FoNot):
            self._extract_terms_from_formula(f.inner)
        elif isinstance(f, (FoConj, FoDisj, FoImpl, FoIff)):
            self._extract_terms_from_formula(f.left)
            self._extract_terms_from_formula(f.right)
        elif isinstance(f, (Forall, Exists)):
            self._extract_terms_from_formula(f.body)

    def check_closure(self) -> bool:
        """Check if this branch contains a contradiction and can be closed."""
        if self.is_closed:
            return True

        for sf in self.formulas:
            if sf.sign and isinstance(sf.formula, FoBot):
                self.is_closed = True
                self.closure_reason = "T(Bot)"
                return True
            if not sf.sign and isinstance(sf.formula, FoTop):
                self.is_closed = True
                self.closure_reason = "F(Top)"
                return True

        pos_atoms = [sf for sf in self.formulas if sf.sign and isinstance(sf.formula, (Pred, Eq))]
        neg_atoms = [sf for sf in self.formulas if not sf.sign and isinstance(sf.formula, (Pred, Eq))]

        for p in pos_atoms:
            for n in neg_atoms:
                if p.formula == n.formula:
                    self.is_closed = True
                    self.closure_reason = f"Complementary pair: {p} and {n}"
                    return True
                if isinstance(p.formula, Pred) and isinstance(n.formula, Pred):
                    mgu = unify_predicates(p.formula, n.formula)
                    if mgu is not None and not mgu:
                        self.is_closed = True
                        self.closure_reason = f"Unifying complementary pair: {p} and {n}"
                        return True

        return False


class SemanticTableau:
    """
    First-Order Semantic Tableau Prover.
    Constructs a refutation tree for formula validity (starting from F(formula)).
    If all branches close, the formula is valid.
    """

    def __init__(self, formula: FoFormula):
        self.goal = formula
        self.branches: List[TableauBranch] = [TableauBranch([SignedFormula(formula, False)])]
        self.log: List[str] = [f"Initial tableau with F({formula})"]
        self.param_counter: int = 1

    def is_closed(self) -> bool:
        return all(b.is_closed for b in self.branches)

    def run(self, max_steps: int = 100) -> bool:
        """Run tableau expansion rules until all branches close or max_steps is reached."""
        for step in range(max_steps):
            for b in self.branches:
                b.check_closure()

            if self.is_closed():
                self.log.append(f"All {len(self.branches)} branch(es) closed. Proved valid.")
                return True

            expanded = False

            # Phase 1: Try Alpha rules (non-branching, propositional)
            for b_idx, b in enumerate(self.branches):
                if b.is_closed:
                    continue
                for sf_idx, sf in enumerate(b.formulas):
                    sign, f = sf.sign, sf.formula
                    if sign and isinstance(f, FoConj):
                        b.formulas.pop(sf_idx)
                        b.formulas.append(SignedFormula(f.left, True))
                        b.formulas.append(SignedFormula(f.right, True))
                        self.log.append(f"Alpha T(&): {f} => T({f.left}), T({f.right})")
                        expanded = True
                        break
                    elif not sign and isinstance(f, FoDisj):
                        b.formulas.pop(sf_idx)
                        b.formulas.append(SignedFormula(f.left, False))
                        b.formulas.append(SignedFormula(f.right, False))
                        self.log.append(f"Alpha F(|): {f} => F({f.left}), F({f.right})")
                        expanded = True
                        break
                    elif not sign and isinstance(f, FoImpl):
                        b.formulas.pop(sf_idx)
                        b.formulas.append(SignedFormula(f.left, True))
                        b.formulas.append(SignedFormula(f.right, False))
                        self.log.append(f"Alpha F(>>): {f} => T({f.left}), F({f.right})")
                        expanded = True
                        break
                    elif sign and isinstance(f, FoNot):
                        b.formulas.pop(sf_idx)
                        b.formulas.append(SignedFormula(f.inner, False))
                        self.log.append(f"Alpha T(~): {f} => F({f.inner})")
                        expanded = True
                        break
                    elif not sign and isinstance(f, FoNot):
                        b.formulas.pop(sf_idx)
                        b.formulas.append(SignedFormula(f.inner, True))
                        self.log.append(f"Alpha F(~): {f} => T({f.inner})")
                        expanded = True
                        break
                if expanded:
                    break

            if expanded:
                continue

            # Phase 2: Try Delta rules (existential / Skolem parameter)
            for b_idx, b in enumerate(self.branches):
                if b.is_closed:
                    continue
                for sf_idx, sf in enumerate(b.formulas):
                    sign, f = sf.sign, sf.formula
                    if (sign and isinstance(f, Exists)) or (not sign and isinstance(f, Forall)):
                        c_fresh = Const(f"c_tab_{self.param_counter}")
                        self.param_counter += 1
                        b.constants.add(c_fresh)
                        inst = f.body.subst({f.var: c_fresh})
                        b.formulas.pop(sf_idx)
                        b.formulas.append(SignedFormula(inst, sign))
                        b._extract_terms_from_formula(inst)
                        rule_name = "Delta T(exists)" if sign else "Delta F(forall)"
                        self.log.append(f"{rule_name}: {f} instantiated with {c_fresh} => {inst}")
                        expanded = True
                        break
                if expanded:
                    break

            if expanded:
                continue

            # Phase 3: Try Beta rules (branching)
            for b_idx, b in enumerate(self.branches):
                if b.is_closed:
                    continue
                for sf_idx, sf in enumerate(b.formulas):
                    sign, f = sf.sign, sf.formula
                    if sign and isinstance(f, FoDisj):
                        b.formulas.pop(sf_idx)
                        b1 = TableauBranch(b.formulas + [SignedFormula(f.left, True)], b.constants, b.instantiated_gamma)
                        b2 = TableauBranch(b.formulas + [SignedFormula(f.right, True)], b.constants, b.instantiated_gamma)
                        self.branches.pop(b_idx)
                        self.branches.insert(b_idx, b2)
                        self.branches.insert(b_idx, b1)
                        self.log.append(f"Beta T(|): {f} branched into T({f.left}) and T({f.right})")
                        expanded = True
                        break
                    elif not sign and isinstance(f, FoConj):
                        b.formulas.pop(sf_idx)
                        b1 = TableauBranch(b.formulas + [SignedFormula(f.left, False)], b.constants, b.instantiated_gamma)
                        b2 = TableauBranch(b.formulas + [SignedFormula(f.right, False)], b.constants, b.instantiated_gamma)
                        self.branches.pop(b_idx)
                        self.branches.insert(b_idx, b2)
                        self.branches.insert(b_idx, b1)
                        self.log.append(f"Beta F(&): {f} branched into F({f.left}) and F({f.right})")
                        expanded = True
                        break
                    elif sign and isinstance(f, FoImpl):
                        b.formulas.pop(sf_idx)
                        b1 = TableauBranch(b.formulas + [SignedFormula(f.left, False)], b.constants, b.instantiated_gamma)
                        b2 = TableauBranch(b.formulas + [SignedFormula(f.right, True)], b.constants, b.instantiated_gamma)
                        self.branches.pop(b_idx)
                        self.branches.insert(b_idx, b2)
                        self.branches.insert(b_idx, b1)
                        self.log.append(f"Beta T(>>): {f} branched into F({f.left}) and T({f.right})")
                        expanded = True
                        break
                    elif sign and isinstance(f, FoIff):
                        b.formulas.pop(sf_idx)
                        b1 = TableauBranch(b.formulas + [SignedFormula(f.left, True), SignedFormula(f.right, True)], b.constants, b.instantiated_gamma)
                        b2 = TableauBranch(b.formulas + [SignedFormula(f.left, False), SignedFormula(f.right, False)], b.constants, b.instantiated_gamma)
                        self.branches.pop(b_idx)
                        self.branches.insert(b_idx, b2)
                        self.branches.insert(b_idx, b1)
                        self.log.append(f"Beta T(<->): {f} branched")
                        expanded = True
                        break
                    elif not sign and isinstance(f, FoIff):
                        b.formulas.pop(sf_idx)
                        b1 = TableauBranch(b.formulas + [SignedFormula(f.left, True), SignedFormula(f.right, False)], b.constants, b.instantiated_gamma)
                        b2 = TableauBranch(b.formulas + [SignedFormula(f.left, False), SignedFormula(f.right, True)], b.constants, b.instantiated_gamma)
                        self.branches.pop(b_idx)
                        self.branches.insert(b_idx, b2)
                        self.branches.insert(b_idx, b1)
                        self.log.append(f"Beta F(<->): {f} branched")
                        expanded = True
                        break
                if expanded:
                    break

            if expanded:
                continue

            # Phase 4: Try Gamma rules (universal instantiation)
            for b_idx, b in enumerate(self.branches):
                if b.is_closed:
                    continue
                for sf_idx, sf in enumerate(b.formulas):
                    sign, f = sf.sign, sf.formula
                    is_gamma = (sign and isinstance(f, Forall)) or (not sign and isinstance(f, Exists))
                    if is_gamma:
                        if not b.constants:
                            default_c = Const("c_0")
                            b.constants.add(default_c)

                        already_done = b.instantiated_gamma.setdefault(sf, set())
                        needed = [t for t in b.constants if t not in already_done]
                        if needed:
                            term = needed[0]
                            already_done.add(term)
                            inst = f.body.subst({f.var: term})
                            new_sf = SignedFormula(inst, sign)
                            b.formulas.append(new_sf)
                            b._extract_terms_from_formula(inst)
                            rule_name = "Gamma T(forall)" if sign else "Gamma F(exists)"
                            self.log.append(f"{rule_name}: {f} instantiated with {term} => {inst}")
                            expanded = True
                            break
                if expanded:
                    break

            if not expanded:
                break

        for b in self.branches:
            b.check_closure()

        return self.is_closed()


def prove_by_tableau(formula: FoFormula, max_steps: int = 100) -> Tuple[bool, List[str]]:
    """
    Attempt to prove validity of a first-order formula using Semantic Tableau.
    Returns (proved: bool, derivation_log: List[str]).
    """
    tableau = SemanticTableau(formula)
    proved = tableau.run(max_steps=max_steps)
    return proved, tableau.log


# -------------------------------------------------------------
# First-Order Equational Reasoning and Term Rewriting Integration
# -------------------------------------------------------------
try:
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
except ImportError:
    pass


