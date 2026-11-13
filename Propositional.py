"""
Propositional Logic Engine in Python.

This module provides:
- Core Propositional AST (Atom, Bot, Top, Not, Conj, Disj, Impl, Iff)
- Operator overloading for formula construction
- Truth value evaluation against valuations (compatible with foIb)
- Truth table generation
- Semantic decision procedures: is_tautology, is_satisfiable, is_contradiction, find_model
- Normal form transformations: Negation Normal Form (NNF), Conjunctive Normal Form (CNF), Disjunctive Normal Form (DNF)
- DPLL SAT Solver with unit propagation and pure literal elimination
"""

from typing import Union, Dict, Set, List, Tuple, Optional, Any, Iterator
import itertools

# Compatibility with Coq definitions
AtomVars = int
nat = int


class Formula:
    """Base class for all propositional logic formulas."""

    def evaluate(self, valuation: Dict[Any, bool]) -> bool:
        """Evaluate the formula given a boolean valuation for atomic variables."""
        raise NotImplementedError

    def atoms(self) -> Set[Any]:
        """Return the set of atomic variables present in the formula."""
        raise NotImplementedError

    def __invert__(self) -> "Formula":
        return Not(self)

    def __and__(self, other: "Formula") -> "Formula":
        return Conj(self, other)

    def __or__(self, other: "Formula") -> "Formula":
        return Disj(self, other)

    def __rshift__(self, other: "Formula") -> "Formula":
        return Impl(self, other)

    def iff(self, other: "Formula") -> "Formula":
        return Iff(self, other)

    def __repr__(self) -> str:
        return str(self)


class Atom(Formula):
    """Atomic proposition identified by an integer or string symbol."""

    def __init__(self, name: Union[int, str]):
        self.name = name

    def evaluate(self, valuation: Dict[Any, bool]) -> bool:
        return valuation.get(self.name, False)

    def atoms(self) -> Set[Any]:
        return {self.name}

    def __str__(self) -> str:
        return str(self.name)

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Atom) and self.name == other.name

    def __hash__(self) -> int:
        return hash(("Atom", self.name))


class Bot(Formula):
    """The bottom / false proposition (contradiction)."""

    def evaluate(self, valuation: Dict[Any, bool]) -> bool:
        return False

    def atoms(self) -> Set[Any]:
        return set()

    def __str__(self) -> str:
        return "Bot"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Bot)

    def __hash__(self) -> int:
        return hash("Bot")


class Top(Formula):
    """The top / true proposition (tautology)."""

    def evaluate(self, valuation: Dict[Any, bool]) -> bool:
        return True

    def atoms(self) -> Set[Any]:
        return set()

    def __str__(self) -> str:
        return "Top"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Top)

    def __hash__(self) -> int:
        return hash("Top")


class Not(Formula):
    """Logical negation of a formula."""

    def __init__(self, inner: Formula):
        self.inner = inner

    def evaluate(self, valuation: Dict[Any, bool]) -> bool:
        return not self.inner.evaluate(valuation)

    def atoms(self) -> Set[Any]:
        return self.inner.atoms()

    def __str__(self) -> str:
        if isinstance(self.inner, Atom):
            return f"~{self.inner}"
        return f"~({self.inner})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Not) and self.inner == other.inner

    def __hash__(self) -> int:
        return hash(("Not", self.inner))


class Conj(Formula):
    """Conjunction (logical AND) of two formulas."""

    def __init__(self, left: Formula, right: Formula):
        self.left = left
        self.right = right

    def evaluate(self, valuation: Dict[Any, bool]) -> bool:
        return self.left.evaluate(valuation) and self.right.evaluate(valuation)

    def atoms(self) -> Set[Any]:
        return self.left.atoms() | self.right.atoms()

    def __str__(self) -> str:
        return f"({self.left} & {self.right})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Conj) and self.left == other.left and self.right == other.right

    def __hash__(self) -> int:
        return hash(("Conj", self.left, self.right))


class Disj(Formula):
    """Disjunction (logical OR) of two formulas."""

    def __init__(self, left: Formula, right: Formula):
        self.left = left
        self.right = right

    def evaluate(self, valuation: Dict[Any, bool]) -> bool:
        return self.left.evaluate(valuation) or self.right.evaluate(valuation)

    def atoms(self) -> Set[Any]:
        return self.left.atoms() | self.right.atoms()

    def __str__(self) -> str:
        return f"({self.left} | {self.right})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Disj) and self.left == other.left and self.right == other.right

    def __hash__(self) -> int:
        return hash(("Disj", self.left, self.right))


class Impl(Formula):
    """Logical implication: left implies right."""

    def __init__(self, left: Formula, right: Formula):
        self.left = left
        self.right = right

    def evaluate(self, valuation: Dict[Any, bool]) -> bool:
        return (not self.left.evaluate(valuation)) or self.right.evaluate(valuation)

    def atoms(self) -> Set[Any]:
        return self.left.atoms() | self.right.atoms()

    def __str__(self) -> str:
        return f"({self.left} >> {self.right})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Impl) and self.left == other.left and self.right == other.right

    def __hash__(self) -> int:
        return hash(("Impl", self.left, self.right))


class Iff(Formula):
    """Logical equivalence (if and only if)."""

    def __init__(self, left: Formula, right: Formula):
        self.left = left
        self.right = right

    def evaluate(self, valuation: Dict[Any, bool]) -> bool:
        return self.left.evaluate(valuation) == self.right.evaluate(valuation)

    def atoms(self) -> Set[Any]:
        return self.left.atoms() | self.right.atoms()

    def __str__(self) -> str:
        return f"({self.left} <-> {self.right})"

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, Iff) and self.left == other.left and self.right == other.right

    def __hash__(self) -> int:
        return hash(("Iff", self.left, self.right))


def foIb(valuation: Dict[Any, bool], f: Formula) -> bool:
    """
    Evaluate a formula f under a boolean valuation.
    Mirrors the Coq Fixpoint foIb definition.
    """
    return f.evaluate(valuation)


def all_valuations(atoms_set: Set[Any]) -> Iterator[Dict[Any, bool]]:
    """Yield all 2^n possible truth valuations over the given set of atoms."""
    sorted_atoms = sorted(list(atoms_set), key=lambda x: str(x))
    for values in itertools.product([False, True], repeat=len(sorted_atoms)):
        yield dict(zip(sorted_atoms, values))


def truth_table(f: Formula) -> List[Tuple[Dict[Any, bool], bool]]:
    """Compute the full truth table of formula f."""
    var_set = f.atoms()
    table = []
    for val in all_valuations(var_set):
        result = f.evaluate(val)
        table.append((val, result))
    return table


def is_tautology(f: Formula) -> bool:
    """Return True if f is true under every valuation."""
    for val in all_valuations(f.atoms()):
        if not f.evaluate(val):
            return False
    return True


def is_contradiction(f: Formula) -> bool:
    """Return True if f is false under every valuation."""
    for val in all_valuations(f.atoms()):
        if f.evaluate(val):
            return False
    return True


def is_satisfiable(f: Formula) -> bool:
    """Return True if f is true under at least one valuation."""
    for val in all_valuations(f.atoms()):
        if f.evaluate(val):
            return True
    return False


def find_model(f: Formula) -> Optional[Dict[Any, bool]]:
    """Return a satisfying valuation (model) if f is satisfiable, or None."""
    for val in all_valuations(f.atoms()):
        if f.evaluate(val):
            return val
    return None


def to_nnf(f: Formula) -> Formula:
    """
    Convert a formula to Negation Normal Form (NNF).
    In NNF, negations appear only immediately before atomic propositions,
    and connectives are limited to Not, Conj, and Disj (with Bot/Top).
    """
    if isinstance(f, (Atom, Bot, Top)):
        return f
    elif isinstance(f, Impl):
        # A >> B is equivalent to ~A | B
        return to_nnf(Disj(Not(f.left), f.right))
    elif isinstance(f, Iff):
        # A <-> B is equivalent to (A & B) | (~A & ~B)
        left_nnf = to_nnf(f.left)
        right_nnf = to_nnf(f.right)
        return Disj(Conj(left_nnf, right_nnf), Conj(to_nnf(Not(left_nnf)), to_nnf(Not(right_nnf))))
    elif isinstance(f, Conj):
        return Conj(to_nnf(f.left), to_nnf(f.right))
    elif isinstance(f, Disj):
        return Disj(to_nnf(f.left), to_nnf(f.right))
    elif isinstance(f, Not):
        inner = f.inner
        if isinstance(inner, Atom):
            return f
        elif isinstance(inner, Bot):
            return Top()
        elif isinstance(inner, Top):
            return Bot()
        elif isinstance(inner, Not):
            # Double negation elimination: ~~A is A
            return to_nnf(inner.inner)
        elif isinstance(inner, Conj):
            # De Morgan: ~(A & B) is ~A | ~B
            return Disj(to_nnf(Not(inner.left)), to_nnf(Not(inner.right)))
        elif isinstance(inner, Disj):
            # De Morgan: ~(A | B) is ~A & ~B
            return Conj(to_nnf(Not(inner.left)), to_nnf(Not(inner.right)))
        elif isinstance(inner, Impl):
            # ~(A >> B) is A & ~B
            return Conj(to_nnf(inner.left), to_nnf(Not(inner.right)))
        elif isinstance(inner, Iff):
            # ~(A <-> B) is (A & ~B) | (~A & B)
            return Disj(Conj(to_nnf(inner.left), to_nnf(Not(inner.right))),
                        Conj(to_nnf(Not(inner.left)), to_nnf(inner.right)))
    raise ValueError(f"Unknown formula type: {type(f)}")


def _distribute_or_over_and(f1: Formula, f2: Formula) -> Formula:
    """Helper to distribute OR over AND: (A & B) | C => (A | C) & (B | C)."""
    if isinstance(f1, Conj):
        return Conj(_distribute_or_over_and(f1.left, f2), _distribute_or_over_and(f1.right, f2))
    if isinstance(f2, Conj):
        return Conj(_distribute_or_over_and(f1, f2.left), _distribute_or_over_and(f1, f2.right))
    return Disj(f1, f2)


def to_cnf_formula(f: Formula) -> Formula:
    """Convert a propositional formula to an equivalent CNF Formula."""
    nnf = to_nnf(f)

    def _cnf(form: Formula) -> Formula:
        if isinstance(form, (Atom, Bot, Top)):
            return form
        if isinstance(form, Not) and isinstance(form.inner, Atom):
            return form
        if isinstance(form, Conj):
            return Conj(_cnf(form.left), _cnf(form.right))
        if isinstance(form, Disj):
            c_left = _cnf(form.left)
            c_right = _cnf(form.right)
            return _distribute_or_over_and(c_left, c_right)
        return form

    return _cnf(nnf)


def _distribute_and_over_or(f1: Formula, f2: Formula) -> Formula:
    """Helper to distribute AND over OR: (A | B) & C => (A & C) | (B & C)."""
    if isinstance(f1, Disj):
        return Disj(_distribute_and_over_or(f1.left, f2), _distribute_and_over_or(f1.right, f2))
    if isinstance(f2, Disj):
        return Disj(_distribute_and_over_or(f1, f2.left), _distribute_and_over_or(f1, f2.right))
    return Conj(f1, f2)


def to_dnf_formula(f: Formula) -> Formula:
    """Convert a propositional formula to an equivalent DNF Formula."""
    nnf = to_nnf(f)

    def _dnf(form: Formula) -> Formula:
        if isinstance(form, (Atom, Bot, Top)):
            return form
        if isinstance(form, Not) and isinstance(form.inner, Atom):
            return form
        if isinstance(form, Disj):
            return Disj(_dnf(form.left), _dnf(form.right))
        if isinstance(form, Conj):
            d_left = _dnf(form.left)
            d_right = _dnf(form.right)
            return _distribute_and_over_or(d_left, d_right)
        return form

    return _dnf(nnf)


# Literal representation for SAT solving:
# Tuple[Any, bool] where (var_name, is_positive)
Literal = Tuple[Any, bool]
Clause = Set[Literal]


def formula_to_clauses(f: Formula) -> List[Clause]:
    """Convert a formula in CNF into a list of clauses (sets of literals)."""
    cnf = to_cnf_formula(f)

    def extract_conjunctions(form: Formula) -> List[Formula]:
        if isinstance(form, Conj):
            return extract_conjunctions(form.left) + extract_conjunctions(form.right)
        return [form]

    def extract_disjunctions(form: Formula) -> Clause:
        if isinstance(form, Disj):
            return extract_disjunctions(form.left) | extract_disjunctions(form.right)
        if isinstance(form, Atom):
            return {(form.name, True)}
        if isinstance(form, Not) and isinstance(form.inner, Atom):
            return {(form.inner.name, False)}
        if isinstance(form, Bot):
            return set()  # empty clause
        if isinstance(form, Top):
            # Tautology clause, can be ignored in SAT or represented with dummy
            return set()
        raise ValueError(f"Unexpected subformula in CNF clause: {form}")

    clauses = []
    for disj in extract_conjunctions(cnf):
        clause = extract_disjunctions(disj)
        clauses.append(clause)
    return clauses


def dpll_solve(clauses: List[Clause], model: Optional[Dict[Any, bool]] = None) -> Optional[Dict[Any, bool]]:
    """
    Davis-Putnam-Logemann-Loveland (DPLL) SAT solver.
    Returns a satisfying assignment (model) or None if unsatisfiable.
    """
    if model is None:
        model = {}

    # Simplify clauses given current assignment
    simplified_clauses: List[Clause] = []
    for c in clauses:
        clause_satisfied = False
        new_c: Clause = set()
        for var, is_pos in c:
            if var in model:
                if model[var] == is_pos:
                    clause_satisfied = True
                    break
            else:
                new_c.add((var, is_pos))
        if not clause_satisfied:
            if not new_c and c:  # Became empty clause from unsatisfaction
                return None
            simplified_clauses.append(new_c)

    # If no clauses remain, all clauses are satisfied
    if not simplified_clauses:
        return model

    # If any clause is empty, it's a contradiction
    for c in simplified_clauses:
        if len(c) == 0:
            return None

    # 1. Unit Propagation
    unit_clauses = [c for c in simplified_clauses if len(c) == 1]
    if unit_clauses:
        unit_lit = next(iter(unit_clauses[0]))
        var, is_pos = unit_lit
        next_model = dict(model)
        next_model[var] = is_pos
        return dpll_solve(simplified_clauses, next_model)

    # 2. Pure Literal Elimination
    all_literals = set().union(*simplified_clauses)
    all_vars = {var for var, _ in all_literals}
    pure_literals: Dict[Any, bool] = {}
    for v in all_vars:
        has_pos = (v, True) in all_literals
        has_neg = (v, False) in all_literals
        if has_pos and not has_neg:
            pure_literals[v] = True
        elif has_neg and not has_pos:
            pure_literals[v] = False

    if pure_literals:
        next_model = dict(model)
        next_model.update(pure_literals)
        return dpll_solve(simplified_clauses, next_model)

    # 3. Branching / Split
    chosen_var = next(iter(all_vars))
    # Try True
    try_true = dict(model)
    try_true[chosen_var] = True
    res = dpll_solve(simplified_clauses, try_true)
    if res is not None:
        return res

    # Try False
    try_false = dict(model)
    try_false[chosen_var] = False
    return dpll_solve(simplified_clauses, try_false)


def sat_solve(f: Formula) -> Optional[Dict[Any, bool]]:
    """Solve satisfiability for formula f using CNF conversion and DPLL."""
    clauses = formula_to_clauses(f)
    return dpll_solve(clauses)
