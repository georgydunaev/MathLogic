"""
Herbrand Theory, Skolemization, Robinson Unification, and Semantic Tableaux.

This module formalizes and implements:
- Robinson First-Order Syntactic Unification with Occurs-Check
- Prenex Normal Form (PNF) conversion via explicit quantifier movement rules
- Dual Skolemization and Herbrandization
- First-Order Signature Extraction (constants, function arities, predicate arities)
- Herbrand Universe construction (H_0, H_k, inductive strata, lazy streams)
- Herbrand Base generation
- Herbrand Expansion and Ground Instance Generation
- Herbrand Expansion Theorem Prover (refutation via DPLL over ground instances)
- Free-Variable Semantic Tableau Prover (Alpha, Beta, Delta, Gamma rules with global MGU unification)
"""

from typing import Union, Dict, Set, List, Tuple, Optional, Any, Callable, Iterator
import itertools

from FirstOrder import (
    Term, Var, Const, Fn,
    FoFormula, Pred, Eq, FoBot, FoTop, FoNot, FoConj, FoDisj, FoImpl, FoIff,
    Forall, Exists, FoLiteral, FoClause,
    _fresh_var, compose_substitutions, unify_terms, unify_predicates,
    to_nnf, standardize_apart_formula, to_cnf_matrix, formula_to_clauses,
)
from Propositional import dpll_solve, Clause as PropClause


# -------------------------------------------------------------
# 1. Robinson First-Order Syntactic Unification with Occurs-Check
# -------------------------------------------------------------

def robinson_unify(
    t1: Term,
    t2: Term,
    subst: Optional[Dict[str, Term]] = None
) -> Optional[Dict[str, Term]]:
    """
    Compute the Most General Unifier (MGU) of two first-order terms
    using Robinson's syntactic unification algorithm with strict occurs-check.
    Returns the MGU substitution dictionary, or None if the terms are not unifiable.
    """
    return unify_terms(t1, t2, subst)


def robinson_unify_all(
    terms: List[Term],
    subst: Optional[Dict[str, Term]] = None
) -> Optional[Dict[str, Term]]:
    """
    Compute the MGU that simultaneously unifies all terms in a list.
    Returns None if any pair fails to unify.
    """
    if not terms:
        return subst or {}
    cur_subst = subst or {}
    first = terms[0]
    for other in terms[1:]:
        new_subst = robinson_unify(first, other, cur_subst)
        if new_subst is None:
            return None
        cur_subst = new_subst
    return cur_subst


def robinson_unify_predicates(
    p1: Pred,
    p2: Pred,
    subst: Optional[Dict[str, Term]] = None
) -> Optional[Dict[str, Term]]:
    """
    Compute the MGU of two atomic predicate formulas P(t_1, ..., t_n) and Q(s_1, ..., s_n).
    Returns None if predicate names or arities differ, or if arguments fail to unify.
    """
    return unify_predicates(p1, p2, subst)


def robinson_unify_atoms(
    a1: FoFormula,
    a2: FoFormula,
    subst: Optional[Dict[str, Term]] = None
) -> Optional[Dict[str, Term]]:
    """
    Unify two atomic first-order formulas (Pred or Eq).
    Returns MGU substitution or None.
    """
    if isinstance(a1, Pred) and isinstance(a2, Pred):
        return robinson_unify_predicates(a1, a2, subst)
    elif isinstance(a1, Eq) and isinstance(a2, Eq):
        cur = robinson_unify(a1.left, a2.left, subst)
        if cur is None:
            return None
        return robinson_unify(a1.right, a2.right, cur)
    return None


# -------------------------------------------------------------
# 2. First-Order Signature Extraction
# -------------------------------------------------------------

class FolSignature:
    """
    Represents a first-order logic signature:
    - constants: set of constant terms (Const)
    - functions: mapping of function symbol names to their integer arities
    - predicates: mapping of predicate symbol names to their integer arities
    """

    def __init__(
        self,
        constants: Optional[Set[Const]] = None,
        functions: Optional[Dict[str, int]] = None,
        predicates: Optional[Dict[str, int]] = None,
    ):
        self.constants: Set[Const] = set(constants or [])
        self.functions: Dict[str, int] = dict(functions or {})
        self.predicates: Dict[str, int] = dict(predicates or {})

    def add_constant(self, c: Const) -> None:
        self.constants.add(c)

    def add_function(self, name: str, arity: int) -> None:
        if name in self.functions and self.functions[name] != arity:
            raise ValueError(
                f"Conflicting arity for function {name}: existing {self.functions[name]} vs new {arity}"
            )
        self.functions[name] = arity

    def add_predicate(self, name: str, arity: int) -> None:
        if name in self.predicates and self.predicates[name] != arity:
            raise ValueError(
                f"Conflicting arity for predicate {name}: existing {self.predicates[name]} vs new {arity}"
            )
        self.predicates[name] = arity

    def ensure_non_empty_domain(self, default_name: str = "c_0") -> Const:
        """
        Herbrand universe requires at least one constant symbol.
        If no constants are present, inject a default constant.
        """
        if not self.constants:
            default_c = Const(default_name)
            self.constants.add(default_c)
            return default_c
        return next(iter(self.constants))

    def __repr__(self) -> str:
        consts_str = "{" + ", ".join(c.name for c in sorted(self.constants, key=lambda c: c.name)) + "}"
        return f"FolSignature(constants={consts_str}, functions={self.functions}, predicates={self.predicates})"


def extract_fol_signature(
    items: Union[FoFormula, FoClause, List[Union[FoFormula, FoClause]], Set[Union[FoFormula, FoClause]]],
    default_constant: Optional[str] = "c_0"
) -> FolSignature:
    """
    Extract the first-order signature (constants, functions, predicates)
    from formulas or clauses.
    If default_constant is provided and no constants occur, injects the default constant.
    """
    sig = FolSignature()

    def _visit_term(t: Term) -> None:
        if isinstance(t, Const):
            sig.add_constant(t)
        elif isinstance(t, Fn):
            sig.add_function(t.name, len(t.args))
            for arg in t.args:
                _visit_term(arg)
        elif isinstance(t, Var):
            pass

    def _visit_formula(f: FoFormula) -> None:
        if isinstance(f, Pred):
            sig.add_predicate(f.name, len(f.args))
            for a in f.args:
                _visit_term(a)
        elif isinstance(f, Eq):
            sig.add_predicate("=", 2)
            _visit_term(f.left)
            _visit_term(f.right)
        elif isinstance(f, FoNot):
            _visit_formula(f.inner)
        elif isinstance(f, (FoConj, FoDisj, FoImpl, FoIff)):
            _visit_formula(f.left)
            _visit_formula(f.right)
        elif isinstance(f, (Forall, Exists)):
            _visit_formula(f.body)
        elif isinstance(f, (FoBot, FoTop)):
            pass

    def _visit_clause(c: FoClause) -> None:
        for lit in c.literals:
            _visit_formula(lit.pred)

    if isinstance(items, (list, tuple, set)):
        item_list = list(items)
    else:
        item_list = [items]

    for item in item_list:
        if isinstance(item, FoClause):
            _visit_clause(item)
        elif isinstance(item, FoFormula):
            _visit_formula(item)
        elif isinstance(item, FoLiteral):
            _visit_formula(item.pred)

    if default_constant is not None:
        sig.ensure_non_empty_domain(default_constant)

    return sig


# -------------------------------------------------------------
# 3. Prenex Normal Form via Quantifier Movement Rules
# -------------------------------------------------------------

def is_prenex(formula: FoFormula) -> bool:
    """
    Check if a formula is in Prenex Normal Form (Q1 x1. ... Qn xn. Matrix),
    where Matrix contains no quantifiers.
    """
    cur = formula
    while isinstance(cur, (Forall, Exists)):
        cur = cur.body

    def _contains_quantifiers(f: FoFormula) -> bool:
        if isinstance(f, (Forall, Exists)):
            return True
        if isinstance(f, FoNot):
            return _contains_quantifiers(f.inner)
        if isinstance(f, (FoConj, FoDisj, FoImpl, FoIff)):
            return _contains_quantifiers(f.left) or _contains_quantifiers(f.right)
        return False

    return not _contains_quantifiers(cur)


def split_prenex(formula: FoFormula) -> Tuple[List[Tuple[str, str]], FoFormula]:
    """
    Decompose a prenex formula into a quantifier prefix list [("forall"|"exists", var)]
    and the quantifier-free matrix.
    """
    quants: List[Tuple[str, str]] = []
    cur = formula
    while isinstance(cur, (Forall, Exists)):
        if isinstance(cur, Forall):
            quants.append(("forall", cur.var))
        else:
            quants.append(("exists", cur.var))
        cur = cur.body
    return quants, cur


def to_prenex_by_movement(formula: FoFormula) -> FoFormula:
    """
    Convert an arbitrary first-order formula into Prenex Normal Form (PNF)
    using classical quantifier movement rules, preserving logical equivalence
    without requiring prior conversion to NNF:
    - Negation:
      ~forall x. A === exists x. ~A
      ~exists x. A === forall x. ~A
    - Conjunction:
      (Q x. A) & B === Q x'. (A[x -> x'] & B)
      A & (Q x. B) === Q x'. (A & B[x -> x'])
    - Disjunction:
      (Q x. A) | B === Q x'. (A[x -> x'] | B)
      A | (Q x. B) === Q x'. (A | B[x -> x'])
    - Implication:
      (Q x. A) >> B === ~Q x'. (A[x -> x'] >> B)  (Quantifier flips in antecedent!)
      A >> (Q x. B) === Q x'. (A >> B[x -> x'])
    - Equivalence:
      A <-> B is first expanded to (A >> B) & (B >> A).
    """
    # Standardize apart first to guarantee all bound variables are globally distinct
    std_formula = standardize_apart_formula(formula)
    used_vars = set(std_formula.free_vars()) | set(std_formula.bound_vars())

    def _fresh(base: str) -> str:
        nonlocal used_vars
        nv = _fresh_var(base, used_vars)
        used_vars.add(nv)
        return nv

    def _extract(f: FoFormula) -> Tuple[List[Tuple[str, str]], FoFormula]:
        if isinstance(f, (FoBot, FoTop, Pred, Eq)):
            return [], f

        elif isinstance(f, Forall):
            quants, matrix = _extract(f.body)
            return [("forall", f.var)] + quants, matrix

        elif isinstance(f, Exists):
            quants, matrix = _extract(f.body)
            return [("exists", f.var)] + quants, matrix

        elif isinstance(f, FoNot):
            quants, matrix = _extract(f.inner)
            # Invert quantifiers: forall <-> exists
            flipped = [("exists" if q == "forall" else "forall", v) for q, v in quants]
            return flipped, FoNot(matrix)

        elif isinstance(f, FoConj):
            q_left, m_left = _extract(f.left)
            q_right, m_right = _extract(f.right)
            return q_left + q_right, FoConj(m_left, m_right)

        elif isinstance(f, FoDisj):
            q_left, m_left = _extract(f.left)
            q_right, m_right = _extract(f.right)
            return q_left + q_right, FoDisj(m_left, m_right)

        elif isinstance(f, FoImpl):
            q_left, m_left = _extract(f.left)
            q_right, m_right = _extract(f.right)
            # Quantifier in antecedent flips polarity: forall <-> exists
            flipped_left = [("exists" if q == "forall" else "forall", v) for q, v in q_left]
            return flipped_left + q_right, FoImpl(m_left, m_right)

        elif isinstance(f, FoIff):
            # Expand to conjunction of implications
            expanded = FoConj(FoImpl(f.left, f.right), FoImpl(f.right, f.left))
            return _extract(expanded)

        else:
            raise ValueError(f"Unknown formula type in prenex movement: {type(f)}")

    quants, matrix = _extract(std_formula)

    res = matrix
    for q_kind, q_var in reversed(quants):
        if q_kind == "forall":
            res = Forall(q_var, res)
        else:
            res = Exists(q_var, res)
    return res


def prenex_normal_form(formula: FoFormula, use_nnf: bool = False) -> FoFormula:
    """
    Top-level converter to Prenex Normal Form.
    If use_nnf is True, pushes negations inside first.
    Otherwise applies direct quantifier movement rules.
    """
    if use_nnf:
        nnf = to_nnf(formula)
        return to_prenex_by_movement(nnf)
    return to_prenex_by_movement(formula)


# -------------------------------------------------------------
# 4. Dual Skolemization and Herbrandization
# -------------------------------------------------------------

def skolemize_formula(
    formula: FoFormula,
    drop_universal: bool = False,
    prefix: str = "sk"
) -> FoFormula:
    """
    Convert a first-order formula into Skolem Normal Form (SNF) for satisfiability/refutation:
    Existential variables are replaced with Skolem functions depending on
    all governing universally quantified variables in whose scope they appear.
    If drop_universal is True, returns the quantifier-free matrix (implicitly universally quantified).
    """
    prenex = to_prenex_by_movement(formula)
    quants, matrix = split_prenex(prenex)

    univ_vars: List[str] = []
    subst_map: Dict[str, Term] = {}
    skolem_id = 1

    for q_kind, q_var in quants:
        if q_kind == "forall":
            univ_vars.append(q_var)
        else:
            # Existential quantifier
            if not univ_vars:
                sk_term: Term = Const(f"{prefix}_c_{skolem_id}")
            else:
                sk_term = Fn(f"{prefix}_f_{skolem_id}", [Var(v) for v in univ_vars])
            skolem_id += 1
            subst_map[q_var] = sk_term

    skolemized_matrix = matrix.subst(subst_map)

    if drop_universal or not univ_vars:
        return skolemized_matrix

    res = skolemized_matrix
    for v in reversed(univ_vars):
        res = Forall(v, res)
    return res


def herbrandize_formula(
    formula: FoFormula,
    drop_existential: bool = False,
    prefix: str = "hb"
) -> FoFormula:
    """
    Dual Skolemization (Herbrandization) for direct validity checking:
    Universal variables are replaced with Herbrand functions depending on
    all governing existentially quantified variables in whose scope they appear.
    The resulting purely existential formula is valid iff the original formula is valid.
    Mathematically: Herbrandize(phi) === ~Skolemize(~phi).
    """
    prenex = to_prenex_by_movement(formula)
    quants, matrix = split_prenex(prenex)

    exist_vars: List[str] = []
    subst_map: Dict[str, Term] = {}
    herbrand_id = 1

    for q_kind, q_var in quants:
        if q_kind == "exists":
            exist_vars.append(q_var)
        else:
            # Universal quantifier
            if not exist_vars:
                hb_term: Term = Const(f"{prefix}_c_{herbrand_id}")
            else:
                hb_term = Fn(f"{prefix}_f_{herbrand_id}", [Var(v) for v in exist_vars])
            herbrand_id += 1
            subst_map[q_var] = hb_term

    herbrandized_matrix = matrix.subst(subst_map)

    if drop_existential or not exist_vars:
        return herbrandized_matrix

    res = herbrandized_matrix
    for v in reversed(exist_vars):
        res = Exists(v, res)
    return res


def skolemize_to_clauses(formula: FoFormula) -> List[FoClause]:
    """
    Complete clausal pipeline:
    Skolemizes a formula, converts its matrix to CNF, and returns a list of FoClauses.
    """
    return formula_to_clauses(formula)


# -------------------------------------------------------------
# 5. Herbrand Universe Construction
# -------------------------------------------------------------

def herbrand_universe_level(
    constants: Set[Const],
    functions: Dict[str, int],
    level: int = 0
) -> List[Term]:
    """
    Construct the Herbrand Universe H_level up to depth 'level':
    - H_0 = constants (if constants is empty, {Const("c_0")})
    - H_{k+1} = H_k U { f(t_1, ..., t_n) | f/n in functions, t_i in H_k }
    Returns a sorted, deduplicated list of ground terms.
    """
    if not constants:
        current_terms: Set[Term] = {Const("c_0")}
    else:
        current_terms = set(constants)

    all_terms: Set[Term] = set(current_terms)

    for _ in range(level):
        new_terms: Set[Term] = set()
        for fn_name, arity in functions.items():
            if arity == 0:
                new_terms.add(Const(fn_name))
            else:
                for arg_tuple in itertools.product(all_terms, repeat=arity):
                    new_terms.add(Fn(fn_name, arg_tuple))
        if not new_terms.issubset(all_terms):
            all_terms.update(new_terms)
        else:
            break

    return sorted(list(all_terms), key=lambda t: (len(str(t)), str(t)))


def herbrand_universe_strata(
    constants: Set[Const],
    functions: Dict[str, int],
    max_level: int = 2
) -> List[List[Term]]:
    """
    Return the Herbrand Universe partitioned into generation strata:
    [S_0, S_1, ..., S_max_level], where S_0 = H_0 and S_{k+1} = H_{k+1} \\ H_k.
    """
    strata: List[List[Term]] = []
    seen: Set[Term] = set()

    base = set(constants) if constants else {Const("c_0")}
    strata.append(sorted(list(base), key=lambda t: str(t)))
    seen.update(base)

    for _ in range(max_level):
        layer: Set[Term] = set()
        for fn_name, arity in functions.items():
            if arity == 0:
                term = Const(fn_name)
                if term not in seen:
                    layer.add(term)
            else:
                for arg_tuple in itertools.product(seen, repeat=arity):
                    term = Fn(fn_name, arg_tuple)
                    if term not in seen:
                        layer.add(term)
        if not layer:
            break
        strata.append(sorted(list(layer), key=lambda t: (len(str(t)), str(t))))
        seen.update(layer)

    return strata


def herbrand_universe_stream(
    constants: Set[Const],
    functions: Dict[str, int]
) -> Iterator[Term]:
    """
    Infinite generator yielding all terms of the Herbrand Universe
    in breadth-first level order without duplicates.
    """
    seen: Set[Term] = set()
    current_level: Set[Term] = set(constants) if constants else {Const("c_0")}

    for t in sorted(list(current_level), key=lambda x: str(x)):
        seen.add(t)
        yield t

    if not functions:
        return

    while True:
        next_level: Set[Term] = set()
        for fn_name, arity in functions.items():
            if arity == 0:
                term = Const(fn_name)
                if term not in seen:
                    next_level.add(term)
            else:
                for arg_tuple in itertools.product(seen, repeat=arity):
                    term = Fn(fn_name, arg_tuple)
                    if term not in seen:
                        next_level.add(term)
        if not next_level:
            break
        for t in sorted(list(next_level), key=lambda x: (len(str(x)), str(x))):
            seen.add(t)
            yield t


def herbrand_universe(
    signature_or_items: Union[FolSignature, FoFormula, FoClause, List[Any]],
    max_level: int = 1
) -> List[Term]:
    """
    Convenience wrapper: construct the Herbrand Universe up to max_level
    from a signature or a collection of formulas/clauses.
    """
    if isinstance(signature_or_items, FolSignature):
        sig = signature_or_items
    else:
        sig = extract_fol_signature(signature_or_items)
    return herbrand_universe_level(sig.constants, sig.functions, max_level)


# -------------------------------------------------------------
# 6. Herbrand Base Generation
# -------------------------------------------------------------

def herbrand_base_level(
    predicates: Dict[str, int],
    terms: List[Term]
) -> List[Pred]:
    """
    Generate the Herbrand Base B(terms): all ground atomic formulas
    P(t_1, ..., t_n) where P/n is in predicates and t_i are in terms.
    """
    atoms: List[Pred] = []
    for pred_name, arity in predicates.items():
        if pred_name == "=":
            continue
        if arity == 0:
            atoms.append(Pred(pred_name, []))
        else:
            for arg_tuple in itertools.product(terms, repeat=arity):
                atoms.append(Pred(pred_name, list(arg_tuple)))
    return atoms


def herbrand_base(
    signature_or_items: Union[FolSignature, FoFormula, FoClause, List[Any]],
    max_level: int = 1
) -> List[Pred]:
    """
    Generate the Herbrand Base for a signature up to the given universe level.
    """
    if isinstance(signature_or_items, FolSignature):
        sig = signature_or_items
    else:
        sig = extract_fol_signature(signature_or_items)
    terms = herbrand_universe_level(sig.constants, sig.functions, max_level)
    return herbrand_base_level(sig.predicates, terms)


# -------------------------------------------------------------
# 7. Ground Instances & Herbrand Expansion Prover
# -------------------------------------------------------------

def ground_instances_of_clause(
    clause: FoClause,
    ground_terms: List[Term]
) -> List[FoClause]:
    """
    Generate all ground instances of a clause under a finite set of ground terms.
    If the clause has no variables, returns [clause].
    """
    clause_vars = sorted(list(clause.vars()))
    if not clause_vars:
        return [clause]

    instances: List[FoClause] = []
    for term_tuple in itertools.product(ground_terms, repeat=len(clause_vars)):
        subst = {var_name: t for var_name, t in zip(clause_vars, term_tuple)}
        instances.append(clause.subst(subst))
    return instances


def ground_instances_of_clauses(
    clauses: List[FoClause],
    ground_terms: List[Term]
) -> List[FoClause]:
    """
    Generate all ground instances for a collection of clauses.
    """
    instances: List[FoClause] = []
    for c in clauses:
        instances.extend(ground_instances_of_clause(c, ground_terms))
    return instances


class HerbrandExpansionProver:
    """
    Theorem Prover based on Herbrand's Theorem (1930):
    A set of first-order clauses S is unsatisfiable if and only if
    there exists a finite set of ground instances of S that is
    propositionally unsatisfiable.

    This prover expands ground instances stratum by stratum over H_0, H_1, ...
    and applies DPLL SAT solving at each expansion step.
    """

    def __init__(self, clauses: List[FoClause], signature: Optional[FolSignature] = None):
        self.clauses = clauses
        self.signature = signature or extract_fol_signature(clauses)
        self.log: List[str] = [f"Initialized Herbrand Expansion Prover with {len(clauses)} clause(s)."]

    def prove(self, max_level: int = 3) -> Tuple[bool, List[str]]:
        """
        Attempt to refute the clause set by enumerating ground instances
        over Herbrand universe levels H_0, ..., H_max_level.
        Returns (proved, log).
        """
        all_ground_clauses: Set[FoClause] = set()

        for level in range(max_level + 1):
            h_terms = herbrand_universe_level(self.signature.constants, self.signature.functions, level)
            self.log.append(f"Level {level}: |H_{level}| = {len(h_terms)} ground terms: {[str(t) for t in h_terms]}")

            # Generate ground instances of all clauses using h_terms
            current_ground = ground_instances_of_clauses(self.clauses, h_terms)
            all_ground_clauses.update(current_ground)
            self.log.append(f"Level {level}: Total accumulated ground clauses = {len(all_ground_clauses)}")

            # Check if empty clause is directly present
            if any(gc.is_empty() for gc in all_ground_clauses):
                self.log.append(f"Empty clause derived at Herbrand level {level}. Refutation complete.")
                return True, self.log

            # Encode ground clauses into propositional logic for DPLL
            atom_to_id: Dict[str, int] = {}
            id_counter = 1
            prop_clauses: List[PropClause] = []

            for gc in all_ground_clauses:
                p_clause: Set[Tuple[int, bool]] = set()
                for lit in gc.literals:
                    atom_key = str(lit.pred)
                    if atom_key not in atom_to_id:
                        atom_to_id[atom_key] = id_counter
                        id_counter += 1
                    p_clause.add((atom_to_id[atom_key], lit.is_positive))
                prop_clauses.append(p_clause)

            # Test propositional satisfiability via DPLL
            sat_model = dpll_solve(prop_clauses)
            if sat_model is None:
                self.log.append(
                    f"DPLL refutation succeeded at Herbrand level {level} "
                    f"({len(prop_clauses)} ground instances, {len(atom_to_id)} propositional atoms). "
                    f"Clause set is unsatisfiable."
                )
                return True, self.log
            else:
                self.log.append(f"Level {level}: Propositionally satisfiable. Proceeding to next level.")

        self.log.append(f"Herbrand expansion bound (max_level={max_level}) reached without refutation.")
        return False, self.log

    def prove_validity(self, formula: FoFormula, max_level: int = 3) -> Tuple[bool, List[str]]:
        """
        Prove validity of a formula by refuting the clausal form of its negation.
        """
        negated = FoNot(formula)
        clauses = formula_to_clauses(negated)
        self.clauses = clauses
        self.signature = extract_fol_signature(clauses)
        self.log = [f"Refuting negation of goal: ~({formula})"]
        return self.prove(max_level=max_level)


def prove_by_herbrand_expansion(
    formula_or_clauses: Union[FoFormula, List[FoClause]],
    max_level: int = 3
) -> Tuple[bool, List[str]]:
    """
    Prove validity of a formula or unsatisfiability of a clause set
    using Herbrand expansion and propositional DPLL refutation.
    """
    if isinstance(formula_or_clauses, FoFormula):
        negated = FoNot(formula_or_clauses)
        clauses = formula_to_clauses(negated)
    else:
        clauses = formula_or_clauses

    prover = HerbrandExpansionProver(clauses)
    return prover.prove(max_level=max_level)


# -------------------------------------------------------------
# 8. Free-Variable Semantic Tableaux with Robinson Unification
# -------------------------------------------------------------

class FvSignedFormula:
    """A signed formula for Free-Variable Tableaux: sign (True=T, False=F) and FoFormula."""

    def __init__(self, formula: FoFormula, sign: bool):
        self.formula = formula
        self.sign = sign

    def subst(self, mapping: Dict[str, Term]) -> "FvSignedFormula":
        return FvSignedFormula(self.formula.subst(mapping), self.sign)

    def free_vars(self) -> Set[str]:
        return self.formula.free_vars()

    def __eq__(self, other: Any) -> bool:
        return isinstance(other, FvSignedFormula) and self.sign == other.sign and self.formula == other.formula

    def __hash__(self) -> int:
        return hash(("FvSignedFormula", self.sign, self.formula))

    def __str__(self) -> str:
        s = "T" if self.sign else "F"
        return f"{s}({self.formula})"

    def __repr__(self) -> str:
        return str(self)


class FvTableauBranch:
    """
    A single branch in a Free-Variable Semantic Tableau.
    Contains signed formulas with free variables and tracks gamma instantiations.
    """

    def __init__(
        self,
        formulas: Optional[List[FvSignedFormula]] = None,
        gamma_counts: Optional[Dict[FvSignedFormula, int]] = None
    ):
        self.formulas: List[FvSignedFormula] = list(formulas or [])
        self.gamma_counts: Dict[FvSignedFormula, int] = dict(gamma_counts or {})
        self.is_closed: bool = False
        self.closure_reason: Optional[str] = None

    def free_vars(self) -> Set[str]:
        res: Set[str] = set()
        for sf in self.formulas:
            res |= sf.free_vars()
        return res

    def subst(self, mapping: Dict[str, Term]) -> "FvTableauBranch":
        new_formulas = [sf.subst(mapping) for sf in self.formulas]
        new_counts = {sf.subst(mapping): cnt for sf, cnt in self.gamma_counts.items()}
        b = FvTableauBranch(new_formulas, new_counts)
        b.is_closed = self.is_closed
        b.closure_reason = self.closure_reason
        return b

    def find_closure_unifiers(self) -> List[Tuple[Dict[str, Term], str]]:
        """
        Find all possible MGU substitutions that close this branch:
        1. T(Bot) or F(Top)
        2. F(t1 = t2) where t1 and t2 unify (reflexivity contradiction)
        3. Complementary atomic pair T(P) and F(Q) unifying via robinson_unify_atoms.
        """
        unifiers: List[Tuple[Dict[str, Term], str]] = []

        for sf in self.formulas:
            if sf.sign and isinstance(sf.formula, FoBot):
                return [({}, "T(Bot)")]
            if not sf.sign and isinstance(sf.formula, FoTop):
                return [({}, "F(Top)")]
            if not sf.sign and isinstance(sf.formula, Eq):
                mgu = robinson_unify(sf.formula.left, sf.formula.right)
                if mgu is not None:
                    unifiers.append((mgu, f"Reflexivity closure on {sf}"))

        pos_atoms = [sf for sf in self.formulas if sf.sign and isinstance(sf.formula, (Pred, Eq))]
        neg_atoms = [sf for sf in self.formulas if not sf.sign and isinstance(sf.formula, (Pred, Eq))]

        for p in pos_atoms:
            for n in neg_atoms:
                mgu = robinson_unify_atoms(p.formula, n.formula)
                if mgu is not None:
                    unifiers.append((mgu, f"Complementary pair {p} and {n} with MGU {mgu}"))

        return unifiers


class FreeVariableTableau:
    """
    First-Order Free-Variable Semantic Tableau Prover.

    Calculus rules:
    - Alpha rules: Propositional non-branching decompositions.
    - Beta rules: Propositional branching decompositions.
    - Delta rules (Skolem): Existential quantifiers are instantiated with
      Skolem terms depending on current branch free variables.
    - Gamma rules (Eigenvariable/Free Variable): Universal quantifiers
      are instantiated with fresh free variables.
    - Closure rule: Unification between complementary atomic formulas
      propagating the MGU globally across all branches.
    """

    def __init__(self, formula: FoFormula, max_gamma_instances: int = 2):
        self.goal = formula
        self.max_gamma_instances = max_gamma_instances
        self.branches: List[FvTableauBranch] = [
            FvTableauBranch([FvSignedFormula(formula, False)])
        ]
        self.log: List[str] = [f"Initialized Free-Variable Tableau with F({formula})"]
        self.var_counter: int = 1
        self.skolem_counter: int = 1

    def _fresh_free_var(self) -> Var:
        v = Var(f"U_{self.var_counter}")
        self.var_counter += 1
        return v

    def _fresh_skolem_term(self, free_vars: Set[str]) -> Term:
        sk_id = self.skolem_counter
        self.skolem_counter += 1
        sorted_vars = sorted(list(free_vars))
        if not sorted_vars:
            return Const(f"sk_c_{sk_id}")
        return Fn(f"sk_f_{sk_id}", [Var(v) for v in sorted_vars])

    def run(self, max_steps: int = 60) -> bool:
        """
        Run the free-variable tableau proof search.
        Returns True if all branches are closed under a global MGU.
        """
        for step in range(max_steps):
            # Check if all branches close simultaneously
            if self._close_tableau():
                self.log.append(f"All branches closed. Proof of {self.goal} complete.")
                return True

            expanded = False

            # Phase 1: Alpha Rules (non-branching propositional)
            for b in self.branches:
                if b.is_closed:
                    continue
                for idx, sf in enumerate(b.formulas):
                    sign, f = sf.sign, sf.formula
                    if sign and isinstance(f, FoConj):
                        b.formulas.pop(idx)
                        b.formulas.append(FvSignedFormula(f.left, True))
                        b.formulas.append(FvSignedFormula(f.right, True))
                        self.log.append(f"Alpha T(&): {f} => T({f.left}), T({f.right})")
                        expanded = True
                        break
                    elif not sign and isinstance(f, FoDisj):
                        b.formulas.pop(idx)
                        b.formulas.append(FvSignedFormula(f.left, False))
                        b.formulas.append(FvSignedFormula(f.right, False))
                        self.log.append(f"Alpha F(|): {f} => F({f.left}), F({f.right})")
                        expanded = True
                        break
                    elif not sign and isinstance(f, FoImpl):
                        b.formulas.pop(idx)
                        b.formulas.append(FvSignedFormula(f.left, True))
                        b.formulas.append(FvSignedFormula(f.right, False))
                        self.log.append(f"Alpha F(>>): {f} => T({f.left}), F({f.right})")
                        expanded = True
                        break
                    elif sign and isinstance(f, FoNot):
                        b.formulas.pop(idx)
                        b.formulas.append(FvSignedFormula(f.inner, False))
                        self.log.append(f"Alpha T(~): {f} => F({f.inner})")
                        expanded = True
                        break
                    elif not sign and isinstance(f, FoNot):
                        b.formulas.pop(idx)
                        b.formulas.append(FvSignedFormula(f.inner, True))
                        self.log.append(f"Alpha F(~): {f} => T({f.inner})")
                        expanded = True
                        break
                if expanded:
                    break

            if expanded:
                continue

            # Phase 2: Delta Rules (Skolem terms for existential formulas)
            for b in self.branches:
                if b.is_closed:
                    continue
                for idx, sf in enumerate(b.formulas):
                    sign, f = sf.sign, sf.formula
                    if (sign and isinstance(f, Exists)) or (not sign and isinstance(f, Forall)):
                        branch_fvs = b.free_vars()
                        sk_term = self._fresh_skolem_term(branch_fvs)
                        inst = f.body.subst({f.var: sk_term})
                        b.formulas.pop(idx)
                        b.formulas.append(FvSignedFormula(inst, sign))
                        rule_name = "Delta T(exists)" if sign else "Delta F(forall)"
                        self.log.append(f"{rule_name}: {f} instantiated with Skolem term {sk_term} => {inst}")
                        expanded = True
                        break
                if expanded:
                    break

            if expanded:
                continue

            # Phase 3: Beta Rules (branching propositional)
            for b_idx, b in enumerate(self.branches):
                if b.is_closed:
                    continue
                for idx, sf in enumerate(b.formulas):
                    sign, f = sf.sign, sf.formula
                    if not sign and isinstance(f, FoConj):
                        b.formulas.pop(idx)
                        b1 = FvTableauBranch(list(b.formulas) + [FvSignedFormula(f.left, False)], b.gamma_counts)
                        b2 = FvTableauBranch(list(b.formulas) + [FvSignedFormula(f.right, False)], b.gamma_counts)
                        self.branches = self.branches[:b_idx] + [b1, b2] + self.branches[b_idx + 1:]
                        self.log.append(f"Beta F(&): {f} branched into F({f.left}) | F({f.right})")
                        expanded = True
                        break
                    elif sign and isinstance(f, FoDisj):
                        b.formulas.pop(idx)
                        b1 = FvTableauBranch(list(b.formulas) + [FvSignedFormula(f.left, True)], b.gamma_counts)
                        b2 = FvTableauBranch(list(b.formulas) + [FvSignedFormula(f.right, True)], b.gamma_counts)
                        self.branches = self.branches[:b_idx] + [b1, b2] + self.branches[b_idx + 1:]
                        self.log.append(f"Beta T(|): {f} branched into T({f.left}) | T({f.right})")
                        expanded = True
                        break
                    elif sign and isinstance(f, FoImpl):
                        b.formulas.pop(idx)
                        b1 = FvTableauBranch(list(b.formulas) + [FvSignedFormula(f.left, False)], b.gamma_counts)
                        b2 = FvTableauBranch(list(b.formulas) + [FvSignedFormula(f.right, True)], b.gamma_counts)
                        self.branches = self.branches[:b_idx] + [b1, b2] + self.branches[b_idx + 1:]
                        self.log.append(f"Beta T(>>): {f} branched into F({f.left}) | T({f.right})")
                        expanded = True
                        break
                    elif sign and isinstance(f, FoIff):
                        b.formulas.pop(idx)
                        b1 = FvTableauBranch(
                            list(b.formulas) + [FvSignedFormula(f.left, True), FvSignedFormula(f.right, True)],
                            b.gamma_counts
                        )
                        b2 = FvTableauBranch(
                            list(b.formulas) + [FvSignedFormula(f.left, False), FvSignedFormula(f.right, False)],
                            b.gamma_counts
                        )
                        self.branches = self.branches[:b_idx] + [b1, b2] + self.branches[b_idx + 1:]
                        self.log.append(f"Beta T(<->): {f} branched into (T,T) | (F,F)")
                        expanded = True
                        break
                    elif not sign and isinstance(f, FoIff):
                        b.formulas.pop(idx)
                        b1 = FvTableauBranch(
                            list(b.formulas) + [FvSignedFormula(f.left, True), FvSignedFormula(f.right, False)],
                            b.gamma_counts
                        )
                        b2 = FvTableauBranch(
                            list(b.formulas) + [FvSignedFormula(f.left, False), FvSignedFormula(f.right, True)],
                            b.gamma_counts
                        )
                        self.branches = self.branches[:b_idx] + [b1, b2] + self.branches[b_idx + 1:]
                        self.log.append(f"Beta F(<->): {f} branched into (T,F) | (F,T)")
                        expanded = True
                        break
                if expanded:
                    break

            if expanded:
                continue

            # Phase 4: Gamma Rules (fresh free variable instantiation)
            for b in self.branches:
                if b.is_closed:
                    continue
                for sf in list(b.formulas):
                    sign, f = sf.sign, sf.formula
                    if (sign and isinstance(f, Forall)) or (not sign and isinstance(f, Exists)):
                        count = b.gamma_counts.get(sf, 0)
                        if count < self.max_gamma_instances:
                            fresh_var = self._fresh_free_var()
                            inst = f.body.subst({f.var: fresh_var})
                            b.gamma_counts[sf] = count + 1
                            b.formulas.append(FvSignedFormula(inst, sign))
                            rule_name = "Gamma T(forall)" if sign else "Gamma F(exists)"
                            self.log.append(f"{rule_name}: {f} instantiated with fresh variable {fresh_var} => {inst}")
                            expanded = True
                            break
                if expanded:
                    break

            if not expanded:
                # Saturation reached without more applicable rules
                break

        # Final closure check
        return self._close_tableau()

    def _close_tableau(self) -> bool:
        """
        Backtracking search over branch closure unifiers to find a global MGU
        that closes every branch in the tableau.
        """
        open_branches = [b for b in self.branches if not b.is_closed]
        if not open_branches:
            return True

        def _backtrack(branch_idx: int, cur_subst: Dict[str, Term]) -> Optional[Dict[str, Term]]:
            if branch_idx >= len(open_branches):
                return cur_subst

            target_branch = open_branches[branch_idx].subst(cur_subst)
            closure_candidates = target_branch.find_closure_unifiers()

            for mgu, reason in closure_candidates:
                composed = compose_substitutions(cur_subst, mgu)
                res = _backtrack(branch_idx + 1, composed)
                if res is not None:
                    return res
            return None

        solution_subst = _backtrack(0, {})
        if solution_subst is not None:
            # Apply solution substitution globally
            self.branches = [b.subst(solution_subst) for b in self.branches]
            for b in self.branches:
                b.is_closed = True
                b.closure_reason = f"Closed under global MGU: {solution_subst}"
            return True

        return False


def prove_by_free_variable_tableau(
    formula: FoFormula,
    max_steps: int = 60,
    max_gamma_instances: int = 2
) -> Tuple[bool, List[str]]:
    """
    Prove validity of a first-order formula using Free-Variable Semantic Tableaux.
    Returns (proved: bool, log: List[str]).
    """
    tableau = FreeVariableTableau(formula, max_gamma_instances=max_gamma_instances)
    proved = tableau.run(max_steps=max_steps)
    return proved, tableau.log
