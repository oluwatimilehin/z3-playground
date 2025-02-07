from typing import List, Dict
import itertools

from z3 import *

operators = ["+", "-"]


def solve_eq(op: str, val: int, target: int):
    x = BitVec("x", 4)
    s = Solver()
    match op:
        case "+":
            s.add(val + x == target)
        case "-":
            s.add(val - x == target)
        case _:
            raise ValueError(f"Unsupported operator")

    if s.check().r != Z3_L_TRUE:
        return None

    return s.model()[x]


def enumerative_synthesis(
    expr, inputs: List[BitVecRef], constants: Dict[BitVecRef, int], target: BitVecVal
):
    zero = BitVecVal(0, 4)
    one = BitVecVal(1, 4)
    minus_one = BitVecVal(-1, 4)
    special_vals = [zero, one, minus_one]
    input_combinations = list(itertools.product(special_vals, repeat=len(inputs)))

    consts_permutation = list(itertools.permutations(constants.keys()))
    inputs_x_consts = list(itertools.product(input_combinations, consts_permutation))

    valid_combos = []

    for combo in inputs_x_consts:
        s = Solver()
        inputs_subst = [(input, combo[0][i]) for i, input in enumerate(inputs)]
        consts_subst = [
            (const, combo[1][i]) for i, const in enumerate(constants.keys())
        ]

        comb = inputs_subst + consts_subst
        subst_expr = substitute(expr, *comb)

        for const, val in constants.items():
            s.add(const == val)
        s.add(subst_expr == target)

        if s.check().r == Z3_L_TRUE:
            valid_combos.append(simplify(subst_expr))

    return valid_combos


def inductive_synthesis(
    orig_expr: BitVecRef,
    inputs: List[BitVecRef],
    constants: Dict[BitVecRef, int],
    target: BitVecVal,
    depth: int = 3,
):
    if depth == 1:
        return enumerative_synthesis(orig_expr, inputs, constants, target)

    results = []
    for c, val in constants.items():
        if val == target:
            results.append(c)
            continue

        for op in operators:
            # TODO: prune no-ops
            x = solve_eq(op, val, target)
            if x == None:
                continue
            for expr in inductive_synthesis(orig_expr, inputs, constants, x, depth - 1):
                expr = expr if expr in constants else f"({expr})"
                results.append(f"{c} {op} {expr}")

    return results


def synthesize(
    expr: BitVecRef,
    inputs: List[BitVecRef],
    constants: Dict[BitVecRef, BitVecVal],
    target: BitVecVal,
):
    print(
        f"Constants: {constants}, Target: {target}, Results: {inductive_synthesis(expr, inputs, constants, target)}"
    )


if __name__ == "__main__":
    x, y, c1, c2, c3 = BitVecs("x y c1 c2 c3", 4)

    synthesize(
        expr=(x + c1) - (y + c2),
        inputs=[x, y],
        constants={c1: BitVecVal(1, 4), c2: BitVecVal(5, 4)},
        target=BitVecVal(4, 4),
    )

    synthesize(
        expr=(x + c1) + (y + c2), inputs=[x, y], constants={c1: 10, c2: 14}, target=24
    )

    synthesize(
        expr=(x * c1) - (x * y - c2) + (y + c3),
        inputs=[x, y],
        constants={c1: 1, c2: 5, c3: 10},
        target=6,
    )
