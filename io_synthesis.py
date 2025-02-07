from typing import List, Dict
import itertools

from z3 import *

operators = ["+", "-"]


def solve_eq(op: str, val: int, target: int, bitwidth: int):
    x = BitVec("x", bitwidth)
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
    expr,
    inputs: List[BitVecRef],
    constants: Dict[BitVecRef, BitVecVal],
    target: BitVecVal,
    bitwidth: int,
):
    zero = BitVecVal(0, bitwidth)
    one = BitVecVal(1, bitwidth)
    minus_one = BitVecVal(-1, bitwidth)
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
    constants: Dict[BitVecRef, BitVecVal],
    target: BitVecVal,
    bitwidth: int,
    depth: int = 3,
):
    if depth == 1:
        return enumerative_synthesis(orig_expr, inputs, constants, target, bitwidth)

    results = []
    for c, val in constants.items():
        if val == target:
            results.append(c)
            continue

        for op in operators:
            # TODO: prune no-ops
            x = solve_eq(op, val, target, bitwidth)
            if x == None:
                continue
            for expr in inductive_synthesis(
                orig_expr, inputs, constants, x, bitwidth, depth - 1
            ):
                expr = expr if expr in constants else f"({expr})"
                results.append(f"{c} {op} {expr}")

    return results


def synthesize(
    expr: BitVecRef,
    inputs: List[BitVecRef],
    constants: Dict[BitVecRef, BitVecVal],
    target: BitVecVal,
    bitwidth: int,
):
    print(
        f"Constants: {constants}, Target: {target}, Results: {inductive_synthesis(expr, inputs, constants, target, bitwidth)}"
    )


if __name__ == "__main__":
    bitwidth = 4
    x, y, c1, c2, c3 = BitVecs("x y c1 c2 c3", bitwidth)
    synthesize(
        expr=(x + c1) - (y + c2),
        inputs=[x, y],
        constants={c1: BitVecVal(1, bitwidth), c2: BitVecVal(5, bitwidth)},
        bitwidth=bitwidth,
        target=BitVecVal(4, bitwidth),
    )

    bitwidth = 8
    x, y, c1, c2, c3 = BitVecs("x y c1 c2 c3", bitwidth)
    synthesize(
        expr=(x + c1) + (y + c2),
        inputs=[x, y],
        constants={c1: BitVecVal(10, 8), c2: BitVecVal(14, 8)},
        bitwidth=bitwidth,
        target=BitVecVal(24, 8),
    )

    synthesize(
        expr=(x * c1) - (x * y - c2) + (y + c3),
        inputs=[x, y],
        constants={
            c1: BitVecVal(1, bitwidth),
            c2: BitVecVal(5, bitwidth),
            c3: BitVecVal(10, bitwidth),
        },
        bitwidth=bitwidth,
        target=BitVecVal(6, bitwidth),
    )
