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
    expr, inputs: List[BitVecRef], constants: Dict[BitVecRef, int], target: int
):
    zero = IntVal(0)
    one = IntVal(1)
    minus_one = IntVal(-1)

    special_vals = [zero, one, minus_one]
    input_combinations = list(itertools.product(special_vals, repeat=len(inputs)))

    # print(input_combinations)

    consts_permutation = list(itertools.permutations(constants.keys()))
    inputs_x_consts = list(itertools.product(input_combinations, consts_permutation))

    # print(consts_permutation)
    # print(inputs_x_consts)

    valid_combos = []

    for combo in inputs_x_consts:
        s = Solver()
        for i, input in enumerate(inputs):
            s.add(input == Int2BV(combo[0][i], 4))

        for i, const in enumerate(constants.keys()):
            s.add(const == constants[combo[1][i]])

        s.add(expr == target)

        if s.check().r == Z3_L_TRUE:
            # print(f"found valid combo: {combo}")
            inputs_subst = [
                (input, Int2BV(combo[0][i], 4)) for i, input in enumerate(inputs)
            ]
            consts_subst = [
                (const, combo[1][i]) for i, const in enumerate(constants.keys())
            ]

            comb = inputs_subst + consts_subst
            valid_combos.append(simplify(substitute(expr, *comb)))

    # print(
    #     f"expr: {expr}, expr type: {type(expr)}; target: {target}; target_type: {type(target)}"
    # )
    # print(f"combos: {valid_combos}")
    return valid_combos


def inductive_synthesis(
    orig_expr: BitVecRef,
    inputs: List[BitVecRef],
    constants: Dict[BitVecRef, int],
    target: int,
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
    constants: Dict[BitVecRef, int],
    target: int,
):
    print(
        f"Constants: {constants}, Target: {target}, Results: {inductive_synthesis(expr, inputs, constants, target)}"
    )


if __name__ == "__main__":
    x, y, c1, c2, c3 = BitVecs(
        "x y c1 c2 c3", 4
    )  # TODO: need to figure out how to get this to work for narrower width; seeing issues with wrapping and stuff;

    synthesize(
        expr=(x + c1) - (y + c2),
        inputs=[x, y],
        constants={c1: 1, c2: 5},
        target=4,
    )

    # synthesize(
    #     expr=(x + c1) + (y + c2), inputs=[x, y], constants={c1: 10, c2: 14}, target=24
    # )

    # synthesize(
    #     expr=(x * c1) - (x * y - c2) + (y + c3),
    #     inputs=[x, y],
    #     constants={c1: 1, c2: 5, c3: 10},
    #     target=6,
    # )
