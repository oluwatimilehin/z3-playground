from typing import List

from z3 import *

operators = ["+", "-"]


def solve_eq(op: str, val: int, target: int):
    x = Int("x")
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


def enumerative_synthesis(inputs: List[int], target: int):
    pass


def inductive_synthesis(inputs: List[int], target: int, depth: int):
    if depth == 1:
        return []  # TODO: implement enumerative synthesis

    results = []
    for i, val in enumerate(inputs):
        if val == target:
            results.append(i)
            continue

        for op in operators:
            # TODO: prune no-ops

            x = solve_eq(op, val, target)
            if x == None:
                continue
            for expr in inductive_synthesis(inputs, x, depth - 1):
                expr = expr if isinstance(expr, int) else f"({expr})"
                results.append(f"{i} {op} {expr}")

    return results


if __name__ == "__main__":
    print(inductive_synthesis([10, 14], 24, 4))
    print(inductive_synthesis([1, 5], 4, 4))
    print(inductive_synthesis([1, 10, 5], 6, 4))
