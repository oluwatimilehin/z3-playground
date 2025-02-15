from typing import List, Dict
import itertools

from z3 import *


def generate_sketches(num_constants: int):
    pass


def get_single_operand_preconditions(
    positive_example: Dict[BitVecRef, BitVecVal],
    negative_examples: List[Dict[BitVecRef, BitVecVal]],
):
    valid_preconditions = []

    for const, positive_val in positive_example.items():
        eq_solver = Solver()
        eq_solver.add(positive_val == 0)

        gt_solver = Solver()
        gt_solver.add(positive_val > 0)

        gte_solver = Solver()
        gte_solver.add(positive_val >= 0)

        lt_solver = Solver()
        lt_solver.add(positive_val < 0)

        lte_solver = Solver()
        lte_solver.add(positive_val <= 0)

        for negative_example_dict in negative_examples:
            negative_example = negative_example_dict[const]
            eq_solver.add(negative_example != 0)

            gt_solver.add(negative_example <= 0)
            gte_solver.add(negative_example < 0)

            lt_solver.add(negative_example >= 0)
            lte_solver.add(negative_example > 0)

        is_lte = lte_solver.check().r == Z3_L_TRUE
        is_gte = gte_solver.check().r == Z3_L_TRUE

        # Prioritize weaker preconditions
        if is_lte or is_gte:
            if is_lte:
                valid_preconditions.append(const <= 0)

            if is_gte:
                valid_preconditions.append(const >= 0)

            continue

        if eq_solver.check().r == Z3_L_TRUE:
            valid_preconditions.append(const == 0)

        if gt_solver.check().r == Z3_L_TRUE:
            valid_preconditions.append(const > 0)

        if lt_solver.check().r == Z3_L_TRUE:
            valid_preconditions.append(const < 0)

    return valid_preconditions


def generate_expressions(sym_vars: List[BitVecRef], bitwidth: int, current: int):
    if current == len(sym_vars):
        return []

    sym_var = sym_vars[current]
    results = []

    ops = {
        "+": lambda a, b: a + b,
        "-": lambda a, b: a - b,
        # "*": lambda a, b: a * b, multiplication needs extra handling so we can get something like (c1 * c2) + c3 and c1 * (c2 + c3)
    }

    for _, func in ops.items():
        for expr in generate_expressions(sym_vars, bitwidth, current + 1):
            results.append(func(sym_var, expr))

    if not results:
        results.append(sym_var)

    return results


def precondition_synthesis(
    expr: BitVecRef,
    positive_example: Dict[BitVecRef, BitVecVal],
    negative_examples: List[Dict[BitVecRef, BitVecVal]],
    bitwidth: int,
):
    sym_vars = [
        BitVec(f"symb_{i}", bitwidth) for i in range(1, len(positive_example) + 1)
    ]
    expression_sketches = generate_expressions(sym_vars, bitwidth, 0)

    values = list(positive_example.keys()) + [BitVecVal(0, 8), BitVecVal(1, 8)]
    combinations = [
        combo
        for combo in list(itertools.product(values, repeat=len(positive_example)))
        if len(set(combo)) > 1 and set(combo) != {BitVecVal(0, 8), BitVecVal(1, 8)}
    ]

    print(f"expression sketches: {expression_sketches}")
    print(f"combinations: {combinations}")

    precondition_candidates = []
    # Is power of 2:
    for subst_sketch, val in positive_example.items():
        power_of_2_solver = Solver()
        power_of_2_solver.add(val & (val - 1) == 0)

        if power_of_2_solver.check().r == Z3_L_TRUE:
            precondition_candidates.append(subst_sketch & (subst_sketch - 1) == 0)

    # TODO: If we have no valid candidates with a single expression, consider joining candidates up to a limit
    for sketch in expression_sketches:
        for combo in combinations:
            substitutions = [(sym_var, combo[i]) for i, sym_var in enumerate(sym_vars)]
            subst_sketch = substitute(sketch, *substitutions)
            positive_subs = [(c, val) for c, val in positive_example.items()]

            positive_expr = substitute(subst_sketch, *positive_subs)
            eq_solver = Solver()
            eq_solver.add(positive_expr == 0)

            gt_solver = Solver()
            gt_solver.add(positive_expr > 0)

            gte_solver = Solver()
            gte_solver.add(positive_expr >= 0)

            lt_solver = Solver()
            lt_solver.add(positive_expr < 0)

            lte_solver = Solver()
            lte_solver.add(positive_expr <= 0)

            for negative_expr in negative_examples:
                negative_subs = [(c, val) for c, val in negative_expr.items()]
                negative_expr = substitute(subst_sketch, *negative_subs)

                eq_solver.add(negative_expr != 0)
                gt_solver.add(negative_expr <= 0)
                gte_solver.add(negative_expr < 0)

                lt_solver.add(negative_expr >= 0)
                lte_solver.add(negative_expr > 0)

            is_lte = lte_solver.check().r == Z3_L_TRUE
            is_gte = gte_solver.check().r == Z3_L_TRUE

            if is_lte or is_gte:
                if is_lte:
                    precondition_candidates.append(subst_sketch <= 0)

                if is_gte:
                    precondition_candidates.append(subst_sketch >= 0)

                continue

            if eq_solver.check().r == Z3_L_TRUE:
                precondition_candidates.append(subst_sketch == 0)

            if gt_solver.check().r == Z3_L_TRUE:
                precondition_candidates.append(subst_sketch > 0)

            if lt_solver.check().r == Z3_L_TRUE:
                precondition_candidates.append(subst_sketch < 0)

    valid_candidates = []
    for candidate in precondition_candidates:
        verifier = Solver()

        verifier.add(And(candidate, Not(expr)))

        print(candidate)
        if verifier.check().r == Z3_L_FALSE:
            valid_candidates.append(candidate)

        print(verifier.model())

    # TODO:
    # - i also need to come up with negative examples
    # now verify the candidates properly; i.e. does the expression always hold true for all values of a and b

    return valid_candidates


if __name__ == "__main__":
    bitwidth = 8
    x, c1, c2 = BitVecs("x c1 c2", bitwidth)

    print(
        precondition_synthesis(
            expr=(x >> c1) * c2 == x * (c2 >> c1),
            positive_example={c1: BitVecVal(1, bitwidth), c2: BitVecVal(8, bitwidth)},
            negative_examples=[],
            bitwidth=bitwidth,
        )
    )
