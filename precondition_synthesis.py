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
    max_conjuctions: int = 2,
):
    sym_vars = [
        BitVec(f"symb_{i}", bitwidth) for i in range(1, len(positive_example) + 1)
    ]
    expression_sketches = generate_expressions(sym_vars, bitwidth, 0)

    values = list(positive_example.keys()) + [
        BitVecVal(0, bitwidth),
        BitVecVal(1, bitwidth),
    ]
    combinations = [
        combo
        for combo in list(itertools.product(values, repeat=len(positive_example)))
        if len(set(combo)) > 1
        and set(combo) != {BitVecVal(0, bitwidth), BitVecVal(1, bitwidth)}
    ]

    # print(f"expression sketches: {expression_sketches}")
    # print(f"combinations: {combinations}")

    precondition_candidates = []
    # Is power of 2:
    for const, val in positive_example.items():
        power_of_2_solver = Solver()
        power_of_2_solver.add(val & (val - 1) == 0)

        if power_of_2_solver.check().r == Z3_L_TRUE:
            precondition_candidates.append(const & (const - 1) == 0)

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

            if lte_solver.check().r == Z3_L_TRUE:
                precondition_candidates.append(subst_sketch <= 0)

            if gte_solver.check().r == Z3_L_TRUE:
                precondition_candidates.append(subst_sketch >= 0)

            if eq_solver.check().r == Z3_L_TRUE:
                precondition_candidates.append(subst_sketch == 0)

            if gt_solver.check().r == Z3_L_TRUE:
                precondition_candidates.append(subst_sketch > 0)

            if lt_solver.check().r == Z3_L_TRUE:
                precondition_candidates.append(subst_sketch < 0)

    valid_candidates = []
    for i in range(1, max_conjuctions + 1):
        candidates = precondition_candidates
        # print(f"Attempt {i} at finding candidates")
        if i > 1:
            conjuctions = [
                combo
                for combo in list(itertools.product(candidates, repeat=i))
                if len(set(combo)) > 1
            ]
            candidates = [And(*combo) for combo in conjuctions]

        for candidate in candidates:
            verifier = Solver()

            verifier.add(And(candidate, Not(expr)))

            print(candidate)
            if verifier.check().r == Z3_L_FALSE:
                valid_candidates.append(candidate)
                continue

            # print(verifier.model())
        if valid_candidates:
            break

    return valid_candidates


def get_negative_examples(expr: BitVecRef, consts: List[BitVecRef], num: int = 3):
    s = Solver()
    s.add(Not(expr))

    results: List[Dict[BitVecRef, BitVecVal]] = []
    for _ in range(num):
        if s.check().r == Z3_L_FALSE:
            break  # Means that there are no constants for which the expression is not satisfied

        model = s.model()
        negative_example = {c: model[c] for c in consts}
        results.append(negative_example)

        for c, val in negative_example.items():
            s.add(c != val)

    return results


if __name__ == "__main__":
    bitwidth = 8
    x, y, c1, c2, c3 = BitVecs("x y c1 c2 c3", bitwidth)

    expr = LShR(x << c1, c2) << c3 == x & LShR(-1 << c1, c2) << c3
    negative_examples = get_negative_examples(expr=expr, consts=[c1, c2, c3], num=3)
    print(f"negative examples: {negative_examples}")
    print(
        precondition_synthesis(
            expr,
            positive_example={
                c1: BitVecVal(8, bitwidth),
                c2: BitVecVal(16, bitwidth),
                c3: BitVecVal(8, bitwidth),
            },
            negative_examples=negative_examples,
            bitwidth=bitwidth,
        )
    )

    # This fails to generate: IsPowerOf2(𝐶1 ) ∧ (𝐶1 − 𝐶2 ) = 1;
    expr = (c2 != (c2 & x)) & ULT(x, c1) == ULT(x, c2)
    negative_examples = get_negative_examples(expr=expr, consts=[c1, c2], num=3)
    print(f"negative examples: {negative_examples}")
    print(
        precondition_synthesis(
            expr,
            positive_example={c1: BitVecVal(16, bitwidth), c2: BitVecVal(15, bitwidth)},
            negative_examples=negative_examples,
            bitwidth=bitwidth,
        )
    )

    # This should have no negative examples, meaning it doesn't require preconditions
    expr = (x + c1) - (y + c2) == x - y + (c1 - c2)
    assert get_negative_examples(expr=expr, consts=[c1, c2], num=3) == []
