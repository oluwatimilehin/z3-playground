import logging

from z3 import *

logger = logging.getLogger(__name__)
log_handler = logging.StreamHandler(sys.stdout)
log_handler.setFormatter(logging.Formatter("%(filename)20s: %(message)s"))
logging_level = logging.INFO
log_handler.setLevel(logging_level)
logger.addHandler(log_handler)
logger.setLevel(logging_level)


def exists_for_all(expr, exists, for_all):
    e_solver = Solver()
    e_solver.add(expr)

    while True:
        if e_solver.check().r != Z3_L_TRUE:
            logger.error(f"Could not satisfy exists formula for {expr}")
            break

        e_model = e_solver.model()

        e_vals = {c: e_model[c] for c in exists}
        substitute_list = [(c, val) for c, val in e_vals.items()]
        subst_expr = substitute(expr, *substitute_list)

        f_solver = Solver()
        f_solver.add(Not(subst_expr))

        if f_solver.check().r == Z3_L_FALSE:
            return e_vals

        f_model = f_solver.model()
        counter_examples = [(f, f_model[f]) for f in for_all]

        e_solver.add(substitute(expr, *counter_examples))


def left_shift_right_shift():
    x, c1, c2, c3, c4 = BitVecs("x c1 c2 c3 c4", 4)

    expr = ((x << c1) >> c2) << c3 == x & c4
    return exists_for_all(expr, [c1, c2, c3, c4], [x])


def add_const():
    x, cst = Ints("x cst")
    expr = x + cst == x

    return exists_for_all(expr, [cst], [x])


if __name__ == "__main__":
    print(left_shift_right_shift())
    print(add_const())
