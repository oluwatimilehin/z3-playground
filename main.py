from z3 import *

import logging

logger = logging.getLogger(__name__)
log_handler = logging.StreamHandler(sys.stdout)
log_handler.setFormatter(logging.Formatter("%(filename)20s: %(message)s"))
logging_level = logging.INFO
log_handler.setLevel(logging_level)
logger.addHandler(log_handler)
logger.setLevel(logging_level)

if __name__ == "__main__":
    bit_width = 4
    x, c1, c2, c3, c4 = BitVecs("x c1 c2 c3 c4", bit_width)

    constraints = []
    exists_solver = Solver()

    expr = ((x << c1) >> c2) << c3 == x & c4
    exists_solver.add(expr)

    while True:
        # for i in range(bit_width):
        #     # Prevent left shifts
        #     exists_solver.add(Implies(Extract(i, i, x) == 1, c1 < bit_width - i))
        #     exists_solver.add(Implies(Extract(i, i, x) == 1, c3 < bit_width - i))

        print(f"Exists solver result: {exists_solver.check()}")
        if exists_solver.check().r != Z3_L_TRUE:
            logger.error("Could not satisfy exists formula")
            break

        exists_m = exists_solver.model()
        print(
            f"c1={exists_m[c1]}, c2={exists_m[c2]}, c3={exists_m[c3]}, c4={exists_m[c4]}, x={exists_m[x]}"
        )

        for_all_solver = Solver()
        subst_exists_expr = substitute(
            expr,
            (c1, exists_m[c1]),
            (c2, exists_m[c2]),
            (c3, exists_m[c3]),
            (c4, exists_m[c4]),
        )
        for_all_solver.add(Not(subst_exists_expr))

        print(f"Forall solver results: {for_all_solver.check()}")
        if for_all_solver.check().r != Z3_L_TRUE:
            logger.info("Constants hold for all x")
            break

        for_all_m = for_all_solver.model()

        print(f"x={for_all_m[x]}")
        print(f"Forall solver result: {for_all_solver.check()}")

        subst_forall_expr = substitute(expr, (x, for_all_m[x]))
        exists_solver.add(subst_forall_expr)
