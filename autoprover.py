#!/usr/bin/env python3

# bench 1000 population: 42.31s user 13.83s system 98% cpu 56.944 total
from proof import Proof
from proof import brute_force_search
from utils import parser
from utils.tactic import TacticsSet
from utils.log import reg_logger
from gp.model import GPModel


if __name__ == "__main__":
    reg_logger()
    args = parser.get_args()
    tactics = TacticsSet(args.tacticBase)
    proof = Proof(input_file=args.file, tactics=tactics)

    if args.bruteForce:
        brute_force_search(proof=proof, tactics=tactics)
    else:
        gp_model = GPModel(args=args, proof=proof, tactics=tactics)
        # gpModel.showProp()
        gp_model.start(gen=10)
        for _ in range(9):
            gp_model.edit()
            gp_model.start(gen=10)

        if gp_model.is_proved():
            for gene in gp_model.proofs:
                print(gene.chromosome)
        else:
            pass
