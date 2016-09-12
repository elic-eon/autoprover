#!/usr/bin/env python3

# bench 1000 population: 42.31s user 13.83s system 98% cpu 56.944 total
from proof import Proof
from proof import bruteForceSearch
from utils import parser
from utils.tactic import TacticsSet
from utils.log import regLogger
from gp.model import GPModel


if __name__ == "__main__":
    regLogger()
    args = parser.getArgs()
    proof = Proof(args.file)
    tactics = TacticsSet(args.tacticBase)

    if args.bruteForce:
        bruteForceSearch(proof=proof, tactics=tactics)
    else:
        gpModel = GPModel(args=args, proof=proof, tactics=tactics)
        # gpModel.showProp()
        gpModel.start()

        if gpModel.isProved():
            pass
        else:
            pass
