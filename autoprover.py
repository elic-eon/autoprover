#!/usr/bin/env python3

import eval, gp, utils
from proof import Proof
from proof import bruteForceSearch
from utils import parser
from utils.tactic import TacticsSet
from gp.model import GPModel

if __name__ == "__main__":
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

