#!/usr/bin/env python3

import eval, gp, utils
from proof import Proof
from utils import parser
from utils.tactic import tacticReader
from gp.model import GPModel

if __name__ == "__main__":
    args = parser.getArgs()
    proof = Proof(args.file)
    tactics = tacticReader(args.tacticBase)
    gpModel = GPModel(args=args, proof=proof, tactics=tactics)
    # gpModel.showProp()
    gpModel.start()

    if gpModel.isProved():
        pass
    else:
        pass

