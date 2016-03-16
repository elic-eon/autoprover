#!/usr/bin/env python3

import eval, gp, utils
from proof import Proof
from utils import parser
from gp.model import GPModel

if __name__ == "__main__":
    args = parser.getArgs()
    proof = Proof(args.file)
    gpModel = GPModel(args=args, proof=proof)
    # gpModel.showProp()
    gpModel.start()

    if gpModel.isProved():
        pass
    else:
        pass

