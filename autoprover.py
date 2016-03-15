#!/usr/bin/env python3

import eval, gp, utils
from proof import Proof
from utils import parser
from gp.model import GP

if __name__ == "__main__":
    args = parser.getArgs()
    proof = Proof(args.file)
    gpModel = GP(args, proof)
    GP.start()

    if GP.isProoved():
        pass
    else:
        pass

