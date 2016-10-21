"""
define a proof
"""
import logging
from evaluation import evaluation

class Proof:
    """A proof"""
    def __init__(self, input_file, tactics):
        self.theorem = []
        self.read_theorem_from_file(input_file)
        self.theorem_name = self.get_theorem_name()
        self.tactics = tactics
        self.offset = self.get_offset()
        logging.info("Theorem Name: %s", self.theorem_name)

    def read_theorem_from_file(self, input_file):
        """read from file
        """
        for line in input_file:
            self.theorem.append(line.strip())

    def get_theorem_name(self):
        """extract theorem name from theorem
        """
        for line in self.theorem:
            if line.startswith("Theorem"):
                return line.split()[1]
            if line.startswith("Lemma"):
                return line.split()[1]

    @property
    def pre_feed_tactic(self):
        """pre-feed tactic including 'Proof.'
        """
        return self.theorem[len(self.theorem)-self.offset:]

    def get_offset(self):
        """
        get the netber of provided tactics
        """
        for index, line in enumerate(self.theorem):
            if line.startswith("Proof."):
                return len(self.theorem)-index
        self.theorem.append("Proof.")
        return 1

def brute_force_search(proof, tactics):
    pool = [([x]) for x in tactics]

    poolBuf = []
    for (tacticList, steps) in pool:
        script = evaluation.preprocess(proof.theorem, tacticList)
        result = evaluation.run_coqtop(script)
        s = evaluation.evaluate_result(result, proof.theoremName)
        if s[1] > steps:
            poolBuf += [(tacticList, s[1])]
    else:
        pool = [] + poolBuf
        poolBuf = []

    # while (True):
    for i in range(100):
        for (tacticList, steps) in pool:
            poolBuf += [(tacticList+[x], steps) for x in tactics]
        else:
            pool = [] + poolBuf
            poolBuf = []

        for (tacticList, steps) in pool:
            script = evaluation.preprocess(proof.theorem, tacticList)
            result = evaluation.run_coqtop(script)
            s = evaluation.evaluate_result(result, proof.theoremName)
            if s[0] is True:
                print("Found")
                print(tacticList)
                return
            elif s[1] > steps:
                poolBuf += [(tacticList, s[1])]
        else:
            pool = [] + poolBuf
            poolBuf = []

        print(len(pool))
