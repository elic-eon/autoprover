from eval import eval
import logging
class Proof:
    def __init__(self, inputFile):
        self.theorem = self.readThmFromFile(inputFile)
        self.theoremName = self.getThmName()
        logging.info("Theorem Name: %s", self.theoremName)

    def readThmFromFile(self, inputFile):
        retList = []
        for line in inputFile:
            retList.append(line.strip())
        return retList

    def getThmName(self):
        for line in self.theorem:
            if (line.startswith("Theorem")):
                return line.split()[1]
            if (line.startswith("Lemma")):
                return line.split()[1]

    def calculateFitness(self, chromosome):
        script = eval.preprocess(self.theorem, chromosome)
        result = eval.runCoqtop(script)
        return eval.evaluateResult(result, self.theoremName)

def bruteForceSearch(proof, tactics):
    pool = [([x],1) for x in tactics]

    poolBuf = []
    for (tacticList, steps) in pool:
        script = eval.preprocess(proof.theorem, tacticList)
        result = eval.runCoqtop(script)
        s = eval.evaluateResult(result, proof.theoremName)
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
            script = eval.preprocess(proof.theorem, tacticList)
            result = eval.runCoqtop(script)
            s = eval.evaluateResult(result, proof.theoremName)
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

