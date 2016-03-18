from eval import eval
class Proof:
    def __init__(self, inputFile):
        self.theorem = self.readThmFromFile(inputFile)

    def readThmFromFile(self, inputFile):
        retList = []
        for line in inputFile:
            retList.append(line.strip())
        return retList

    def calculateFitness(self, chromosome):
        script = eval.preprocess(self.theorem, chromosome)
        result = eval.runCoqtop(script)
        return eval.evaluateResult(result)

