from eval import eval
class Proof:
    def __init__(self, inputFile):
        self.theorem = self.readThmFromFile(inputFile)
        self.theoremName = self.getThmNameFromList(self.theorem)

    def readThmFromFile(self, inputFile):
        retList = []
        for line in inputFile:
            retList.append(line.strip())
        return retList

    def getThmNameFromList(self, tList):
        for line in tList:
            if (line.startswith("Theorem")):
                return line.split()[1]

    def calculateFitness(self, chromosome):
        script = eval.preprocess(self.theorem, chromosome)
        result = eval.runCoqtop(script)
        return eval.evaluateResult(result, self.theoremName)

