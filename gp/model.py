class GP:
    def __init__(self, args, population=None, maxGeneration=None,
            mutateRate=None, eliteRate=None, crossRate=None,
            crossType=None, verifyNum=None, proof):
        self.population = population or args.population
        self.maxGeneration = maxGeneration or args.maxGeneration
        self.mutateRate = mutateRate or args.mutateRate
        self.eliteRate = eliteRate or args.eliteRate
        self.crossRate = crossRate or args.crossRate
        self.crossType = crossType or args.crossType
        self.verifyNum = verifyNum or args.verifyNum
        self.proof = proof

