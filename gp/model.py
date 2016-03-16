class GP:
    def __init__(self, args, population=None, maxGeneration=None,
            mutate_rate=None, eliteRate=None, cross_rate=None,
            cross_version=None, verify_num=None, proof):
        self.population = population or args.population
        self.maxGeneration = maxGeneration or args.maxGeneration
        self.mutate_rate = mutate_rate or args.mutate_rate
        self.eliteRate = eliteRate or args.eliteRate
        self.cross_rate = cross_rate or args.cross_rate
        self.cross_version = cross_version or args.cross_version
        self.verify_num = verify_num or args.verify_num
        self.proof = proof

