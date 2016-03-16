from gp.chromosome import Chromosome

class Gene:
    def __init__(self, tactics):
        self.chromosome = Chromosome(tactics)
        self.fitness = 0

    def updateFitness(self, fitness):
        self.fitness = fitness
