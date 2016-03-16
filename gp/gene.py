from gp.chromosome import Chromosome

class Gene:
    def __init__(self):
        self.chromosome = Chromosome()
        self.fitness = 0

    def updateFitness(self, fitness):
        self.fitness = fitness
