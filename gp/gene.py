from random import random, randint

class Gene:
    def __init__(self, tactics=None, chromosome=None):
        if chromosome is not None:
            self.chromosome = chromosome
        else:
            self.chromosome = self.randomChromosome(tactics)
        self.fitness = 0

    def updateFitness(self, fitness):
        self.fitness = fitness

    def randomChromosome(self, tactics):
        chromosome = []
        chromosomeLength = randint(4, 15)
        for fragNum in range(15):
            tactic = tactics[randint(0, len(tactics)-1)]
            if len(chromosome) == 0:
                chromosome.append(tactic)
            else:
                while tactic[1] is False and (tactic == chromosome[-1]):
                    tactic = tactics[randint(0, len(tactics)-1)]
                chromosome.append(tactic)
        return chromosome

    def length(self):
        return len(self.chromosome)

