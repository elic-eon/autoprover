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
            tactic = tactics.randomSelect()
            if len(chromosome) == 0:
                chromosome.append(tactic)
            else:
                while (tactics.isUnrepeatable(tactic) and 
                        tactic == chromosome[-1] ):
                    tactic = tactics.randomSelect()
                chromosome.append(tactic)
        return chromosome

    def length(self):
        return len(self.chromosome)

