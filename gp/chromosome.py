from random import random, randint

class Chromosome:
    def __init__(self, tactics):
        self.chromosome = []
        chromosomeLength = randint(4, 15)
        print(chromosomeLength)
        for fragNum in range(chromosomeLength):
            tactic = tactics[randint(0, len(tactics)-1)]
            if len(self.chromosome) == 0:
                self.chromosome.append(tactic)
            else:
                while tactic[1] is False and (tactic == self.chromosome[-1]):
                    tactic = tactics[randint(0, len(tactics)-1)]
                self.chromosome.append(tactic)

    def showChromosome(self):
        print(self.chromosome)
