from random import random, randint
from eval import eval
import logging

class Gene:
    def __init__(self, tactics=None, chromosome=None):
        if chromosome is not None:
            self.chromosome = chromosome
        else:
            self.chromosome = self.randomChromosome(tactics)
        self.fitness = 0
        self.goal = None
        self._isProof = False

    def __len__(self):
        return len(self.chromosome)

    def updateFitnessForAProof(self, proof):
        # TODO extract these two func into coqapi
        coqScript = eval.preprocess(proof.theorem, self.chromosome)
        runOutput = eval.runCoqtop(coqScript)
        
        coqStates = eval.getCoqStates(runOutput, proof.theoremName)
        self.goal = coqStates[-1].getGoal()
        self._isProof = coqStates[-1].isProof()
        self.fitness = len(coqStates)
    
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

    def isProof(self):
        return self._isProof


