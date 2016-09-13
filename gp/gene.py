"""
define class Gene
"""
# from random import randint
from evaluation import evaluation
# import logging

def random_chromosome(tactics):
    """
    generate a random chromosome
    """
    chromosome = []
    # chromosome_length = randint(4, 15)
    for _ in range(15):
        tactic = tactics.randomSelect()
        if len(chromosome) == 0:
            chromosome.append(tactic)
        else:
            while (tactics.isUnrepeatable(tactic) and
                   tactic == chromosome[-1]):
                tactic = tactics.randomSelect()
            chromosome.append(tactic)
    return chromosome

class Gene:
    """
    gene for gp
    """
    def __init__(self, tactics=None, chromosome=None):
        if chromosome is not None:
            self.chromosome = chromosome
        else:
            self.chromosome = random_chromosome(tactics)
        self.fitness = 0
        self.goal = None
        self._is_proof = False

    def __len__(self):
        return len(self.chromosome)

    def update_fitness_for_proof(self, proof):
        """
        re-evaluate fitness for a proof
        """
        # TODO extract these two func into coqapi
        coq_script = evaluation.preprocess(proof.theorem, self.chromosome)
        run_output = evaluation.run_coqtop(coq_script)
        coq_states = evaluation.get_coq_states(run_output, proof.theoremName)
        self.goal = coq_states[-1].getGoal()
        print(self.chromosome[0:3])
        print(coq_states[-1].data)
        self._is_proof = coq_states[-1].isProof()
        self.fitness = len(coq_states)
        return

    def update_fitness(self, fitness):
        """
        replace fitness by arg
        """
        self.fitness = fitness


    def is_proof(self):
        """
        return if it is a proved gene
        """
        return self._is_proof
