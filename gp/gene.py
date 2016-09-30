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
        tactic = tactics.random_select()
        if len(chromosome) == 0:
            chromosome.append(tactic)
        else:
            while (tactics.is_unrepeatable(tactic) and
                   tactic == chromosome[-1]):
                tactic = tactics.random_select()
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
        self.length_of_states = 0
        self.lastest_state = None
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
        coq_states = evaluation.get_coq_states(run_output, proof,
                                               self.chromosome)
        self.lastest_state = coq_states[-1]
        # print(self.chromosome[0:3])
        # print(coq_states[-1].data)
        self._is_proof = coq_states[-1].is_proof
        self.length_of_states = len(coq_states)
        # self.fitness = len(coq_states)-2
        self.fitness = evaluation.calculate_fitness(coq_states,
                                                    self.chromosome,
                                                    proof.tactics)
        return

    def modification(self):
        """Modify one tactic of gene
        """
        if self.is_proof():
            return
        print("Human involve")
        print(len(self.chromosome), end="\t")
        print(self.length_of_states, end="\t")
        print(self.fitness)
        print(self.chromosome)
        print(self.lastest_state.hypothesis)
        print("======================")
        print(self.lastest_state.goal)
        input_tactic = input("Enter tactic: ")
        if len(self.chromosome) == self.length_of_states-2:
            self.chromosome.append(input_tactic)
        else:
            self.chromosome[self.length_of_states-2] = input_tactic
        print(self.chromosome)

    def goal(self):
        """return goal of gene
        """
        return self.lastest_state.goal()

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
