"""
define class Gene
"""
# from random import randint
from evaluation import evaluation
# import logging

def random_chromosome(tactics):
    """generate a random chromosome with length of 15.

    Args:
        tactics (Tactic): a Tactic class instance.

    Returns:
        list: chromosome, a list of string(tactic).
    """
    chromosome = []
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

    Args:
        tactics (Tactic): a Tactic class instance.
        chromosome (list): can provide a chromosome.
    """
    def __init__(self, tactics=None, chromosome=None):
        if chromosome is not None:
            self.chromosome = chromosome
        else:
            self.chromosome = random_chromosome(tactics)
        self.fitness = 0
        self.coq_states = None

    def __len__(self):
        return len(self.chromosome)

    @property
    def is_proof(self):
        """True if this gene is a Proof

        Returns:
            bool: is_proof
        """
        if self.coq_states:
            return self.coq_states[-1].is_proof
        else:
            return False

    @property
    def length_of_states(self):
        """A property of length_of_states
        Returns:
            int: length of self.coq_states
        """
        return len(self.coq_states)

    def update_fitness_for_proof(self, proof):
        """re-evaluate fitness for a proof
        Args:
            proof (Proof): a Proof instance.
        """
        # TODO extract these two func into coqapi
        coq_script = evaluation.preprocess(proof.theorem, self.chromosome)
        run_output = evaluation.run_coqtop(coq_script)
        self.coq_states = evaluation.get_coq_states(run_output, proof,
                                                    self.chromosome)

        if self.is_proof:
            return

        self.fitness = evaluation.calculate_fitness(self.coq_states)
        print(self.fitness)
        for state in self.coq_states:
            print(state)
        return

    def print_lastest(self):
        """print out gene
        """
        print("c_len\ts_len\tfitness")
        print(len(self.chromosome), end="\t")
        print(self.length_of_states-1, end="\t")
        print(self.fitness)
        print(self.valid_tactics())
        print(self.coq_states[-1])
        return

    def modification(self):
        """Modify one tactic of gene
        """
        if self.is_proof:
            return
        print("Human involve")
        self.print_lastest()
        try:
            input_tactic = input("Enter tactic: ")
        except EOFError:
            return
        if len(self.chromosome) == self.length_of_states-2:
            self.chromosome.append(input_tactic)
        else:
            self.chromosome[self.length_of_states-2] = input_tactic
        print(self.chromosome)

    def valid_tactics(self):
        """valid tactics from self.coq_states
        Returns:
            string: valid tactics
        """
        return '\n'.join(e.tactic for e in self.coq_states)

    def goal(self):
        """return goal of gene
        """
        return self.coq_states[-1].goal()

    def update_fitness(self, fitness):
        """
        replace fitness by arg
        """
        self.fitness = fitness
