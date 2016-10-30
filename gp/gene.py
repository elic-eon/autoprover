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

        self.fitness = evaluation.calculate_fitness(
            self.coq_states[proof.offset:])
        n_error = len(self.chromosome) - len(self.coq_states)
        self.fitness += 1 - (n_error / len(self.chromosome)) ** 2
        # print(self.fitness)
        # for state in self.coq_states:
            # print(state)
        return

    def print_lastest(self):
        """print out gene
        """
        print("c_len\ts_len\tfitness")
        print(len(self.chromosome), end="\t")
        print(self.length_of_states-1, end="\t")
        print(self.fitness)
        print('\n'.join(self.valid_tactics))
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
        self.chromosome.append(input_tactic)
        # print(self.chromosome)

    @property
    def valid_tactics(self):
        """valid tactics from self.coq_states
        Returns:
            list: valid tactics
        """
        if self.coq_states:
            return [e.tactic for e in self.coq_states]
        else:
            return self.chromosome

    @property
    def goal(self):
        """return goal of gene
        """
        return self.coq_states[-1].goal

    def update_fitness(self, fitness):
        """
        replace fitness by arg
        """
        self.fitness = fitness

    def format_output(self, proof):
        """Prepare a formated gene output
        """
        format_string = ""
        format_string += "\n".join(proof.theorem_body)
        format_string += "\nProof.\n"
        format_string += "\n".join(["  "+e for e in self.valid_tactics[1:]])
        format_string += "\n"
        return format_string

    def print_progress(self):
        """Print all state of gene
        """
        for state in self.coq_states:
            print(state)
