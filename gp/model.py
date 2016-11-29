"""
define model for gp
"""
# from threading import Thread
# from queue import Queue
from multiprocessing import Pool
from random import random, randint
from math import floor
import operator
from gp.gene import Gene
from gp.rule import GeneRule
from gp.action import GeneAction
from gp.trigger import GeneTrigger

#TODO fox too many instant
class GPModel:
    """
    gp model
    """
    #TODO fix too many args
    def __init__(self, args=None, populationSize=None, maxGeneration=None,
                 mutateRate=None, eliteRate=None, crossRate=None,
                 crossType=None, verifyNum=None, proof=None, tactics=None):
        self.population_size = populationSize or args.populationSize
        self.max_generation = maxGeneration or args.maxGeneration
        self.mutate_rate = mutateRate or args.mutateRate
        self.elite_rate = eliteRate or args.eliteRate
        self.cross_rate = crossRate or args.crossRate
        self.cross_type = crossType or args.crossType
        self.verify_num = verifyNum or args.verifyNum
        self.debug = args.debug
        self.proof = proof
        self.tactics = tactics
        self.population = None
        self.current_generation = 1
        self.proofs = []
        self.rules = []
        self.init_population(self.population_size)
        self.pre_process()

    def show_prop(self):
        """
        display property for model
        """
        print(self.population_size)
        print(self.max_generation)
        print(self.mutate_rate)
        print(self.elite_rate)
        print(self.cross_rate)
        print(self.cross_type)
        print(self.verify_num)
        print(self.proof)

    def init_population(self, size):
        """
        create population by size
        """
        print("Initializing population.")
        self.population = []
        for _ in range(size):
            self.population.append(Gene(self.tactics))

    def pre_process(self):
        """
        run before start
        """
        self.current_generation = 1
        self.update_fitness_for_population()
        self.sort_sopulation()
        self.check_proof()

    def is_proved(self):
        """
        check population has a proof
        """
        return len(self.proofs) > 0

    def start(self, gen=None):
        """
        run the model
        """
        if gen is None:
            # if gen is not set
            local_gen_limit = self.max_generation + 1
        else:
            local_gen_limit = gen

        if self.current_generation > self.max_generation:
            return

        for _ in range(local_gen_limit):
            print("Generation No.{0}".format(self.current_generation))
            if self.debug:
                self.sort_sopulation()
                for index in range(0, 30):
                    self.population[index].print_lastest()
            self.crossover()
            self.update_fitness_for_population()
            self.apply_rules()
            self.next_generation()
            if self.current_generation > self.max_generation:
                break

        # self.printGeneByIndex(0, True)
    def next_generation(self):
        """
        next generation
        """
        print("Avg. fitness\tAvg. length")
        print("{0:.8f}\t{1}".format(self.average_fitness(),
                                    self.average_length_of_gene()))
        self.current_generation += 1
        self.sort_sopulation()
        self.check_proof()

    def check_proof(self):
        """Check if there is a proof in population
        """
        for gene in self.population:
            if gene.is_proof:
                print(gene.chromosome)
                for state in gene.coq_states:
                    print(state)
                self.proofs.append(Gene(chromosome=gene.valid_tactics))

    def update_fitness_for_population(self):
        """
        return individual if theorem is proved, o.w return None
        """
        def wrapper(func, *args, **kwargs):
            """func wrapper"""
            return func, args, kwargs

        with Pool(processes=4) as pool:
            for gene in self.population:
                func, args, kargs = wrapper(gene.update_fitness_for_proof, self.proof)
                pool.apply_async(func(*args, **kargs))

    def apply_rules(self):
        """Perform action by rules"""
        if len(self.rules) == 0:
            return
        for gene in self.population:
            for rule in self.rules:
                if rule.type == "gene":
                    rule.check_and_apply(gene)

    def crossover(self):
        """
        the crossover operation for gp
        """
        self.sort_sopulation()
        elite_amount = round(self.elite_rate * self.population_size)
        # preserve from the top
        new_population = [ele for ele in self.population if ele.ttl > 0]
        for individual in new_population:
            if individual.ttl > 0:
                individual.ttl -= 1
        new_population += self.population[:elite_amount]

        while len(new_population) < self.population_size:
            # newGene = self.crossBelowCrossRate()
            new_gene, new_gene2 = self.cross_on_arb_seq()
            if random() <= self.mutate_rate:
                self.mutate(new_gene)
            new_population.append(new_gene)
            if len(new_population) == self.population_size:
                break

            if random() <= self.mutate_rate:
                self.mutate(new_gene2)
            new_population.append(new_gene2)
        self.population = new_population

    def sort_sopulation(self):
        """
        sort population by length and fitness
        """
        self.population.sort(key=lambda x: x.fitness, reverse=True)

    def cross_below_cross_rate(self):
        """
        select two parent by cross rate, crossover on random point
        """
        p1_index = randint(0, floor(self.population_size * self.cross_rate)-1)
        p2_index = randint(0, floor(self.population_size * self.cross_rate)-1)
        gene_of_p1 = self.population[p1_index]
        gene_of_p2 = self.population[p2_index]
        cross_point = randint(0, int_min(len(gene_of_p1), len(gene_of_p2))-1)
        new_chromosome = []
        new_chromosome += gene_of_p1.chromosome[:cross_point]
        new_chromosome += gene_of_p2.chromosome[cross_point:]
        if (self.tactics.is_unrepeatable(new_chromosome[cross_point])
                and cross_point < len(new_chromosome)-1):
            if new_chromosome[cross_point] == new_chromosome[cross_point+1]:
                del new_chromosome[cross_point]
        return Gene(chromosome=new_chromosome)

    def cross_on_arb_seq(self, slmax=6):
        """
        select two parent by cross_rate, crossover by some seqence
        """
        p1_index = randint(0, floor(self.population_size * self.cross_rate)-1)
        p2_index = randint(0, floor(self.population_size * self.cross_rate)-1)
        gene_of_p1 = self.population[p1_index]
        gene_of_p2 = self.population[p2_index]

        p1_begin = myrandint(0, len(gene_of_p1)-1)
        p1_end = p1_begin + myrandint(1, int_min(slmax, len(gene_of_p1)-p1_begin))
        p2_begin = myrandint(0, len(gene_of_p2)-1)
        p2_end = p2_begin + myrandint(1, int_min(slmax, len(gene_of_p2)-p2_begin))
        new_chromosome = []
        new_chromosome += gene_of_p1.chromosome[:p1_begin]
        new_chromosome += gene_of_p2.chromosome[p2_begin:p2_end]
        new_chromosome += gene_of_p1.chromosome[p1_end:]
        new_chromosome2 = []
        new_chromosome2 += gene_of_p2.chromosome[:p2_begin]
        new_chromosome2 += gene_of_p1.chromosome[p1_begin:p1_end]
        new_chromosome2 += gene_of_p2.chromosome[p2_end:]
        self.remove_repeatable(new_chromosome)
        self.remove_repeatable(new_chromosome2)
        return Gene(chromosome=new_chromosome), Gene(chromosome=new_chromosome2)

    def remove_repeatable(self, chromosome):
        """
        remove repeatable tactic
        """
        tactic_set = set()

        for index, tactic in enumerate(chromosome):
            if self.tactics.is_unrepeatable(tactic):
                if tactic in tactic_set:
                    del chromosome[index]
                else:
                    tactic_set.add(tactic)

    def mutate(self, gene):
        """
        the mutate operation
        """
        if len(gene) == 1:
            gene.chromosome[0] = self.tactics.random_select()
        else:
            gene.chromosome[randint(0, len(gene)-1)] = \
                    self.tactics.random_select()

    def average_fitness(self):
        """Calculate the average fitness for population.

        Returns:
            double: avg. fitness
        """
        return sum([e.fitness for e in self.population]) / len(self.population)

    def average_length_of_gene(self):
        """Calculate the average fitness for population.

        Returns:
            double: avg. fitness
        """
        return sum([len(e) for e in self.population]) / len(self.population)

    def edit(self, index, data=None):
        """Human involved modification of some gene of the population
        """
        if self.current_generation > self.max_generation:
            return
        print("Edit Gene {} now.".format(index))
        gene = self.population[index]
        gene.modification(data=data)
        gene.update_fitness_for_proof(self.proof)
        if gene.is_proof:
            self.proofs.append(Gene(chromosome=gene.valid_tactics))
        return

    def show_proofs(self):
        """Show proofs found
        """
        if self.proofs:
            for gene in self.proofs:
                print(gene.format_output(self.proof))
        else:
            print("There is not proof for now.")

    def list(self, argv):
        """List property of some individual.

        Args:
            argv(list): sub command of list function.
        """
        def get_interval(interval):
            """Get begin and end of interval
            """
            interval_list = interval.split("-")
            if len(interval_list) == 1:
                return (int(interval_list[0]), int(interval_list[0])+1)
            else:
                return (int(interval_list[0]), int(interval_list[1])+1)
        if not argv or not argv[0]:
            return

        (begin, end) = get_interval(argv[0])
        if len(argv) == 1:
            for index, gene in enumerate(self.population[begin:end]):
                print("{0}: {1:.8f}".format(index, gene.fitness))
                gene.print_progress()
        elif argv[1] == "fitness":
            for index, gene in enumerate(self.population[begin:end]):
                print("{0}: {1:.8f}".format(index, gene.fitness))
        elif argv[1] == "chromosome":
            for index, gene in enumerate(self.population[begin:end]):
                print("{0}: {1}".format(index, gene.chromosome))
        elif argv[1] == "ttl":
            for index, gene in enumerate(self.population[begin:end]):
                print("{0}: {1}".format(index, gene.ttl))

    def set_attributes(self, argv):
        """Set attributes of population
        """
        if argv[0] == "population" or argv[0] == "pop":
            if argv[1] == "ttl":
                self.population[int(argv[2])].ttl = int(argv[3])
        elif argv[0] == "rule":
            trigger = GeneTrigger(last_goal="number (S n) d mod 3 = sumdigits (S n) d mod 3")
            cmd = ["edit"]
            data = ["append",
                    "change ((d (S n) + 10 * number n d) mod 3 = (d (S n) + sumdigits n d) mod 3)."]
            act = GeneAction(cmd=cmd, data=data)
            self.rules.append(GeneRule(trigger=trigger, action_list=[act],
                                       proof=self.proof))
        elif argv[0] == "rule2":
            trigger = GeneTrigger(tactic_restriction=("rewrite Zplus_mod.", 2))
            trigger2 = GeneTrigger(tactic_restriction=("rewrite Zmult_mod.", 2))
            cmd = ["penalty"]
            act = GeneAction(cmd=cmd, data="1.2")
            self.rules.append(GeneRule(trigger=trigger, action_list=[act],
                                       proof=self.proof))
            self.rules.append(GeneRule(trigger=trigger2, action_list=[act],
                                       proof=self.proof))
        elif argv[0] == "rule3":
            trigger = GeneTrigger(tactic_restriction=("rewrite -> plus_n_O.", 2))
            trigger2 = GeneTrigger(tactic_restriction=("rewrite <- mult_0_l at 1.", 2))
            trigger3 = GeneTrigger(tactic_restriction=("rewrite <- mult_plus_distr_r.", 2))
            trigger4 = GeneTrigger(tactic_restriction=("rewrite -> mult_plus_distr_l.", 2))
            cmd = ["penalty"]
            act = GeneAction(cmd=cmd, data="1.2")
            self.rules.append(GeneRule(trigger=trigger, action_list=[act],
                                       proof=self.proof))
            self.rules.append(GeneRule(trigger=trigger2, action_list=[act],
                                       proof=self.proof))
            self.rules.append(GeneRule(trigger=trigger3, action_list=[act],
                                       proof=self.proof))
            self.rules.append(GeneRule(trigger=trigger4, action_list=[act],
                                       proof=self.proof))

    def defrag(self, index_list):
        """Defrag some gene"""
        for index in index_list:
            self.population[index].defrag(self.proof)

    def print_stats(self):
        """print tactic usage"""
        stats = {e: 0 for e in self.tactics.all_tactics}
        for gene in self.population:
            for tactic in gene.chromosome:
                try:
                    stats[tactic] += 1
                except KeyError:
                    stats[tactic] = 1

        sorted_stats = sorted(stats.items(),
                              key=operator.itemgetter(1), reverse=True)
        total_tactic = sum(stats.values())
        sum_of_usage = 0.0
        for tactic, count in sorted_stats:
            usage = count / total_tactic
            sum_of_usage += usage
            print("{0}: {1:.4f}%".format(tactic, usage*100))

def myrandint(begin, end):
    """
    randint warrper for begin == end
    """
    if begin == end:
        return begin
    else:
        return randint(begin, end)

def int_max(int_a, int_b):
    """
    max(a, b)
    """
    if int_a > int_b:
        return int_a
    else:
        return int_b

def int_min(int_a, int_b):
    """
    min(a, b)
    """
    if int_a < int_b:
        return int_a
    else:
        return int_b
