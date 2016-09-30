"""
define model for gp
"""
from random import random, randint
from math import floor
from evaluation import evaluation
from gp.gene import Gene

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
        self.proved_individual = None
        self.population = None
        self.current_generation = 0
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
        self.population = []
        for _ in range(size):
            self.population.append(Gene(self.tactics))

    def pre_process(self):
        """
        run before start
        """
        self.current_generation = 1
        self.proved_individual = self.calculate_fitness()


    def start(self, gen=None):
        """
        run the model
        """
        if gen is None:
            local_gen_limit = self.max_generation + 1
        else:
            local_gen_limit = gen

        for _ in range(local_gen_limit):
            # TODO calculate_fitness should not return individual
            print("Generation No.{0}".format(self.current_generation))
            # if self.debug:
                # self.sort_sopulation()
                # for index in range(0, 30):
                    # self.print_gene_by_index(index, False)
            self.crossover()
            self.next_generation()
            if self.current_generation > self.max_generation:
                break

        # self.printGeneByIndex(0, True)
    def next_generation(self):
        """
        next generation
        """
        self.proved_individual = self.calculate_fitness()
        self.current_generation += 1

    def calculate_fitness(self):
        """
        return individual if theorem is proved, o.w return None
        """
        for (index, gene) in enumerate(self.population):
            gene.update_fitness_for_proof(self.proof)
            # print("{0} {1} {2}".format(index, gene.fitness, len(gene)))
            if gene.is_proof():
                self.print_gene_by_index(index, True)
                return index
        return None

    def crossover(self):
        """
        the crossover operation for gp
        """
        self.sort_sopulation()
        elite_amount = round(self.elite_rate * self.population_size)
        # preserve from the top
        new_population = [] + self.population[:elite_amount] # not deep copy
        for _ in range(elite_amount, int(self.population_size/2)):
            # newGene = self.crossBelowCrossRate()
            new_gene, new_gene2 = self.cross_on_arb_seq()
            if random() <= self.mutate_rate:
                self.mutate(new_gene)
            if random() <= self.mutate_rate:
                self.mutate(new_gene2)
            new_population.append(new_gene)
            new_population.append(new_gene2)
        self.population = new_population

    def sort_sopulation(self):
        """
        sort population by length and fitness
        """
        self.population.sort(key=len, reverse=False)
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
        # print("{0} {1} {2} {3}".format(len(geneOfParentOne.chromosome)
            # ,len(geneOfParentTwo.chromosome), len(newChromosome), len(newChromosome2)))
        return Gene(chromosome=new_chromosome), Gene(chromosome=new_chromosome2)

    def mutate(self, gene):
        """
        the mutate operation
        """
        if len(gene) == 1:
            gene.chromosome[0] = self.tactics.random_select()
        else:
            gene.chromosome[randint(0, len(gene)-1)] = \
                    self.tactics.random_select()

    def edit(self):
        """Human involved modification of some gene of the population
        """
        self.sort_sopulation()
        editable_amount = 1
        for index in range(editable_amount):
            self.population[index].modification()

    def print_gene_by_index(self, index, print_pcript):
        """
        print a gene
        """
        # TODO move print function to gp.gene
        # print(self.population[index].fitness)
        print("{0} {1}".format(len(self.population[index].chromosome),
                               self.population[index].fitness))
        if print_pcript:
            script = evaluation.preprocess(self.proof.theorem,
                                           self.population[index].chromosome)
            for tactic in script:
                print(tactic)

    def is_proved(self):
        """
        check population has a proof
        """
        return self.proved_individual is None

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
