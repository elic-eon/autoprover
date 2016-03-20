from gp.gene import Gene
from random import random, randint
from math import floor

class GPModel:
    def __init__(self, args=None, populationSize=None, maxGeneration=None,
            mutateRate=None, eliteRate=None, crossRate=None,
            crossType=None, verifyNum=None, proof=None, tactics=None):
        self.populationSize = populationSize or args.populationSize
        self.maxGeneration = maxGeneration or args.maxGeneration
        self.mutateRate = mutateRate or args.mutateRate
        self.eliteRate = eliteRate or args.eliteRate
        self.crossRate = crossRate or args.crossRate
        self.crossType = crossType or args.crossType
        self.verifyNum = verifyNum or args.verifyNum
        self.proof = proof
        self.tactics = tactics

    def showProp(self):
        print(self.populationSize)
        print(self.maxGeneration)
        print(self.mutateRate)
        print(self.eliteRate)
        print(self.crossRate)
        print(self.crossType)
        print(self.verifyNum)
        print(self.proof)

    def initPopulation(self, size):
        self.population = []
        for individual in range(size):
            self.population.append(Gene(self.tactics))

    def initProcess(self):
        self.currentGeneration = 1
        self.provedIndividual = None

    def nextGeneration(self):
        self.currentGeneration += 1

    def calculateFitness(self):
        # return individual if theorem is proved, o.w return None
        for (index, gene) in enumerate(self.population):
            (isProved, fitness) = self.proof.calculateFitness(gene.chromosome)
            # print("{0} {1}".format(index, fitness))
            gene.updateFitness(fitness)
            self.population[index] = gene
            if isProved:
                return index
        return None

    def sortPopulation(self):
        self.population.sort(key = lambda x : x.fitness, reverse=True)

    def crossBelowCrossRate(self):
        parentOneIndex = randint(
                0, floor(self.populationSize * self.crossRate)-1)
        parentTwoIndex = randint(
                0, floor(self.populationSize * self.crossRate)-1)
        geneOfParentOne = self.population[parentOneIndex]
        geneOfParentTwo = self.population[parentTwoIndex]
        crossPoint = randint(0, min(geneOfParentOne.length(),
            geneOfParentTwo.length())-1)
        # TODO merge class Chromosome into Gene, chromosome simply a list of
        # tactics, no need to be a class
        newChromosome = []
        newChromosome += geneOfParentOne.chromosome[:crossPoint]
        newChromosome += geneOfParentTwo.chromosome[crossPoint:]
        return Gene(chromosome=newChromosome)


    def crossover(self):
        self.sortPopulation()
        eliteAmount = round(self.eliteRate * self.populationSize)
        newPopulation = [] + self.population[:eliteAmount] # not deep copy
        for childIndex in range(eliteAmount, self.populationSize):
            newGene = self.crossBelowCrossRate()
            newPopulation.append(newGene)
            if random() <= self.mutateRate:
                self.mutate(newGene)

        self.population = newPopulation

    def mutate(self, gene):
        gene.chromosome[randint(0, gene.length()-1)] = self.tactics[randint(
            0, len(self.tactics)-1)]

    def start(self):
        self.initPopulation(self.populationSize)
        self.initProcess()
        while (True):
            # if (self.currentGeneration > self.maxGeneration):
            if (self.currentGeneration > 1):
                break;
            print("Generation No.{0}".format(self.currentGeneration))
            self.provedIndividual = self.calculateFitness()
            if self.provedIndividual is not None:
                break;
            self.crossover()
            self.nextGeneration()

    def isProved(self):
        if self.provedIndividual is None:
            return False
        else:
            return True
