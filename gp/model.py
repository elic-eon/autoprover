from gp.gene import Gene
from random import random, randint
from math import floor
from eval import eval

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
        self.debug = args.debug
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

    def start(self):
        self.initPopulation(self.populationSize)
        self.preProcess()
        while (True):
            self.provedIndividual = self.calculateFitness()
            if self.provedIndividual is not None:
                # TODO add to a list, do not break
                break;
            if (self.currentGeneration > self.maxGeneration):
                break;
            print("Generation No.{0}".format(self.currentGeneration))
            self.sortPopulation()
            if self.debug:
                for index in range(0, 30):
                    self.printGeneByIndex(index, False)
            self.crossover()
            self.nextGeneration()
        # self.printGeneByIndex(0, True)

    def initPopulation(self, size):
        self.population = []
        for individual in range(size):
            self.population.append(Gene(self.tactics))

    def preProcess(self):
        self.currentGeneration = 1
        self.provedIndividual = None

    def nextGeneration(self):
        self.currentGeneration += 1

    def calculateFitness(self):
        # return individual if theorem is proved, o.w return None
        for (index, gene) in enumerate(self.population):
            (isProved, fitness) = self.proof.calculateFitness(gene.chromosome)
            # print("{0} {1} {2}".format(index, fitness, gene.length()))
            gene.updateFitness(fitness)
            if isProved:
                self.printGeneByIndex(index, True)
                return index
        return None

    def sortPopulation(self):
        self.population.sort(key = lambda x : x.length(), reverse=False)
        self.population.sort(key = lambda x : x.fitness, reverse=True)

    def crossBelowCrossRate(self):
        parentOneIndex = randint(
                0, floor(self.populationSize * self.crossRate)-1)
        parentTwoIndex = randint(
                0, floor(self.populationSize * self.crossRate)-1)
        geneOfParentOne = self.population[parentOneIndex]
        geneOfParentTwo = self.population[parentTwoIndex]
        crossPoint = randint(0,
                min(geneOfParentOne.length(),geneOfParentTwo.length())-1)
        newChromosome = []
        newChromosome += geneOfParentOne.chromosome[:crossPoint]
        newChromosome += geneOfParentTwo.chromosome[crossPoint:]
        if (newChromosome[crossPoint][1] is False
                and crossPoint < len(newChromosome)-1):
            if newChromosome[crossPoint] == newChromosome[crossPoint+1]:
                del newChromosome[crossPoint]
        return Gene(chromosome=newChromosome)

    def crossOnArbSeq(self, slmax=6):
        parentOneIndex = randint(
                0, floor(self.populationSize * self.crossRate)-1)
        parentTwoIndex = randint(
                0, floor(self.populationSize * self.crossRate)-1)
        geneOfParentOne = self.population[parentOneIndex]
        geneOfParentTwo = self.population[parentTwoIndex]

        p1Begin = myrandint(0, geneOfParentOne.length()-1)
        p1End = p1Begin + myrandint(1,
                min(slmax, geneOfParentOne.length()-p1Begin))
        p2Begin = myrandint(0, geneOfParentTwo.length()-1)
        p2End = p2Begin + myrandint(1,
                min(slmax, geneOfParentTwo.length()-p2Begin))
        newChromosome = []
        newChromosome += geneOfParentOne.chromosome[:p1Begin]
        newChromosome += geneOfParentTwo.chromosome[p2Begin:p2End]
        newChromosome += geneOfParentOne.chromosome[p1End:]
        newChromosome2 = []
        newChromosome2 += geneOfParentTwo.chromosome[:p2Begin]
        newChromosome2 += geneOfParentOne.chromosome[p1Begin:p1End]
        newChromosome2 += geneOfParentTwo.chromosome[p2End:]
        # print("{0} {1} {2} {3}".format(len(geneOfParentOne.chromosome)
            # ,len(geneOfParentTwo.chromosome), len(newChromosome), len(newChromosome2)))
        return Gene(chromosome=newChromosome), Gene(chromosome=newChromosome2)

    def crossover(self):
        self.sortPopulation()
        eliteAmount = round(self.eliteRate * self.populationSize)
        newPopulation = [] + self.population[:eliteAmount] # not deep copy
        for childIndex in range(eliteAmount, int(self.populationSize/2)):
            # newGene = self.crossBelowCrossRate()
            newGene, newGene2 = self.crossOnArbSeq()
            if random() <= self.mutateRate:
                self.mutate(newGene)
            if random() <= self.mutateRate:
                self.mutate(newGene2)
            newPopulation.append(newGene)
            newPopulation.append(newGene2)
        self.population = newPopulation

    def mutate(self, gene):
        if (gene.length() == 1):
            gene.chromosome[0] = self.tactics.randomSelect()
        else:
            gene.chromosome[randint(0, 
                gene.length()-1)] = self.tactics.randomSelect()

    def printGeneByIndex(self, index, printScript):
        # print(self.population[index].fitness)
        print("{0} {1}".format(len(self.population[index].chromosome),
            self.population[index].fitness))
        if (printScript):
            script = eval.preprocess(self.proof.theorem,
                    self.population[index].chromosome)
            for tactic in script:
                print(tactic)

    def isProved(self):
        if self.provedIndividual is None:
            return False
        else:
            return True

def myrandint(a, b):
    if a == b:
        return a
    else:
        return randint(a, b)

def max(a, b):
    if a > b:
        return a
    else:
        return b

def min(a, b):
    if a < b:
        return a
    else:
        return b
