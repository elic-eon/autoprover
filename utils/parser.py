import argparse

def getArgs():
    parser = argparse.ArgumentParser(description='Autoprover')
    parser.add_argument("file", type=open, help="a theorem to be proved")
    parser.add_argument("-p", "--population", dest='population',
            type=int, help="population size, default is 1000")
    parser.add_argument("-g", "--max-generation", dest='maxGeneration',
            type=int, help="a maximun generation, defalut is 100")
    parser.add_argument("-m", "--mutate-rate", dest='mutateRate',
            type=float, help="a mutate rate in interval (0, 1), default is 0.25")
    parser.add_argument("-e", "--elite-rate", dest='eliteRate',
            type=float, help="the percentage of elitism, default is 0")
    parser.add_argument("-c", "--cross-rate", dest='crossRate',
            type=int, help="a cross rate, defalut is 0.5")
    parser.add_argument("-t", "--cross-type", dest='crossType',
            type=int, help="different type of cross, default is 0")
    parser.add_argument("-n", "--verify-num", dest='verifyNum',
            type=int, help="number of top proofs to verify in each generation, default is 50")
    args = parser.parse_args()
    return args
