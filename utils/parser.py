import argparse

def getArgs():
    parser = argparse.ArgumentParser(description='Autoprover')
    parser.add_argument("-i", "--input", help="your input", default=None)
    args = parser.parse_args()
    return args
