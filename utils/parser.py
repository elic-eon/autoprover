import argparse

def getArgs():
    parser = argparse.ArgumentParser(description='Autoprover')
    parser.add_argument("file", type=open, help="a theorem to be proved")
    args = parser.parse_args()
    return args
