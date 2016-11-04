#!/usr/bin/env python3
"""Autoprover
"""

# bench 1000 population: 42.31s user 13.83s system 98% cpu 56.944 total
from proof import Proof
from utils import parser
from utils.tactic import TacticsSet
from utils.log import reg_logger
from gp.model import GPModel

HELP_MESSAGE = """help(h): Print help message.
next(n) <step>: Start n generation.
show-property(show-prop): Show property of GP model.
edit(e): Edit best gene.
list(l): List some property of population.
show-proofs(sp): Show proofs which is found.
"""

def main():
    """Main program
    """
    reg_logger()
    args = parser.get_args()
    tactics = TacticsSet(args.tacticBase)
    proof = Proof(input_file=args.file, tactics=tactics)

    gp_model = GPModel(args=args, proof=proof, tactics=tactics)
    while True:
        try:
            input_string = input("> ")
        except EOFError:
            break

        input_list = input_string.split(" ")
        if input_list[0] == "h" or input_list[0] == "help":
            print(HELP_MESSAGE)
        elif input_list[0] == "show-property" or input_list[0] == "show-prop":
            gp_model.show_prop()
        elif input_list[0] == "show-proof" or input_list[0] == "sp":
            gp_model.show_proofs()
        elif input_list[0] == "n" or input_list[0] == "next":
            step = int(input_list[1])
            gp_model.start(gen=step)
        elif input_list[0] == "defrag":
            try:
                index = int(input_list[1])
            except IndexError:
                print("Invaild command")
            gp_model.defrag(index_list=[index])
        elif input_list[0] == "edit" or input_list[0] == "e":
            try:
                index = input_list[1]
                gp_model.edit(index=int(index))
            except IndexError:
                gp_model.edit()
        elif input_list[0] == "list" or input_list[0] == "l":
            sub_cmd = input_list[1:]
            gp_model.list(sub_cmd)
        elif input_list[0] == "set" or input_list[0] == "s":
            sub_cmd = input_list[1:]
            gp_model.set_attributes(sub_cmd)
        else:
            print("Invaild command")


if __name__ == "__main__":
    main()
