"""
define TacticSet
"""
import random
import logging

class TacticsSet():
    """
    regist a tactic set, and some operation
    """
    def __init__(self, tacticBase=None):
        self.read(tacticBase)

    def read(self, tactic_base):
        """
        read tactics from file
        """
        self.repeatable = set()
        self.unrepeatable = set()
        rep_flag = True

        for line in tactic_base:
            line = line.strip()
            if not line.startswith("#"):
                for tactic in line.rstrip().split(','):
                    if tactic == "":
                        continue
                    if rep_flag:
                        self.repeatable.add(tactic+".")
                    else:
                        self.unrepeatable.add(tactic+".")
                rep_flag = True
            else:
                if line.startswith("#unrepeatable"):
                    rep_flag = False
        logging.info("%d tactics loaded",
                     len(self.repeatable) + len(self.unrepeatable))

    def random_select(self):
        """
        return a tactic in the set
        """
        return random.choice(tuple(self.repeatable | self.unrepeatable))

    def is_unrepeatable(self, tactic):
        """
        if tactic in the set
        """
        return tactic in self.unrepeatable
