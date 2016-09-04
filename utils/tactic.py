import random
class TacticsSet():
    def __init__(self, tacticBase=None):
        self.read(tacticBase)

    def read(self, tacticBase):
        self.repeatable = set()
        self.unrepeatable = set()
        repFlag = True

        for line in tacticBase:
            line = line.strip()
            if not line.startswith("#"):
                for tactic in line.rstrip().split(','):
                    if tactic == "":
                        continue
                    if repFlag:
                        self.repeatable.add(tactic+".")
                    else:
                        self.unrepeatable.add(tactic+".")
                repFlag = True
            else:
                if line.startswith("#unrepeatable"):
                    repFlag = False
    def randomSelect(self):
        return random.choice(tuple(self.repeatable | self.unrepeatable))

    def isUnrepeatable(self, tactic):
        return tactic in self.unrepeatable
