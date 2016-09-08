class CoqState():
    def __init__(self, text, isProof=False):
        self._isProof = isProof
        self.data = text
        self.goal = None

    def isProof(self):
        return self._isProof

    def getGoal(self):
        return self.goal
