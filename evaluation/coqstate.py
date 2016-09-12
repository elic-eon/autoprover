"""
define coq
"""

class CoqState():
    """
    coq state data structure
    """
    def __init__(self, text, isProof=False):
        self._is_proof = isProof
        self.data = text
        self.goal = None

    def is_proof(self):
        """
        return if itself is a proof
        """
        return self._is_proof

    def get_goal(self):
        """
        return goal of state
        """
        return self.goal
