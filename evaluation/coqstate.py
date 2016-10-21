"""Coqstate
This module describe the state of coqtop, including hypothesis, current goals
and a coq tactic.

Example:
    current_state = Coqstate(some_coq_output, a_tactic)
"""

class CoqState:
    """
    coq state data structure
    """
    def __init__(self, text, tactic, is_proof=False):
        self._is_proof = is_proof
        self._tactic = tactic
        self.data = text
        self._goal = ""
        self._hypothesis = ""
        self._error = False
        self._no_more_goal = False
        if not self._is_proof:
            self.parse(text)

    def __eq__(self, other):
        return self._goal == other.goal

    def __str__(self):
        return '> %s\n%s\n%s\n%s' % (self._tactic,
                                     self._hypothesis,
                                     "============================",
                                     self._goal)

    def parse(self, text):
        """Parse goal and hypothesis from text
        set _error and _no_more_goal
        """
        goal_flag = False
        for i, line in enumerate(text.split("\n")):
            line = line.strip()
            if line.find("No more subgoals.") > -1:
                self._no_more_goal = True
                return
            elif (line.startswith("Error: No such unproven subgoal")
                  or line.startswith("Error: No such goal.")):
                self._error = True
                self._no_more_goal = True
                return
            elif line.startswith("Error:") or line.startswith("H, H"):
                self._error = True
                return
            if i > 1:
                if line.startswith("==="):
                    goal_flag = True
                else:
                    if goal_flag:
                        self._goal += line + "\n"
                    else:
                        self._hypothesis += line + "\n"
        self._goal = self._goal.rstrip('\n')
        self._hypothesis = self._hypothesis.rstrip('\n')

    @property
    def is_no_more_goal(self):
        """no more goal attribute
        """
        return self._no_more_goal

    @property
    def is_error_state(self):
        """Error state attribute
        """
        return self._error

    @property
    def is_proof(self):
        """
        return if itself is a proof
        """
        return self._is_proof

    @property
    def goal(self):
        """
        return goal of state
        """
        return self._goal

    @property
    def hypothesis(self):
        """
        return hypothesis of state
        """
        return self._hypothesis

    def print_out(self):
        pass
