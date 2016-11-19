"""This module provide rules based on triggers and actions
"""
from gp.action import Action
from gp.trigger import Trigger

class Rule:
    """base class"""
    def __init__(self, trigger=None, action_list=[]):
        self.trigger = trigger
        self.action_list = action_list

    def setTrigger(self):
        pass

    def printTrigger(self):
        pass

class GeneRule(Rule):
    """rules applied on gene"""
    pass

def main():
    """main test funciton"""
    cmd = ["edit", "1"]
    data = ["append",
            "change ((d (S n) + 10 * number n d) mod 3 = (d (S n) + sumdigits n d) mod 3)."]
    act = Action(cmd=cmd, data=data)
    trigger = Trigger(last_goal="number (S n) d mod 3 = sumdigits (S n) d mod 3")
    a_rule = Rule(trigger=trigger, action_list=[act])

if __name__ == "__main__":
    main()
