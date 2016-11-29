"""This module provide rules based on triggers and actions
"""
from gp.action import Action
from gp.trigger import Trigger

class Rule:
    """base class"""
    def __init__(self, trigger=None, action_list=None):
        self.trigger = trigger
        self.action_list = action_list

    def set_trigger(self, trigger):
        """set trigger"""
        self.trigger = trigger

    def print_trigger(self):
        """print trigger"""
        print(self.trigger)

class GeneRule(Rule):
    """rules applied on gene"""
    def __init__(self, trigger=None, action_list=None, proof=None):
        super().__init__(trigger, action_list)
        self.proof = proof
        self.type = "gene"

    def check_and_apply(self, gene):
        """Check gene is need to be applied action or not"""
        ret = self.trigger.test(gene)
        if ret["status"]:
            for _ in range(ret["count"]):
                for action in self.action_list:
                    action.apply(gene)
        if ret["update"]:
            gene.update_fitness_for_proof(self.proof)
