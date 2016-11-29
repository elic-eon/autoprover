"""test gene or population"""
class Trigger:
    """Base class"""
    def __init__(self):
        pass

class GeneTrigger(Trigger):
    """Gene trigger"""
    def __init__(self, last_goal=None, tactic_restriction=None):
        super().__init__()
        self.last_goal = last_goal
        self.tactic_restriction = tactic_restriction

    def test(self, gene):
        """test if gene trigger action"""
        if self.last_goal:
            ret = {"status": self.last_goal == gene.goal.rstrip("\n"),
                   "update": True, "count": 1}
            return ret
        elif self.tactic_restriction:
            target_tactic = self.tactic_restriction[0]
            interval = int(self.tactic_restriction[1])
            def check_repeat(tactics):
                """check func"""
                index = 0
                count = 0
                while index < len(tactics):
                    if tactics[index] == target_tactic:
                        for i in range(interval):
                            n_index = index+i+1
                            if n_index >= len(tactics):
                                break
                            else:
                                if tactics[index+i+1] == target_tactic:
                                    count += 1
                    index += 1
                return count
            count = check_repeat(gene.valid_tactics)
            if count > 0:
                return {"status": True, "update": False, "count": count}
            else:
                return {"status": False, "update": False, "count": 1}
            # return func(gene.valid_tactics)
