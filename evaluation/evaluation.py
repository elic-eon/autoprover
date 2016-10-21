"""evaluation function for chromosome
"""

import subprocess
from subprocess import PIPE, STDOUT
from evaluation.coqstate import CoqState

def preprocess(theorem, chromosome):
    """
    convert chromosome to complete Coq script
    """
    script = [] + theorem
    script += chromosome
    script += ["Qed."]
    return script

def run_coqtop(script):
    """run Coq script and return output

    Args:
        script: list of string (tactic) usually end with '.'

    Returns:
        string: the output of coqtop
    """
    coqtop = subprocess.Popen('coqtop', shell=False,
                              stdin=PIPE, stdout=PIPE, stderr=STDOUT)

    # truncate to byte string
    byte_string = b''
    for line in script:
        byte_string += line.encode('utf-8')
        byte_string += b'\n'

    # communicate with coqtop
    (out, _) = coqtop.communicate(input=byte_string)

    return out.decode('utf-8')

def get_coq_states(result, proof, chromosome, threshold=-1):
    """return valid coq states, will ignore useless and error steps

    Args:
        result (string): Plain text output from coqtop
        proof (Proof): Proof instance
        chromosome (list): the corresponse chromosome of result
        threshold (int): the number of error tactic tolerance, -1 will ignore
            all error.

    Returns:
        list of Coqstate
    """
    # the first and the last is useless
    splited_result = split_coqtop_result(result, proof.theorem_name)[1:-1]

    offset = proof.offset
    coq_states = []
    tactics_set = set()
    error_count = 0
    for (i, step) in enumerate(splited_result):
        if i < offset:
            coq_states.append(CoqState(step, proof.pre_feed_tactic[i]))
            continue

        # create a new state
        if i == (len(splited_result)-1):
            # lastest step
            state = CoqState(step, "Qed.")
        else:
            state = CoqState(step, chromosome[i-offset])

        if state.is_no_more_goal:
            coq_states.append(state)
        elif state.is_error_state or state == coq_states[-1]:
            error_count += 1
        elif proof.tactics.is_unrepeatable(chromosome[i-offset]):
            if chromosome[i-offset] in tactics_set:
                error_count += 1
            else:
                tactics_set.add(chromosome[i-offset])
        else:
            coq_states.append(state)

        if error_count == threshold:
            break

    return coq_states

def split_coqtop_result(result, theorem_name):
    """
    split result into steps
    """
    spliter = theorem_name + " <"
    return [spliter+x for x in result.split(spliter)]

def calculate_fitness(coq_states):
    """calculate fitness from coqstates
    score = sum(len(hypothesis)/len(goal))
    """
    score = 0.0
    for state in coq_states:
        try:
            score += len(state.hypothesis) / len(state.goal)
        except ZeroDivisionError:
            print(state.data)
            exit(1)
    return score
