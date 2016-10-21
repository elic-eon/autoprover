"""evaluation function for chromosome
"""

import subprocess
from subprocess import PIPE, STDOUT
from evaluation.coqstate import CoqState

def preprocess(theorem, chromosome):
    """
    convert chromosome to complete Coq script

    Args:
        theorem (list): a list of string contains theorem or some pre-provided
            tactic.
        chromosome (list): a list of string.

    Returns:
        byte: a byte string will be passed to coqtop
    """
    script = b''
    script += b'\n'.join(line.encode("utf-8") for line in theorem) + b'\n'
    script += b'\n'.join(line.encode("utf-8") for line in chromosome) + b'\n'
    script += b'Qed.'
    return script

def run_coqtop(script):
    """run Coq script and return output

    Args:
        script (byte): a coq script

    Returns:
        string: the output of coqtop
    """
    coqtop = subprocess.Popen('coqtop', shell=False,
                              stdin=PIPE, stdout=PIPE, stderr=STDOUT)

    # communicate with coqtop
    (out, _) = coqtop.communicate(input=script)

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

        if state.is_proof:
            coq_states.append(state)
            break
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
    """ split result into steps

    Args:
        result (string): the output of coqtop

    Returns:
        list: a list of states(string) of coqtop
    """
    spliter = theorem_name + " <"
    return [spliter+x for x in result.split(spliter)]

def calculate_fitness(coq_states):
    """calculate fitness from coqstates
    score = sum(len(hypothesis)/len(goal))

    Args:
        coq_states (list): a list of Coqstate

    Returns:
        double: represent fitness of a gene, higher is better.

    If raise ZeroDivisionError, means there is a bug.
    """
    score = 0.0
    for state in coq_states:
        try:
            score += len(state.hypothesis) / len(state.goal)
        except ZeroDivisionError:
            print(state.data)
            exit(1)
    return score
