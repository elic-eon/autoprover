import subprocess
from subprocess import PIPE, STDOUT
from eval.coqState import CoqState

def preprocess(theorem, chromosome):
    script = [] + theorem
    script += ["Proof."]
    script += ["intros."]
    script += chromosome
    script += ["Qed."]
    return script

def runCoqtop(script):
    coqtop = subprocess.Popen('coqtop',
            shell=False, stdin=PIPE, stdout=PIPE, stderr=STDOUT)

    # truncate to byte string
    byteString = b''
    for line in script:
        byteString += line.encode('utf-8')
        byteString += b'\n'

    # communicate with coqtop
    (out, err) = coqtop.communicate(input=byteString)

    return out.decode('utf-8')

def getCoqStates(result, theoremName):
    splitedResult = splitCoqtopResult(result, theoremName)

    filteredResult = []
    for (i, step) in enumerate(splitedResult):
        if (i == 0):
            filteredResult.append(CoqState(step))
            continue

        if noMoreGoal(step):
            filteredResult.append(CoqState(None, isProof=True))
            break
        elif step != splitedResult[i-1]:
            if isErrorStep(step):
                break
            else:
                filteredResult.append(CoqState(step))
        else:
            break

    return filteredResult
    

def evaluateResult(result, theoremName, errorThreshold = 0,
        uselessThreshold = 0):
    validTactic = -1
    errorTactic = 0
    uselessTactic = 0
    isProved = False

    totalSteps = splitCoqtopResult(result, theoremName)

    for (i, step) in enumerate(totalSteps):
        if (i == 0):
            validTactic += 1
            continue

        if noMoreGoal(step):
            return (True, validTactic)
        if checkPrevState(totalSteps, i) is True:
            if isErrorStep(step):
                errorTactic += 1
            else:
                validTactic += 1
        else:
            uselessTactic += 1
        if errorTactic > errorThreshold or uselessTactic > uselessThreshold:
            break

    return (isProved, validTactic)

def checkPrevState(totalSteps, curIdx):
    for i in range(curIdx):
        if totalSteps[curIdx] == totalSteps[i]:
            return False
    else:
        return True

def isErrorStep(step):
    for line in step:
        if line.startswith("Error:"):
            return True
    else:
        return False

def noMoreGoal(step):
    for line in step:
        if line.startswith("Error: No such unproven subgoal"):
            return True
        if line.find("No more subgoals.") > -1:
            return True
    else:
        return False

def splitCoqtopResult(result, theoremName):
    totalSteps = []
    step = []
    state = "begin"
    spliter = theoremName + " <"

    for line in result.split("\n"):
        line = line.strip()
        if state == "begin":
            if line.startswith(spliter):
                state = "start"
                step = [line]
        else:
            if line.startswith(spliter):
                state == "state"
                totalSteps.append(step)
                step = [line]
            else:
                step.append(line)
    else:
        totalSteps.append(step)

    return totalSteps
