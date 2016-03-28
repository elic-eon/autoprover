import subprocess
from subprocess import PIPE, STDOUT

def preprocess(theorem, chromosome):
    script = [] + theorem
    script += ["Proof."]
    script += ["intros."]
    script += [x[0] for x in chromosome]
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

def evaluateResult(result, theoremName):
    validTactic = -3
    errorTactic = 0
    isProved = False

    totalSteps = splitCoqtopResult(result, theoremName)
    print(totalSteps)

    return (False, 1)

    for line in result.split("\n"):
        line = line.strip()
        print(line)
        if (line.startswith("============================")):
            validTactic += 1
        if (line.startswith("Error: ")):
            if (line.startswith("Error: No such unproven subgoal")):
                isProved = True
                break
            else:
                errorTactic += 1
                isProved = False
                break
        if (line.startswith("Qed.")):
            isProved = True
            break
    return (isProved, validTactic)

def splitCoqtopResult(result, theoremName):
    totalSteps = []
    step = []
    state = "begin"
    spliter = theoremName + " <"
    print(spliter)
    for line in result.split("\n"):
        line = line.strip()
        # print(line)
        if state == "begin":
            if line.startswith(spliter):
                state = "start"
                step = []
        else:
            if line.startswith(spliter):
                state == "state"
                totalSteps.append(step)
                step = []
            else:
                step.append(line)
    else:
        totalSteps.append(step)
    i = 0
    for s in totalSteps:
        print(i)
        for l in s:
            print(l)
        i += 1
        print("")
    exit(1)
    return totalSteps
