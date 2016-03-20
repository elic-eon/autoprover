import subprocess
from subprocess import PIPE, STDOUT

def preprocess(theorem, chromosome):
    script = [] + theorem
    script += ["Proof."]
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

def evaluateResult(result):
    validTactic = 0
    errorTactic = 0
    isProved = False

    for line in result.split("\n"):
        line = line.strip()
        if (line.startswith("============================")):
            validTactic += 1
        if (line.startswith("Error: ")):
            errorTactic += 1
        if (line.startswith("Qed.")):
            isProved = True
            break
    return (isProved, validTactic)
