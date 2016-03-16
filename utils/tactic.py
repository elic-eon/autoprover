def tacticReader(tacticBase):
    tactics = []
    repeatable = True
    for line in tacticBase:
        line = line.strip()
        if not line.startswith("#"):
            for tactic in line.rstrip().split(','):
                tactics.append((tactic, repeatable))
            repeatable = True
        else:
            if line.startswith("#unrepeatable"):
                repeatable = False
    return tactics
