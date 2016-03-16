def tacticReader(tacticBase):
    tactics = []
    for line in tacticBase:
        line = line.strip()
        if not line.startwith("#"):
            for tactic in line.rstrip().split(','):
                tactics.append((tactic, repeatable))
            repeatable = True
        else:
            if line.startwith("#unrepeatable"):
                repeatable = False
    return tactics
