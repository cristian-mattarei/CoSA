I: nreset = 1_1
I: reset_done = False

S1: nreset = 0_1
S1: reset_done = False

S2: nreset = 0_1
S2: reset_done = False

SD: nreset = 1_1
SD: reset_done = True

# TRANS
I -> S1
S1 -> S2
S2 -> SD
SD -> SD