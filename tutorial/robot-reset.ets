# INIT
I: rst = 1_1
I: reset_done = False

S1: rst = 1_1
S1: reset_done = False

SD: rst = 0_1
SD: reset_done = True

# TRANS
I -> S1
S1 -> SD
SD -> SD
