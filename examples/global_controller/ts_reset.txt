# INIT
I: self.reset_in = 0_1
I: reset_done = 0_1

# STATES
S1: self.reset_in = 1_1
S1: reset_done = 0_1

S2: self.reset_in = 0_1
S2: reset_done = 0_1

S3: self.reset_in = 0_1
S3: reset_done = 1_1

# TRANSITIONS
I -> S1
S2 -> S2
S2 -> S3
S3 -> S3
