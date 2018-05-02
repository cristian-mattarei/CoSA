I: self.rst = 1_1
I: self.push = 0_1
I: self.pop  = 0_1
I: reset_done = 0_1
# Needed when looking at critical invariant
# I: en.out = 0_1

S0: self.rst = 1_1
S0: self.push = 0_1
S0: self.pop  = 0_1
S0: reset_done = 0_1

S1: self.rst = 0_1
S1: reset_done = 1_1

I -> S0
S0 -> S1
S1 -> S1