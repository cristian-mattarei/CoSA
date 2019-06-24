I: self.config_en = 1_1
I: self.config_data = 0_2
I: pokes_done = False

S0: self.config_en = 0_1
S0: pokes_done = True

I -> S0
S0 -> S0
