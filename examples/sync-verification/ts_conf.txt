# INIT
I: self.reset = 0_1
I: conf_done = 0_1
I: self.config_addr = 00000000
I: self.config_data = 00000000
I: self.tile_id = 0036

# STATES

S0: self.config_addr = 00000000
S0: self.tile_id = 0036
S0: self.config_data = 00000000
S0: self.reset = 0_1
S0: conf_done = 0_1

S0a: self.config_addr = 00000000
S0a: self.tile_id = 0036
S0a: self.config_data = 00000000
S0a: self.reset = 1_1
S0a: conf_done = 0_1

S1: self.config_addr = 00000000
S1: self.tile_id = 0036
S1: self.config_data = 00000000
S1: self.reset = 0_1
S1: conf_done = 0_1

S1a: self.config_addr = F1000036
S1a: self.tile_id = 0036
S1a: self.config_data = 00000002
S1a: self.reset = 0_1
S1a: conf_done = 0_1

S2: self.config_addr = F1000036
S2: self.tile_id = 0036
S2: self.config_data = 00000002
S2: self.reset = 0_1
S2: conf_done = 0_1

S2a: self.config_addr = FF000036
S2a: self.tile_id = 0036
S2a: self.config_data = 0002000B
S2a: self.reset = 0_1
S2a: conf_done = 0_1

S3: self.config_addr = FF000036
S3: self.tile_id = 0036
S3: self.config_data = 0002000B
S3: self.reset = 0_1
S3: conf_done = 0_1

S3a: self.config_addr = 00020036
S3a: self.tile_id = 0036
S3a: self.config_data = 00000005
S3a: self.reset = 0_1
S3a: conf_done = 0_1

S4: self.config_addr = 00020036
S4: self.tile_id = 0036
S4: self.config_data = 00000005
S4: self.reset = 0_1
S4: conf_done = 0_1

S4a: self.config_addr = 00080036
S4a: self.tile_id = 0036
S4a: self.config_data = C0200000
S4a: self.reset = 0_1
S4a: conf_done = 0_1

S5: self.config_addr = 00080036
S5: self.tile_id = 0036
S5: self.config_data = C0200000
S5: self.reset = 0_1
S5: conf_done = 0_1

S5a: self.config_addr = 00000000
S5a: self.tile_id = 0036
S5a: self.config_data = 00000000
S5a: self.reset = 0_1
S5a: conf_done = 1_1

# TRANSITIONS
I -> S0
S0 -> S0a
S0a -> S1
S1 -> S1a
S1a -> S2
S2 -> S2a
S2a -> S3
S3 -> S3a
S3a -> S4
S4 -> S4a
S4a -> S5
S5 -> S5a
S5a -> S5a

