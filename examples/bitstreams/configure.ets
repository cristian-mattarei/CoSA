# INIT
I: self.reset_in = 0_1
I: conf_done = 0_1
I: self.config_addr_in = 00000000
I: self.config_data_in = 00000000

# STATES
S0: self.reset_in = 0_1
S0: conf_done = 0_1
S0: self.config_addr_in = 00000000
S0: self.config_data_in = 00000000

S0a: self.reset_in = 1_1
S0a: conf_done = 0_1
S0a: self.config_addr_in = 00000000
S0a: self.config_data_in = 00000000

S1: self.reset_in = 0_1
S1: conf_done = 0_1
S1: self.config_addr_in = 00000000
S1: self.config_data_in = 00000000

S1a: self.reset_in = 0_1
S1a: conf_done = 0_1
S1a: self.config_addr_in = F0000007
S1a: self.config_data_in = 00000000

S2: self.reset_in = 0_1
S2: conf_done = 0_1
S2: self.config_addr_in = F0000007
S2: self.config_data_in = 00000000

S2a: self.reset_in = 0_1
S2a: conf_done = 0_1
S2a: self.config_addr_in = FF000007
S2a: self.config_data_in = 00080000

S3: self.reset_in = 0_1
S3: conf_done = 0_1
S3: self.config_addr_in = FF000007
S3: self.config_data_in = 00080000

S3a: self.reset_in = 0_1
S3a: conf_done = 0_1
S3a: self.config_addr_in = 00030007
S3a: self.config_data_in = 00000000

S4: self.reset_in = 0_1
S4: conf_done = 0_1
S4: self.config_addr_in = 00030007
S4: self.config_data_in = 00000000

S4a: self.reset_in = 0_1
S4a: conf_done = 0_1
S4a: self.config_addr_in = 00080007
S4a: self.config_data_in = 0000000E

S5: self.reset_in = 0_1
S5: conf_done = 0_1
S5: self.config_addr_in = 00080007
S5: self.config_data_in = 0000000E

S5a: self.reset_in = 0_1
S5a: conf_done = 0_1
S5a: self.config_addr_in = FF000008
S5a: self.config_data_in = 000A0000

S6: self.reset_in = 0_1
S6: conf_done = 0_1
S6: self.config_addr_in = FF000008
S6: self.config_data_in = 000A0000

S6a: self.reset_in = 0_1
S6a: conf_done = 0_1
S6a: self.config_addr_in = 00020008
S6a: self.config_data_in = 00000001

S7: self.reset_in = 0_1
S7: conf_done = 0_1
S7: self.config_addr_in = 00020008
S7: self.config_data_in = 00000001

S7a: self.reset_in = 0_1
S7a: conf_done = 0_1
S7a: self.config_addr_in = 00030008
S7a: self.config_data_in = 00000005

S8: self.reset_in = 0_1
S8: conf_done = 0_1
S8: self.config_addr_in = 00030008
S8: self.config_data_in = 00000005

S8a: self.reset_in = 0_1
S8a: conf_done = 0_1
S8a: self.config_addr_in = 00080008
S8a: self.config_data_in = 00300001

S9: self.reset_in = 0_1
S9: conf_done = 0_1
S9: self.config_addr_in = 00080008
S9: self.config_data_in = 00300001

S9a: self.reset_in = 0_1
S9a: conf_done = 0_1
S9a: self.config_addr_in = F1000009
S9a: self.config_data_in = 00000007

S10: self.reset_in = 0_1
S10: conf_done = 0_1
S10: self.config_addr_in = F1000009
S10: self.config_data_in = 00000007

S10a: self.reset_in = 0_1
S10a: conf_done = 0_1
S10a: self.config_addr_in = FF000009
S10a: self.config_data_in = 0002000B

S11: self.reset_in = 0_1
S11: conf_done = 0_1
S11: self.config_addr_in = FF000009
S11: self.config_data_in = 0002000B

S11a: self.reset_in = 0_1
S11a: conf_done = 0_1
S11a: self.config_addr_in = 00020009
S11a: self.config_data_in = 00000000

S12: self.reset_in = 0_1
S12: conf_done = 0_1
S12: self.config_addr_in = 00020009
S12: self.config_data_in = 00000000

S12a: self.reset_in = 0_1
S12a: conf_done = 0_1
S12a: self.config_addr_in = 00080009
S12a: self.config_data_in = 00300001

S13: self.reset_in = 0_1
S13: conf_done = 0_1
S13: self.config_addr_in = 00080009
S13: self.config_data_in = 00300001

S13a: self.reset_in = 0_1
S13a: conf_done = 0_1
S13a: self.config_addr_in = 00090009
S13a: self.config_data_in = 00000000

S14: self.reset_in = 0_1
S14: conf_done = 0_1
S14: self.config_addr_in = 00090009
S14: self.config_data_in = 00000000

S14a: self.reset_in = 0_1
S14a: conf_done = 0_1
S14a: self.config_addr_in = 0003000A
S14a: self.config_data_in = 00000C00

S15: self.reset_in = 0_1
S15: conf_done = 0_1
S15: self.config_addr_in = 0003000A
S15: self.config_data_in = 00000C00

S15a: self.reset_in = 0_1
S15a: conf_done = 0_1
S15a: self.config_addr_in = 000A000A
S15a: self.config_data_in = 00000000

S16: self.reset_in = 0_1
S16: conf_done = 0_1
S16: self.config_addr_in = 000A000A
S16: self.config_data_in = 00000000

S16a: self.reset_in = 0_1
S16a: conf_done = 0_1
S16a: self.config_addr_in = 000D000A
S16a: self.config_data_in = 00000000

S17: self.reset_in = 0_1
S17: conf_done = 0_1
S17: self.config_addr_in = 000D000A
S17: self.config_data_in = 00000000

S17a: self.reset_in = 0_1
S17a: conf_done = 0_1
S17a: self.config_addr_in = 0008000D
S17a: self.config_data_in = 40000000

S18: self.reset_in = 0_1
S18: conf_done = 0_1
S18: self.config_addr_in = 0008000D
S18: self.config_data_in = 40000000

S18a: self.reset_in = 0_1
S18a: conf_done = 0_1
S18a: self.config_addr_in = 0009000F
S18a: self.config_data_in = 40000000

S19: self.reset_in = 0_1
S19: conf_done = 0_1
S19: self.config_addr_in = 0009000F
S19: self.config_data_in = 40000000

S19a: self.reset_in = 0_1
S19a: conf_done = 0_1
S19a: self.config_addr_in = F1000012
S19a: self.config_data_in = 00000007

S20: self.reset_in = 0_1
S20: conf_done = 0_1
S20: self.config_addr_in = F1000012
S20: self.config_data_in = 00000007

S20a: self.reset_in = 0_1
S20a: conf_done = 0_1
S20a: self.config_addr_in = FF000012
S20a: self.config_data_in = 0002000B

S21: self.reset_in = 0_1
S21: conf_done = 0_1
S21: self.config_addr_in = FF000012
S21: self.config_data_in = 0002000B

S21a: self.reset_in = 0_1
S21a: conf_done = 0_1
S21a: self.config_addr_in = 00020012
S21a: self.config_data_in = 00000005

S22: self.reset_in = 0_1
S22: conf_done = 0_1
S22: self.config_addr_in = 00020012
S22: self.config_data_in = 00000005

S22a: self.reset_in = 0_1
S22a: conf_done = 0_1
S22a: self.config_addr_in = 00080012
S22a: self.config_data_in = C0000000

S23: self.reset_in = 0_1
S23: conf_done = 0_1
S23: self.config_addr_in = 00080012
S23: self.config_data_in = C0000000

S23a: self.reset_in = 0_1
S23a: conf_done = 0_1
S23a: self.config_addr_in = 00000013
S23a: self.config_data_in = 000000FF

S24: self.reset_in = 0_1
S24: conf_done = 0_1
S24: self.config_addr_in = 00000013
S24: self.config_data_in = 000000FF

S24a: self.reset_in = 0_1
S24a: conf_done = 0_1
S24a: self.config_addr_in = FF000013
S24a: self.config_data_in = 0000E000

S25: self.reset_in = 0_1
S25: conf_done = 0_1
S25: self.config_addr_in = FF000013
S25: self.config_data_in = 0000E000

S25a: self.reset_in = 0_1
S25a: conf_done = 0_1
S25a: self.config_addr_in = 00080013
S25a: self.config_data_in = 00000000

S26: self.reset_in = 0_1
S26: conf_done = 0_1
S26: self.config_addr_in = 00080013
S26: self.config_data_in = 00000000

S26a: self.reset_in = 0_1
S26a: conf_done = 0_1
S26a: self.config_addr_in = 00090013
S26a: self.config_data_in = 00000003

S27: self.reset_in = 0_1
S27: conf_done = 0_1
S27: self.config_addr_in = 00090013
S27: self.config_data_in = 00000003

S27a: self.reset_in = 0_1
S27a: conf_done = 0_1
S27a: self.config_addr_in = 00080014
S27a: self.config_data_in = 00000000

S28: self.reset_in = 0_1
S28: conf_done = 0_1
S28: self.config_addr_in = 00080014
S28: self.config_data_in = 00000000

S28a: self.reset_in = 0_1
S28a: conf_done = 0_1
S28a: self.config_addr_in = 00090014
S28a: self.config_data_in = 80000000

S29: self.reset_in = 0_1
S29: conf_done = 0_1
S29: self.config_addr_in = 00090014
S29: self.config_data_in = 80000000

S29a: self.reset_in = 0_1
S29a: conf_done = 0_1
S29a: self.config_addr_in = 00020015
S29a: self.config_data_in = 00200000

S30: self.reset_in = 0_1
S30: conf_done = 0_1
S30: self.config_addr_in = 00020015
S30: self.config_data_in = 00200000

S30a: self.reset_in = 0_1
S30a: conf_done = 0_1
S30a: self.config_addr_in = 0004000A
S30a: self.config_data_in = 00000054

S31: self.reset_in = 0_1
S31: conf_done = 0_1
S31: self.config_addr_in = 0004000A
S31: self.config_data_in = 00000054

S31a: self.config_addr_in = 00000000
S31a: self.config_data_in = 00000000
S31a: self.reset_in = 0_1
S31a: conf_done = 1_1

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
S5a -> S6
S6 -> S6a
S6a -> S7
S7 -> S7a
S7a -> S8
S8 -> S8a
S8a -> S9
S9 -> S9a
S9a -> S10
S10 -> S10a
S10a -> S10
S10 -> S10a
S10a -> S11
S11 -> S11a
S11a -> S12
S12 -> S12a
S12a -> S13
S13 -> S13a
S13a -> S14
S14 -> S14a
S14a -> S15
S15 -> S15a
S15a -> S16
S16 -> S16a
S16a -> S17
S17 -> S17a
S17a -> S18
S18 -> S18a
S18a -> S19
S19 -> S19a
S19a -> S20
S20 -> S20a
S20a -> S21
S21 -> S21a
S21a -> S22
S22 -> S22a
S22a -> S23
S23 -> S23a
S23a -> S24
S24 -> S24a
S24a -> S25
S25 -> S25a
S25a -> S26
S26 -> S26a
S26a -> S27
S27 -> S27a
S27a -> S28
S28 -> S28a
S28a -> S29
S29 -> S29a
S29a -> S30
S30 -> S30a
S30a -> S31
S31 -> S31a
S31a -> S31a