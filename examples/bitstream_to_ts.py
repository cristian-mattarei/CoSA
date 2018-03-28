
import sys

abstract_clock = False

with open(sys.argv[1], "r") as f:
    out = []
    trans = []
    
    out.append("# INIT")
    out.append("I: self.config_addr = 00000000")
    out.append("I: self.config_data = 00000000")
    out.append("I: self.tile_id = 0015")
    out.append("I: self.reset = 1_1")
    out.append("I: conf_done = 0_1")

    out.append("\n# STATES")
    stateid = 0

    trans.append("I -> S%s_p"%stateid)
        
    for line in f.readlines():
        addr = line.strip().split()[0]
        data = line.strip().split()[1]

        out.append("S%s_p: self.config_addr = %s"%(stateid, addr))
        out.append("S%s_p: self.config_data = %s"%(stateid, data))
        out.append("S%s_p: self.tile_id = 0015"%(stateid))
        out.append("S%s_p: self.reset = 0_1"%(stateid))
        out.append("S%s_p: conf_done = 0_1"%(stateid))
        out.append("")

        if not abstract_clock:
            out.append("S%s_n: self.config_addr = %s"%(stateid, addr))
            out.append("S%s_n: self.config_data = %s"%(stateid, data))
            out.append("S%s_n: self.tile_id = 0015"%(stateid))
            out.append("S%s_n: self.reset = 0_1"%(stateid))
            out.append("S%s_n: conf_done = 0_1"%(stateid))
            out.append("")

            trans.append("S%s_p -> S%s_n"%(stateid, stateid))
            trans.append("S%s_n -> S%s_p"%(stateid, stateid+1))
        else:
            trans.append("S%s_p -> S%s_p"%(stateid, stateid+1))
            
        stateid += 1
        
    out.append("S%s_p: self.config_addr = 00000000"%(stateid))
    out.append("S%s_p: self.config_data = 00000000"%(stateid))
    out.append("S%s_p: self.tile_id = 0015"%(stateid))
    out.append("S%s_p: self.reset = 0_1"%(stateid))
    out.append("S%s_p: conf_done = 1_1"%(stateid))

    trans.append("S%s_p -> S%s_p"%(stateid, stateid))
    
    out.append("\n# TRANSITIONS")
    out.append("\n".join(trans))

    print("\n".join(out))
    
