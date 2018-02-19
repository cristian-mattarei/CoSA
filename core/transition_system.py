
from pysmt.shortcuts import Symbol, And

NEXT = "_N"

class TS(object):

    vars = None
    init = None
    trans = None
    invar = None
    
    comment = None
    
    def __init__(self, vars, init, trans, invar):
        self.vars = vars
        self.init = init
        self.trans = trans
        self.invar = invar

        self.comment = None

    def inline_invar(self):
        if self.invar is not None:
            self.trans = And([self.trans, self.invar, TS.to_next(self.invar)])

        self.invar = None

    @staticmethod
    def get_prime(v):
        return Symbol(("%s"+NEXT) % v.symbol_name(), v.symbol_type())

    @staticmethod
    def to_next(formula):
        varmap = dict([(v,TS.get_prime(v)) for v in formula.get_free_variables()])
        return formula.substitute(varmap)
