#!/usr/bin/env python3
from cosa.environment import reset_env
from cosa.encoders.formulae import StringParser
from pysmt.shortcuts import Symbol, Array, get_env
from pysmt.typing import BVType, ArrayType

def test_next():
    reset_env()
    arrtype = ArrayType(BVType(3), BVType(4))
    arr = Symbol("arr", arrtype)
    idx = Symbol("idx", BVType(3))
    parser = StringParser()
    [(_, f, _)] = parser.parse_formulae(["next(arr)[idx]"])
    assert (f.args()[1] == idx)

def test_prev():
    reset_env()
    arrtype = ArrayType(BVType(3), BVType(4))
    arr = Symbol("arr", arrtype)
    idx = Symbol("idx", BVType(3))
    parser = StringParser()
    [(_, f, _)] = parser.parse_formulae(["prev(arr)[idx]"])
    assert (f.args()[1] == idx)


if __name__ == "__main__":
    test_next()
    test_prev()
