STS: Symbolic Transition System format
========================

This format allows for the definition of a component-based Symbolic Transition System, which is characterized by:

- system variables, divided into ``STATE``, ``INPUT``, ``OUTPUT``, and ``VAR``

- initial states formula, i.e., ``INIT``

- transition relation formula, i.e., ``TRANS``

- invariant formula, i.e., ``INVAR``, which constraints every states of the system, including the initial ones 

The language supports also a typed modules definition and instantiation. A module can be defined using the keyword ``DEF``, followed by a list of parameters, while its instantiation should be defined in the ``VAR`` section.

========================
Example
========================

Simple definition of an 8-bit counter with clock and reset. The lines that starts with ``#`` are comments. 

.. code::

    VAR
    clk: BV(1);
    rst: BV(1);
    
    OUTPUT
    out: BV(8);

    INIT
    out = 0_8;
    clk = 0_1;

    TRANS
    # Clock behavior definition
    (clk = 0_1) <-> (next(clk) = 1_1);
    # When posedge and not reset we increase out by 1
    (posedge(clk) & ! posedge(rst)) -> (next(out) = (out + 1_8));
    # When not posedge and not reset we keep the value of the out
    (! posedge(clk) & ! posedge(rst)) -> (next(out) = (out));
    # When reset we set out to 0
    posedge(rst) -> (next(out) = 0);
    
    
Definition using sub-module instantiation

.. code::

  VAR
    clk: BV(1);
    rst: BV(1);
    counter_1: Counter(clk, rst);
    
  OUTPUT
    out: BV(8);
    
  TRANS
    # Clock behavior definition
    (clk = 0_1) <-> (next(clk) = 1_1);
    
  INVAR
    # Enforcement of the equivalence between local output value and the output of the sub-module
    out = counter_1.out;

  DEF Counter(clk: BV(1), rst: BV(1)):
    VAR
    out: BV(8);

    INIT
    out = 0_8;

    TRANS
    # When posedge and not reset we increase out by 1
    (posedge(clk) & ! posedge(rst)) -> (next(out) = (out + 1_8));
    # When not posedge and not reset we keep the value of the out
    (! posedge(clk) & ! posedge(rst)) -> (next(out) = (out));
    # When reset we set out to 0
    posedge(rst) -> (next(out) = 0);
