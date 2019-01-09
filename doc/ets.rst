ETS: Explicit states Transition System format
========================

This format allows for the definition of an Explicit States Transition System, which is characterized by two sections:

- states definition, expressed as values assignments to system variables, e.g., ``I: clk = 0_1`` for the initial state or ``S1: output = 4_8`` for the state ``S1``, and so on

- transitions definition, e.g., ``I -> S1`` defines a transition from the state ``I`` to the state ``S1``

The language does not require types definition, because it is inferred by the values assignment.

========================
Example
========================

Simple definition of a 2-bit counter. The lines that starts with ``#`` are comments. 

.. code::

    # States definition
    I: output = 0_2
    S1: output = 1_2
    S2: output = 2_2
    S3: output = 3_2
    
    # Transitions
    I -> S1
    S1 -> S2
    S2 -> S3
    S3 -> I
    

========================
Reset procedure example
========================

The ETS format is particularly suited for the definition of sequential behaviors such as the reset procedures. In fact, most hardware definitions require to be properly initialized before performing any analysis.
In the following example, the ``reset_done`` variable is used to keep track of the reset status, and it is used to specify a pre-condition for the verification properties.

.. code::

    I: rst = 0_1
    I: reset_done = False
    
    S1: rst = 1_1
    S1: reset_done = False
    
    S2: rst = 0_1
    S2: reset_done = True
    
    SE: reset_done = True
    
    I -> S1
    S1 -> S2
    S2 -> SE
    # the reset_done signal remains up forever, defined as a self-loop on the SE state
    SE -> SE
