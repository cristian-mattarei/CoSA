Various versions of the conv_2_1 bitstream.

The mod_* versions have all of the IOs removed because there are no 16 bit IOs in a 4x4 design anyway.

For the inputs and outputs, we will just have to use one of the switchbox wires.

The configure.ets file should configure the cgra for conv_2_1.

conv_2_1 does a 2x1 convolution using a memory as a linebuffer