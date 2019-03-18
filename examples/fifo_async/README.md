Verification of Async FIFO implementation obtained from OH! Open Hardware for Chip Designers Project
https://github.com/parallella/oh

For simplicity, the two clocks run at the same frequency, but they're just offset.

The clock behavior DetClock(wr_clk, 1) at line 4 of problem.txt starts wr_clk at zero and then toggles it every step.

The Simple STS file, rd_clk.ssts, starts rd_clk at *1* and toggles it every step.
