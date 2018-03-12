
Files:
- mul_2_pe.json: PE tile, configured to compute a multiplication by 2
- mul_2.json: Simple multiplication by 2
- mul_2_pe-passes.json: mul_2_pe.json after running "removeconstduplicates,deletedeadinstances,removeunconnected,fold-constants,cullzexts,cullgraph" passes
- mul_2b.json: Faulty moltiplication by 2 (it adds the 7th bit to the output)
