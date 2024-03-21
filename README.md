# SynthLLM
### Getting started:

- Install the [Verified Software Toolchain
(VST)](https://vst.cs.princeton.edu/). The [coq
platform](https://github.com/coq/platform/) is the preferred
mechanism, VST is included in the optional packages.

- Download and make the [Verifiable
C](https://softwarefoundations.cis.upenn.edu/vc-current/index.html)
Volume of Software Foundations.

- Update the \_CoqProject file to point to the location of VC on your
machine.

- Compile any C-files you want to verify, e.g. `clightgen -normalize swap.c`

- Step through Verif_swap.v

- Results on LLMs (MBP benchmark): https://docs.google.com/document/d/1BxwtcKKPPoRXTg82FNXsqUh1dizimIYenwPCrFgU_Ds/edit?usp=sharing
- Results on LLMs (SUSLik benchmark): https://docs.google.com/document/d/15V879SO9ZkKpROnPafEMCnP3nvfJLELFWBjAmNOcwRc/edit?usp=sharing
