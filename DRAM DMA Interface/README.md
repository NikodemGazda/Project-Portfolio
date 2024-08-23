# DRAM DMA Interface

This project report implements a DRAM DMA interface module, which handles DMA reads by generating addresses, synchronizing signals, and managing a FIFO buffer. The module consists of five main components: an address generator, size logic, a done counter, a FIFO, and synchronization blocks for clock domain crossing. Despite occasional issues, particularly with boundary cases and stall signals, the design functions as intended, passing several test cases in simulation and on hardware.

- This was a group project I collaborated on with Alexander Huynh in EEL5721 Reconfigurable Computing (Fall 2023).
- My portion was the DRAM DMA interface and he worked on the convolution operation.
- My contributions begin on page 4 of the [report](https://github.com/NikodemGazda/Project-Portfolio/blob/main/DRAM%20DMA%20Interface/report.pdf) in the **DMA Read**.
- The scope and description of the project can be found in the [project outline](https://github.com/NikodemGazda/Project-Portfolio/blob/main/DRAM%20DMA%20Interface/project_outline.pdf). I was mainly responsible for parts 1 and 3.
- My portion of the code can be found in the uploaded [zip file](https://github.com/NikodemGazda/Project-Portfolio/blob/main/DRAM%20DMA%20Interface/code.zip). Including the entire code base wouldn't fit on Github, so in this zip are the VHDL files that were manually created.
