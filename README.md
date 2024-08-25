# Project Portfolio
This repository is a collection of the individual and collaborative projects I've worked on during my undergraduate and graduate degrees at the University of Florida, as well as projects I've taken on personally to develop my skills and expand my expertise in computer engineering.

# Table of Contents:
### 🔧: Documentation in progress
These links will take you to a summary of each project, which then links to the project pages.
- [The UkeMaster 3000](#the-ukemaster-3000)
- [GatorBreaker](#gatorbreaker)
- [DRAM DMA Interface](#dram-dma-interface)
- [FPGA Pong](#fpga-pong)
- [MIPS Architecture](#mips-architecture)
- [SRAM VLSI Design](#sram-vlsi-design)
- [Logo Classification](#logo-classification)
- [RAID 5 File System from Scratch](#raid-5-file-system-from-scratch)
- [Linux Keyboard Driver](#linux-keyboard-driver)
- [Case Study on Parallel Computing Benchmark LAGHOS](#case-study-on-parallel-computing-benchmark-laghos)
- [AWS IoT Home AC System](#aws-iot-home-ac-system) 🔧
- [Guitar Teaching Tool](#guitar-teaching-tool) 🔧
- [GazdaSolar Estimate Tool](#gazdasolar-estimate-tool) 🔧

# List of Projects:
## **[The UkeMaster 3000:](https://github.com/NikodemGazda/Projects/tree/main/The%20UkeMaster%203000)**
Ukulele robot that plays back any sounds recorded into it on a ukulele. Senior Design project for the Spring of 2023, won first place out of ~30 other projects. This design required extensive hardware programming using VHDL to create a complex system with custom SPI and Solenoid/Servo control modules as well as intricate, fine-tuned timing requirements.

<img src="https://github.com/NikodemGazda/Projects/assets/26459327/91d85d06-5b33-4f11-8b8b-8562115df68e" width="356" height="200">

**Relevant topics: FPGA, VHDL, Signal Processing, Troubleshooting**.

[Back to Top](#table-of-contents)

## **[GatorBreaker:](https://github.com/NikodemGazda/Projects/tree/main/GatorBreaker)**
Game of Breakout programmed from scratch using an RTOS on a TIVA C series LaunchPad. Final project for EEL4745C - MicroProcessor Applications 2, Fall of 2022. Project prompt was to create an interesting project with elements of a real-time operating system.

[<img src="https://github.com/NikodemGazda/Projects/assets/26459327/dab3a0d5-39de-4be7-bc10-43c1410d77d6" width="356" height="200">](https://www.youtube.com/watch?v=1_CdH1m1Uq0 "GatorBreaker")

**Relevant topics: RTOS.**

[Back to Top](#table-of-contents)

## **[DRAM DMA Interface:](https://github.com/NikodemGazda/Project-Portfolio/tree/main/DRAM%20DMA%20Interface)**
Half of the final for Recongifurable Computing, this project is a DRAM DMA interface that streams data to/from external DRAM. The main challenge of interfacing with the DRAMs is dealing with both control and data signals that cross clock domains. This project dealt with RTL Design, plenty of functional verification, time-domain crossing, and metastability.

<img src="https://github.com/user-attachments/assets/1bb55f3c-89c7-4fb4-baee-93378dcee4c1" width="360" height="200">

**Relevant topics: RTL Design, Functional digital verification, time-domain crossing, metastability.**

[Back to Top](#table-of-contents)

## **[FPGA Pong:](https://github.com/NikodemGazda/Project-Portfolio/tree/main/FPGA%20Pong)**
Fully functioning game of pong implemented using a Basys 3 FPGA in both VHDL and Verilog. Initially implemented as pure hardware, eventually evolved to full SoC with hardware, software, and OS. Group project in EEL5934 - System-on-Chip Design.

<img src="https://github.com/NikodemGazda/Project-Portfolio/assets/26459327/e6f79df7-55d0-46a1-95a9-b7a276275207" width="360" height="200">

**Relevant topics: VHDL, SoC Design, Hardware/Software Partitioning**

[Back to Top](#table-of-contents)

## **[MIPS Architecture:](https://github.com/NikodemGazda/Project-Portfolio/tree/main/MIPS%20Architecture)**
Functioning MIPS architecture capable of running programs built on the DE-10 Lite FPGA. This was a final project for EEL4712 - Digital Design. Project includes diagram to explain datapath and FSM.

<img src="https://github.com/NikodemGazda/Project-Portfolio/assets/26459327/93c21f84-c250-4552-83ba-892e93901c30" width="317" height="200">

**Relevant topics: VHDL, Digital Design, FPGA, Computer systems, FSM, Datapath**

[Back to Top](#table-of-contents)

## **[SRAM VLSI Design:](https://github.com/NikodemGazda/Projects/tree/main/SRAM%20VLSI%20Design)**
Functioning transistor-scale design of an SRAM cell. This project was completed as a group for EEE4310 - VLSI Circuits and Technology. Project includes demux logic, 4x2 SRAM, sense amplifier, and read-write logic.

<img src="https://github.com/NikodemGazda/Projects/assets/26459327/a9d88f0d-fa55-40c7-8672-fe2c54f40d5b" width="780" height="200">

**Relevant topics: VLSI/IC Design, SRAM, Digital Circuit Simulation and Verification.**

[Back to Top](#table-of-contents)

## **[Logo Classification:](https://github.com/NikodemGazda/Projects/tree/main/Logo%20Classification%20-%20Machine%20Learning)**
Logo classification machine learning model (using GoogLeNet) used to classify natural images of the logos of 10 different companies. Final project for EEL5840 - Fundamentals of Machine Learning, Spring of 2023.

<img src="https://github.com/NikodemGazda/Projects/assets/26459327/eb4146f0-6f20-45df-a2ba-40a4d897bf94" width="356" height="200">

**Relevant topics: Machine Learning, Neural Networks, Transfer Learning.**

[Back to Top](#table-of-contents)

## **[RAID 5 File System from Scratch:](https://github.com/NikodemGazda/Project-Portfolio/tree/main/RAID%205%20File%20System)**
This final project for EEL4736 Principles of Computer System Design extends a client-server file system built in previous homework assignments to support multiple servers with redundant block storage, implementing RAID-5 for fault tolerance, data integrity, and performance optimization. The system handles corrupt blocks and server disconnections using checksum-based error detection and repair mechanisms, while ensuring load balancing, data parity management, and recovery processes.

<img src="https://github.com/user-attachments/assets/54ec4eaa-1a50-4fbb-b006-77395419b123" width="317" height="200">

**Relevant topics: RAID-5, Fault Tolerance, File Systems, Data Integrity**

[Back to Top](#table-of-contents)

## **[Linux Keyboard Driver:](https://github.com/NikodemGazda/Project-Portfolio/tree/main/Linux%20Keyboard%20Driver)**
For the final project of EEL 5733 Advanced Systems Programming, I created a user space simulator that modeled the usbkbd driver, focusing on I/O communication concurrency and using pipes, threads, and URB completion handlers. The project demonstrated the correct handling of key events and LED statuses through multi-process and multi-threaded architecture.

<img src="https://github.com/user-attachments/assets/752669bc-0fb0-4e25-8c64-240000fdf020" width="317" height="200">

**Relevant topics: Linux drivers, multi-threaded programming, URB completion handlers, USB drivers**

[Back to Top](#table-of-contents)

## **[Case Study on Parallel Computing Benchmark LAGHOS:](https://github.com/NikodemGazda/Project-Portfolio/tree/main/PCA%20Case%20Study)**
This case study was a final project for EEL6763 Parallel Computer Architecture. In this case study, a partner (Jonathan Lijewski) and I were profiling and optimizing the LAGHOS high-order Euler equation solver. This included porting the code to HiPerGator, evaluating performance across MPI, MPI+OpenMP, and CUDA configurations, and refining the code.

<img src="https://github.com/user-attachments/assets/19a251b7-f09c-4124-90b1-5bff2dda3fa0" width="317" height="200">

**Relevant topics: Parallel computing, MPI, OpenMP/OMP, Cuda, profiling, high-performance computing**

[Back to Top](#table-of-contents)

## **[AWS IoT Home AC System:](https://github.com/NikodemGazda/Project-Portfolio/tree/main/AWS%20IoT%20Home%20AC)**
Functioning MIPS architecture capable of running programs built on the DE-10 Lite FPGA. This was a final project for EEL4712 - Digital Design. Project includes diagram to explain datapath and FSM.

<img src="https://github.com/NikodemGazda/Project-Portfolio/assets/26459327/93c21f84-c250-4552-83ba-892e93901c30" width="317" height="200">

**Relevant topics: VHDL, Digital Design, FPGA, Computer systems, FSM, Datapath**

[Back to Top](#table-of-contents)

## **[Guitar Teaching Tool:](https://github.com/NikodemGazda/Project-Portfolio/tree/main/Guitar%20Teaching%20Tool)**
Learned JavaScript to create an app to make it easier to learn the guitar. I honestly use this very often and though the code is less complicated than the other projects listed in this portfolio, it's by far the most useful project and one of the ones I'm most proud of. Pure engineering--I had a problem and I solved it.

<img src="https://github.com/NikodemGazda/Project-Portfolio/assets/26459327/ed002c83-b59b-40c3-89f0-6b64da41b029" width="423" height="200">

**Relevant topics: Javascript, Music :)**

[Back to Top](#table-of-contents)

## **[GazdaSolar Estimate Tool:](https://github.com/NikodemGazda/Project-Portfolio/tree/main/GazdaSolar%20Estimate%20Tool)**
Estimate calculator tool for solar panel installation company GazdaSolar. Challenged to create this calculator with no prior knowledge of website development. Learned tools like PHP, CSS, or HTML to create the beautiful masterpiece you see before you:

<img src="https://github.com/NikodemGazda/Project-Portfolio/assets/26459327/d67fb82c-4444-427f-b9ec-60ecde02dde7" width="347" height="400">

**Relevant topics: PHP, CSS, HTML**

[Back to Top](#table-of-contents)

