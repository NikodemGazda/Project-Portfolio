# FPGA Pong

This project involves the implementation of a Pong game using FPGA hardware and software in collaboration with partners Brian Lien and Lucas Mueller. The project explores two distinct implementations of the classic Pong game, one solely using VHDL for hardware design and another combining hardware and software using a MicroBlaze processor.

## Hardware-Only Implementation

### Overview
The hardware-only implementation of Pong uses VHDL to design all components required to play the game. This includes a VGA controller, a game controller, and an image generator. The top-level VHDL file, `Pong_Game.vhd`, integrates these components and interfaces with the FPGA board I/O.

### Components
- **Game Controller (`gamecontroller.vhd`)**: Manages the game logic, including the movement of the ball and paddles, collision detection, and scorekeeping. It uses a state machine to update game states and process button inputs.
- **Image Generator (`image_generator.vhd`)**: Draws game elements on the screen by converting their positions into RGB values based on predefined boundaries.
- **VGA Controller (`vga_controller.v`)**: Synchronizes the VGA display output. The controller was sourced from David J. Marion’s repository due to issues with the initial controller provided.

### Challenges and Lessons
The team faced challenges with Vivado for the first time, particularly in configuring the VGA controller. Debugging these issues provided a deeper understanding of VHDL and Vivado's design environment.

## Hardware-Software Implementation

### Overview
The hardware-software implementation integrates hardware components with a software-based game controller running on a MicroBlaze processor. This approach uses a mix of VHDL for hardware and C for software components.

### Components
- **Game Controller**: Implemented in C, running on the MicroBlaze processor. It calculates the ball and paddle movements based on GPIO inputs and updates the game state.
- **GPIO Module**: Captures paddle movement inputs and sends them to the MicroBlaze via the AXI bus.
- **Image Generator & VGA Controller**: Handle the graphical output, converting game state data into visual display signals for the monitor.

### Challenges and Lessons
The main challenges involved integration issues between Vivado and Vitis, particularly with Makefile generation and clocking logic conflicts. The team learned how to create and export IPs using Vivado and further deepened their understanding of the AXI bus protocols. This project showcased our ability to handle both hardware-only and hardware-software integrated designs, highlighting their proficiency in VHDL, system integration, and debugging complex issues with FPGA design tools. For a detailed description, refer to the documentation in this repository.

## Video Demo:

[![Watch the video](https://img.youtube.com/vi/xeyRFYQphgc/maxresdefault.jpg)](https://youtu.be/xeyRFYQphgc)
