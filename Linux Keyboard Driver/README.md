# Linux Keyboard Driver
Below is the documentation for the final project for EEL 5733 Advanced Systems Programming which involves implementing a user-space simulator for the usbkbd driver. The simulator closely models the callbacks and concurrency aspects of the original driver, including URB completion handlers and input subsystem callbacks. The goal is to ensure accurate simulation of keyboard events and LED status using multi-process and multi-threaded architecture.

For the code, see the [code](https://github.com/NikodemGazda/Project-Portfolio/blob/main/Linux%20Keyboard%20Driver/code.zip). For more on the project scope, see the [project instructions](https://github.com/NikodemGazda/Project-Portfolio/blob/main/Linux%20Keyboard%20Driver/project_instructions.pdf). For more information on the implementation, see below.

## Build:
- make (Makefile uses g++ compiler, run using WSL on Ubuntu 22.04.4 LTS)

## Run:
- ./sim < input.txt

## Functionality:
### Main
- In main, we start by initializing the led_buffer with mmap and the 3 pipes we use.
- We then fork to start the driver process, in which the child calls the open function and then waits to join the usb_core threads. The parent moves onto fork again for the keyboard process.
- The keyboard process' child creates the two endpoint threads and then waits for them to join. The main process then waits for the other processes to end and, unmaps the led_buffer, and frees the device.
### Driver
- usb_kbd_open() initializes the values for the device and runs usb_submit_urb() for the first time.
- usb_submit_urb() creates the usb_core endpoints on first call. Other calls of this function for caps key presses and other normal presses signal for the urb to be submitted.
- the usb_core_int() polls the key interrupt presses from the device and starts the irq completion handler. If the caps flag is activated, it stores the captured input with caps in mind.
- usb_core_ctrl() waits for the urb submitted flag, and once it is, writes a command to the ctrl endpoint in the device. It also accepts the ACK from the ctrl endpoint and creates the usb_kbd_led() thread.
- usb_kbd_led() writes to led_buffer.
- usb_kbd_irq() checks what kinda key press it is and calls input_report_key() and usb_submit_urb with the key press information.
- input_report_key() records the caps press into kbd_dev.dev->led and sets off usb_kbd_event() if CAPS. If not, it writes the key press to stdout.
- usb_kbd_event() writes to led_buffer.
### Device/Keyboard
- usb_kbd_int() is the endpoint thread that sends data to the driver via pipe. It waits till the ctrl endpoint ACKs each send before sending the next char.
- usb_kbd_ctrl() is the ctrl endpoint thread. It polls the command pipe and reads from led_buffer/ACKs accordingly. Sets a flag once ACK sends. Once the simulation finishes, it prints the CAPS toggle information.

## Assumptions:
- The event thread sets the buffer on caps presses and usb_kbd_led writes to led_buffer on caps releases.
- Implemented so only one key press is accepted at a time, so synchronization is achieved through the urb_submitted variable.
