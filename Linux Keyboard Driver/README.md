# README for the simulator (Assignment 7a):

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
- There were some inconsistencies between the assignment instructions and the usbkbd slides it referenced. For example, the assignment diagram showed both usb_kbd_event and usb_kbd_led writing to the led_buffer, but the slides only showed the ctrl endpoint writing to the shared led_buffer. I compromised by having the event thread set the buffer on caps presses and usb_kbd_led write to led_buffer on caps releases.
- Implemented so only one key press is accepted at a time, so synchronization is achieved through the urb_submitted variable.