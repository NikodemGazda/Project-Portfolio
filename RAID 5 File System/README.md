# RAID 5 File System
This project implemented a RAID-5 fault-tolerant file system built across multiple servers, capable of distributing data and parity blocks, managing block errors, and recovering from server failures. Key objectives were improving load distribution, increasing aggregate capacity, and enhancing fault tolerance.

- Implemented RAID-5 functionality to tolerate single server failures in systems with up to N=8 servers.
- Handled two failure types: corrupted blocks and disconnected servers, using checksums for error detection and data recovery.
- Supported block caching for efficient access, with optional cache logging enabled via command-line arguments.
- Designed a simple repair process to regenerate lost data when a failed server was replaced.
- This project built on previous homework assignments in EEL4736 Principles of Computer System Design.

## More Information
For more information on the project scope and instructions, see the [project instructions](https://github.com/NikodemGazda/Project-Portfolio/blob/main/RAID%205%20File%20System/project_instructions.txt). For more information on the implementation, see the [project report](https://github.com/NikodemGazda/Project-Portfolio/blob/main/RAID%205%20File%20System/project_report.pdf). To take a look at the code, see the [code](https://github.com/NikodemGazda/Project-Portfolio/blob/main/RAID%205%20File%20System/code.zip).
