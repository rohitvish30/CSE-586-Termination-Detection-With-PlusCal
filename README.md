# CSE-586-Termination-Detection-With-PlusCal

There are N processes numbered 1..N connected by channels. A process
can be in one of two possible states: active or idle. Initially all processes are
active, and all channels are empty.
A process that is in the active state can perform the following actions:
1. send a message
2. receive a message, or
3. change state to be idle.
An idle process, on the other hand, can only perform a single action:
receive a message, at which point it becomes active. (A process can read
only its own state and the sequence of messages it sends and receives.)
There is a special detector process, process 0, that aims to detect termination
of the processes 1..N. When a process becomes idle, it sends a
message to the detector. So, when the detector has heard from all processes,
it knows that all processes became idle. However, simply indicating a transition
to idle is not enough. The global state of a distributed system consists
of the states of all processes and communication channels in the system. So
the processes should supply the detector information about the state of the
channels as well.
The detector should declare done when it detects the termination occurred,
i.e., when all processes are idle and there is no message in transit to
any process. The detector should provide these properties:
• safety: invariant.(done =>) computation has terminated)
• progress: computation has terminated -> done
