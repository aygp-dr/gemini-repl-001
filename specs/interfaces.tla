---- MODULE interfaces ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Commands, Responses

VARIABLES 
    command_queue,
    response_queue,
    system_state

TypeOK == 
    /\ command_queue \in Seq(Commands)
    /\ response_queue \in Seq(Responses)
    /\ system_state \in {"init", "ready", "processing", "error"}

Init ==
    /\ command_queue = <<>>
    /\ response_queue = <<>>
    /\ system_state = "init"

ProcessCommand ==
    /\ system_state = "ready"
    /\ Len(command_queue) > 0
    /\ system_state' = "processing"
    /\ command_queue' = Tail(command_queue)
    /\ UNCHANGED response_queue

Next ==
    \/ ProcessCommand
    \/ system_state' = system_state /\ UNCHANGED <<command_queue, response_queue>>

Spec == Init /\ [][Next]_<<command_queue, response_queue, system_state>>

====
