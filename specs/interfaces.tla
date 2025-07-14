---- MODULE interfaces ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Commands, Responses, MaxQueueSize

VARIABLES 
    command_queue,
    response_queue,
    system_state

\* Type definitions
SystemStates == {"init", "ready", "processing", "error"}

TypeOK == 
    /\ command_queue \in Seq(Commands)
    /\ response_queue \in Seq(Responses)
    /\ system_state \in SystemStates
    /\ Len(command_queue) <= MaxQueueSize
    /\ Len(response_queue) <= MaxQueueSize

Init ==
    /\ command_queue = <<>>
    /\ response_queue = <<>>
    /\ system_state = "init"

BecomeReady ==
    /\ system_state = "init"
    /\ system_state' = "ready"
    /\ UNCHANGED <<command_queue, response_queue>>

ProcessCommand ==
    /\ system_state = "ready"
    /\ Len(command_queue) > 0
    /\ system_state' = "processing"
    /\ command_queue' = Tail(command_queue)
    /\ UNCHANGED response_queue

CompleteProcessing ==
    /\ system_state = "processing"
    /\ system_state' = "ready"
    /\ \E resp \in Responses : response_queue' = Append(response_queue, resp)
    /\ UNCHANGED command_queue

HandleError ==
    /\ system_state \in {"processing", "ready"}
    /\ system_state' = "error"
    /\ UNCHANGED <<command_queue, response_queue>>

RecoverFromError ==
    /\ system_state = "error"
    /\ system_state' = "ready"
    /\ UNCHANGED <<command_queue, response_queue>>

Next ==
    \/ BecomeReady
    \/ ProcessCommand
    \/ CompleteProcessing
    \/ HandleError
    \/ RecoverFromError

Spec == Init /\ [][Next]_<<command_queue, response_queue, system_state>>

\* Properties
QueueBounded == 
    /\ Len(command_queue) <= MaxQueueSize
    /\ Len(response_queue) <= MaxQueueSize

EventuallyReady ==
    system_state = "processing" ~> system_state = "ready"

====
