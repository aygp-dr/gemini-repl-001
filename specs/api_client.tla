---- MODULE api_client ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS MaxRetries, TimeoutDuration

VARIABLES 
    request_state,
    retry_count,
    response_buffer,
    connection_status

RequestStates == {"idle", "sending", "waiting", "received", "error", "timeout"}
ConnectionStates == {"disconnected", "connecting", "connected", "failed"}

TypeOK ==
    /\ request_state \in RequestStates
    /\ retry_count \in 0..MaxRetries
    /\ response_buffer \in Seq(STRING)
    /\ connection_status \in ConnectionStates

Init ==
    /\ request_state = "idle"
    /\ retry_count = 0
    /\ response_buffer = <<>>
    /\ connection_status = "disconnected"

Connect ==
    /\ connection_status = "disconnected"
    /\ connection_status' = "connecting"
    /\ UNCHANGED <<request_state, retry_count, response_buffer>>

SendRequest ==
    /\ request_state = "idle"
    /\ connection_status = "connected"
    /\ request_state' = "sending"
    /\ UNCHANGED <<retry_count, response_buffer, connection_status>>

ReceiveResponse ==
    /\ request_state = "waiting"
    /\ request_state' = "received"
    /\ response_buffer' = Append(response_buffer, "response_data")
    /\ UNCHANGED <<retry_count, connection_status>>

HandleError ==
    /\ request_state \in {"sending", "waiting"}
    /\ retry_count < MaxRetries
    /\ request_state' = "error"
    /\ retry_count' = retry_count + 1
    /\ UNCHANGED <<response_buffer, connection_status>>

Next ==
    \/ Connect
    \/ SendRequest
    \/ ReceiveResponse
    \/ HandleError

Spec == Init /\ [][Next]_<<request_state, retry_count, response_buffer, connection_status>>

\* Safety properties
NoExcessiveRetries == retry_count <= MaxRetries
ValidStateTransitions == request_state = "received" => Len(response_buffer) > 0

====