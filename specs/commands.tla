---- MODULE commands ----
EXTENDS Naturals, Sequences

CONSTANTS SlashCommands, UserInputs

VARIABLES current_command, command_history

TypeOK ==
    /\ current_command \in SlashCommands \cup UserInputs \cup {""}
    /\ command_history \in Seq(SlashCommands \cup UserInputs)

Init ==
    /\ current_command = ""
    /\ command_history = <<>>

ExecuteCommand ==
    /\ current_command # ""
    /\ command_history' = Append(command_history, current_command)
    /\ current_command' = ""

Next == ExecuteCommand

Spec == Init /\ [][Next]_<<current_command, command_history>>

====
