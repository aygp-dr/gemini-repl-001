---- MODULE commands ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS SlashCommands, UserInputs

VARIABLES current_command, command_history

\* Define command types
AllCommands == SlashCommands \cup UserInputs

TypeOK ==
    /\ current_command \in AllCommands \cup {""}
    /\ command_history \in Seq(AllCommands)

Init ==
    /\ current_command = ""
    /\ command_history = <<>>

ExecuteCommand ==
    /\ current_command # ""
    /\ command_history' = Append(command_history, current_command)
    /\ current_command' = ""

ReceiveInput(cmd) ==
    /\ current_command = ""
    /\ cmd \in AllCommands
    /\ current_command' = cmd
    /\ UNCHANGED command_history

Next == 
    \/ ExecuteCommand
    \/ \E cmd \in AllCommands : ReceiveInput(cmd)

Spec == Init /\ [][Next]_<<current_command, command_history>>

\* Properties
HistoryGrowsMonotonically == 
    [][Len(command_history') >= Len(command_history)]_command_history

====
