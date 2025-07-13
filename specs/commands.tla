---------------------------- MODULE commands ----------------------------
EXTENDS Sequences, TLC

CONSTANTS 
    SLASH_COMMANDS,  \* Set of valid slash commands
    MAX_ARGS         \* Maximum number of arguments

VARIABLES
    commandHistory,
    currentCommand,
    executionState

\* Command structure
Command == [
    name: SLASH_COMMANDS,
    args: Seq(STRING),
    timestamp: Nat
]

\* Core commands definition
CoreCommands == {
    "/help", "/exit", "/quit", "/clear", 
    "/history", "/save", "/load", "/model",
    "/config", "/retry"
}

\* Advanced commands definition  
AdvancedCommands == {
    "/system", "/temperature", "/max-tokens",
    "/stream", "/debug"
}

Init ==
    /\ commandHistory = <<>>
    /\ currentCommand = [name |-> "/help", args |-> <<>>, timestamp |-> 0]
    /\ executionState = "idle"

\* Parse command from input string
ParseCommand(input) ==
    LET parts == SplitString(input, " ")
    IN [
        name |-> Head(parts),
        args |-> Tail(parts),
        timestamp |-> Now()
    ]

\* Validate command
IsValidCommand(cmd) ==
    /\ cmd.name \in SLASH_COMMANDS
    /\ Len(cmd.args) <= MAX_ARGS
    /\ ValidateArgs(cmd.name, cmd.args)

\* Command execution states
ExecuteCommand(cmd) ==
    /\ executionState' = "executing"
    /\ currentCommand' = cmd
    /\ commandHistory' = Append(commandHistory, cmd)

\* Safety property: No invalid commands executed
SafetyInvariant ==
    \A cmd \in Range(commandHistory): IsValidCommand(cmd)

=============================================================================
