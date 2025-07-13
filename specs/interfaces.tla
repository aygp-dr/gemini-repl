---------------------------- MODULE interfaces ----------------------------
EXTENDS Sequences, TLC, Naturals

CONSTANTS Commands, Prompts, APIKey, STRING

VARIABLES 
    inputBuffer,
    commandQueue,
    apiQueue,
    outputBuffer,
    sessionState

Init == 
    /\ inputBuffer = <<>>
    /\ commandQueue = <<>>
    /\ apiQueue = <<>>
    /\ outputBuffer = <<>>
    /\ sessionState = [
           authenticated |-> FALSE,
           model |-> "gemini-2.0-flash",
           temperature |-> 0,  \* Using integer instead of real
           maxTokens |-> 2048
       ]

\* Input Handler Interface
ParseInput(input) ==
    IF input[1] = "/" 
    THEN [type |-> "command", value |-> input]
    ELSE [type |-> "prompt", value |-> input]

\* Command Parser Interface
IsValidCommand(cmd) ==
    cmd \in Commands

\* API Client Interface
CreateAPIRequest(prompt) ==
    [
        contents |-> <<[parts |-> <<[text |-> prompt]>>]>>,
        config |-> [
            temperature |-> sessionState.temperature,
            maxTokens |-> sessionState.maxTokens
        ]
    ]

\* Type Invariants
TypeInvariant ==
    /\ inputBuffer \in Seq(STRING)
    /\ commandQueue \in Seq([type: {"command"}, value: STRING])
    /\ outputBuffer \in Seq(STRING)
    \* Note: apiQueue type checking simplified for now

=============================================================================
