---- MODULE gemini_api ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS MaxTokens, Models

VARIABLES
    request,
    response,
    token_count,
    api_state

\* Request and response structures
Request == [
    model: Models,
    prompt: STRING,
    temperature: 0..100,
    max_tokens: 1..MaxTokens
]

Response == [
    content: STRING,
    prompt_tokens: Nat,
    completion_tokens: Nat,
    total_tokens: Nat,
    finish_reason: {"stop", "max_tokens", "error"}
]

ApiStates == {"ready", "processing", "rate_limited", "error"}

TypeOK ==
    /\ api_state \in ApiStates
    /\ token_count \in 0..MaxTokens
    /\ request \in [model: Models, prompt: STRING, temperature: 0..100, max_tokens: 1..MaxTokens]
    /\ response \in [content: STRING, prompt_tokens: Nat, completion_tokens: Nat, total_tokens: Nat, finish_reason: {"stop", "max_tokens", "error"}]

Init ==
    /\ api_state = "ready"
    /\ token_count = 0
    /\ request = [model |-> CHOOSE m \in Models : TRUE, prompt |-> "", temperature |-> 70, max_tokens |-> 100]
    /\ response = [content |-> "", prompt_tokens |-> 0, completion_tokens |-> 0, total_tokens |-> 0, finish_reason |-> "stop"]

ProcessRequest ==
    /\ api_state = "ready"
    /\ request.prompt # ""
    /\ api_state' = "processing"
    /\ token_count' = Len(request.prompt) \div 4  \* Approximate tokenization
    /\ UNCHANGED <<request, response>>

GenerateResponse ==
    /\ api_state = "processing"
    /\ LET completion_tokens == CHOOSE n \in 1..request.max_tokens : TRUE
       IN /\ response' = [
              content |-> "Generated response",
              prompt_tokens |-> token_count,
              completion_tokens |-> completion_tokens,
              total_tokens |-> token_count + completion_tokens,
              finish_reason |-> IF completion_tokens = request.max_tokens THEN "max_tokens" ELSE "stop"
          ]
    /\ api_state' = "ready"
    /\ UNCHANGED <<request, token_count>>

HandleRateLimit ==
    /\ api_state = "processing"
    /\ api_state' = "rate_limited"
    /\ UNCHANGED <<request, response, token_count>>

Next ==
    \/ ProcessRequest
    \/ GenerateResponse
    \/ HandleRateLimit

Spec == Init /\ [][Next]_<<request, response, token_count, api_state>>

\* Properties
TokenLimit == token_count <= MaxTokens
ResponseCompleteness == response.finish_reason = "stop" => response.content # ""

====