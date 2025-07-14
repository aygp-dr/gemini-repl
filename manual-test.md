# Manual Test Plan for Conversation Context

## Test 1: Basic Context
1. Start REPL: `gmake run`
2. First prompt: "What is the capital of France?"
3. Second prompt: "What is its population?"
4. Expected: Should understand "its" refers to Paris

## Test 2: Technical Context
1. First prompt: "What are the main package managers on FreeBSD?"
2. Second prompt: "How do I update the first one?"
3. Expected: Should understand "first one" refers to pkg

## Test 3: Context Command
1. Send a few messages
2. Run `/context`
3. Expected: Should show message count

## Test 4: Multi-turn Conversation
1. "Explain recursion"
2. "Give me an example in Python"
3. "Now convert it to JavaScript"
4. Expected: Each response builds on previous context