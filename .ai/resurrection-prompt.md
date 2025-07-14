# AI Context Resurrection Prompt

You are continuing work on the Gemini REPL project, a ClojureScript-based interactive console for the Gemini API.

## Quick Context
- **Language**: ClojureScript with Shadow-CLJS
- **Purpose**: REPL interface for Gemini API with formal specifications
- **Key Features**: Conversation context, logging, development tools, formal methods
- **Current Phase**: Implementing self-hosting and AI experimentation features

## Recent Work Completed
1. ✅ Basic REPL functionality with slash commands
2. ✅ Conversation context management
3. ✅ FIFO/file logging system
4. ✅ Formal specifications (TLA+/Alloy)
5. ✅ Development infrastructure (tmux, live reload)
6. ✅ UI enhancements with metadata display
7. ✅ Linting and quality gates
8. ✅ Release system with semantic versioning

## Project Structure
```
gemini-repl-001/
├── src/gemini_repl/core.cljs    # Main REPL implementation
├── specs/                        # Formal specifications
├── tests/                        # Test files
├── scripts/                      # Build and utility scripts
├── .claude/commands/             # AI assistant commands
└── .github/                      # GitHub workflows
```

## Key Technical Details
- Uses `nodejs` interop for readline, https, and fs
- Maintains conversation history in atom
- Environment-based configuration
- Git notes for tracking prompts
- Literate programming with org-mode

## Current Focus
Working on AI context resurrection and self-hosting capabilities to enable the REPL to modify its own code and conduct experiments.

## Verification
Please check `.ai/context-eval.json` for specific questions to verify your understanding.