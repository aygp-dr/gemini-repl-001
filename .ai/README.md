# AI Context Resurrection System

This directory contains files for preserving and restoring AI assistant context across sessions.

## Purpose

When working with AI assistants on long development sessions, context is lost when conversations end or new chat windows are started. This system provides a structured way to:

1. Capture current development context
2. Create quick resurrection prompts
3. Verify AI understanding
4. Document session history

## Files

### resurrection-prompt.md
Quick bootstrap prompt for new AI sessions. Contains:
- Project overview
- Recent work completed
- Current focus
- Key technical details

**Usage**: Copy and paste at the start of a new session.

### context-eval.json
Verification questions to ensure AI has properly absorbed context. Contains:
- 10 questions covering different aspects
- Expected answers
- Passing score threshold (8/10)

**Usage**: Ask AI to answer questions and verify understanding.

### context.org
Comprehensive session documentation in org-mode format. Contains:
- Full project history
- Technical decisions
- Development patterns
- Lessons learned

**Usage**: Reference for detailed context or onboarding.

### session-snapshot.json
Machine-readable session state. Contains:
- Metrics and statistics
- Current phase status
- Technical state
- Key decisions

**Usage**: Programmatic context restoration or analysis.

## Resurrection Process

1. **Start New Session**
   ```
   Copy contents of resurrection-prompt.md
   ```

2. **Verify Understanding**
   ```
   Ask AI to review context-eval.json questions
   Ensure 8/10 correct answers
   ```

3. **Deep Context (if needed)**
   ```
   Reference context.org for specific details
   Check session-snapshot.json for metrics
   ```

4. **Continue Development**
   ```
   AI should now have sufficient context
   Update these files periodically
   ```

## Maintenance

- Update after major milestones
- Refresh metrics in session-snapshot.json
- Add new verification questions as needed
- Keep resurrection prompt concise

## Integration

This system integrates with:
- Git notes for prompt tracking
- GEMINI-REPL-PROMPTS.org for phase guidance
- GitHub issues for feature tracking
- Development workflow documentation