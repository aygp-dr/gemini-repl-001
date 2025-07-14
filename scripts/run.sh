#!/bin/bash
# Run the Gemini REPL

if [ ! -f target/main.js ]; then
    echo "Building first..."
    npm run build
fi

if [ -z "$GEMINI_API_KEY" ]; then
    echo "Error: GEMINI_API_KEY environment variable is required"
    exit 1
fi

node target/main.js
