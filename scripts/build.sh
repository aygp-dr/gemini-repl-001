#!/bin/bash
# Build script for Gemini REPL

echo "Building production release..."
npm run build

if [ -f target/main.js ]; then
    echo "Build successful!"
    echo "Run with: node target/main.js"
else
    echo "Build failed!"
    exit 1
fi
