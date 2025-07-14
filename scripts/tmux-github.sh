#!/bin/bash
# GitHub status monitor for tmux dashboard

while true; do
    clear
    echo "=== GitHub Issues ==="
    gh issue list --limit 5
    echo
    echo "=== Pull Requests ==="
    gh pr list --limit 5
    echo
    echo "=== Workflow Status ==="
    gh run list --limit 3
    sleep 30
done