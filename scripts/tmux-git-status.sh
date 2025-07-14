#!/bin/bash
# Git status monitor for tmux dashboard

while true; do
    clear
    echo "=== Git Status ==="
    echo
    git status -s
    echo
    echo "=== Recent Commits ==="
    git log --oneline -5
    echo
    echo "=== Current Branch ==="
    git branch --show-current
    sleep 2
done