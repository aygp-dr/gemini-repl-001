#!/bin/bash
# Script to manage pull requests

set -e

case "$1" in
  "list")
    gh pr list
    ;;
  "create")
    gh pr create --title "$2" --body "$3"
    ;;
  "merge")
    gh pr merge "$2" --squash --delete-branch
    ;;
  "close")
    gh pr close "$2"
    ;;
  *)
    echo "Usage: $0 {list|create|merge|close} [args]"
    exit 1
    ;;
esac
