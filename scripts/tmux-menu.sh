#!/bin/bash
# Interactive menu for tmux dashboard

echo "=== Gemini REPL Dashboard ==="
echo
echo "Quick Commands:"
echo "  1. Run REPL (make run)"
echo "  2. Run Tests (make test)"
echo "  3. Build Project (make build)"
echo "  4. Start Dev Mode (make dev)"
echo "  5. Check Linting (make lint)"
echo "  6. Verify Specs (make verify)"
echo "  7. View Logs (tail -f logs/gemini-repl.log)"
echo "  8. Exit Menu"
echo
read -p "Select option (1-8): " choice

case $choice in
    1) make run ;;
    2) make test ;;
    3) make build ;;
    4) make dev ;;
    5) make lint ;;
    6) make verify ;;
    7) tail -f logs/gemini-repl.log ;;
    8) exit ;;
    *) echo "Invalid option" ;;
esac