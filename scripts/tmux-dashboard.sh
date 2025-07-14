#!/bin/bash
# Tmux Development Dashboard for Gemini REPL

SESSION_NAME="gemini-repl-dev"
PROJECT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

# Kill existing session if it exists
tmux kill-session -t $SESSION_NAME 2>/dev/null

# Create new session with main REPL pane
tmux new-session -d -s $SESSION_NAME -n "Dashboard" -c "$PROJECT_DIR"

# Configure status bar
tmux set-option -t $SESSION_NAME status-bg colour235
tmux set-option -t $SESSION_NAME status-fg colour136
tmux set-option -t $SESSION_NAME status-left '#[fg=colour235,bg=colour252,bold] GEMINI REPL #[fg=colour252,bg=colour238,nobold]#[fg=colour245,bg=colour238,bold] #S #[fg=colour238,bg=colour234,nobold]'
tmux set-option -t $SESSION_NAME status-right '#[fg=colour235,bg=colour252] %H:%M %d-%b-%y '

# Create layout - 6 panes
# +-------------------+-------------------+
# |                   |                   |
# |   1. Main REPL    |  2. Build Output  |
# |                   |                   |
# +-------------------+-------------------+
# | 3. Log Monitor    | 4. Git Status     |
# +-------------------+-------------------+
# | 5. System Monitor | 6. Test Runner    |
# +-------------------+-------------------+

# Split horizontally for top row
tmux split-window -t $SESSION_NAME:0.0 -h -p 50

# Split the left pane horizontally twice
tmux split-window -t $SESSION_NAME:0.0 -v -p 66
tmux split-window -t $SESSION_NAME:0.2 -v -p 50

# Split the right pane horizontally twice  
tmux split-window -t $SESSION_NAME:0.1 -v -p 66
tmux split-window -t $SESSION_NAME:0.4 -v -p 50

# Pane 0: Main REPL
tmux send-keys -t $SESSION_NAME:0.0 "echo 'Main REPL - Run: make run'" C-m

# Pane 1: Build Output
tmux send-keys -t $SESSION_NAME:0.1 "echo 'Build Output - Run: npm run dev'" C-m

# Pane 2: Log Monitor
tmux send-keys -t $SESSION_NAME:0.2 "echo 'Log Monitor - Starting...'" C-m
tmux send-keys -t $SESSION_NAME:0.2 "node scripts/test-logging.js" C-m

# Pane 3: Git Status
tmux send-keys -t $SESSION_NAME:0.3 "watch -n 2 'git status -s && echo && git log --oneline -5'" C-m

# Pane 4: System Monitor
cat > "$PROJECT_DIR/scripts/tmux-monitor.sh" << 'EOF'
#!/bin/bash
while true; do
    clear
    echo "=== System Monitor ==="
    echo
    echo "CPU Usage:"
    top -l 1 | grep "CPU usage" | head -1 || echo "  N/A"
    echo
    echo "Memory:"
    vm_stat | grep -E "(free|active|inactive|wired)" | head -4 || echo "  N/A"
    echo
    echo "Disk:"
    df -h . | tail -1
    echo
    echo "Node Processes:"
    ps aux | grep -E "node|shadow-cljs" | grep -v grep | wc -l | xargs echo "  Count:"
    sleep 5
done
EOF
chmod +x "$PROJECT_DIR/scripts/tmux-monitor.sh"
tmux send-keys -t $SESSION_NAME:0.4 "./scripts/tmux-monitor.sh" C-m

# Pane 5: Test Runner
tmux send-keys -t $SESSION_NAME:0.5 "echo 'Test Runner - Run: make test'" C-m

# Select the main REPL pane
tmux select-pane -t $SESSION_NAME:0.0

# Attach to session
if [ -z "$TMUX" ]; then
    tmux attach-session -t $SESSION_NAME
else
    tmux switch-client -t $SESSION_NAME
fi