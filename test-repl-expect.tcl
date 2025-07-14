#!/usr/bin/env tclsh
# Basic test for REPL using Tcl

package require Expect

# Set timeout
set timeout 5

# Test if we can spawn the REPL
if {[catch {spawn node target/main.js} msg]} {
    puts "Error spawning REPL: $msg"
    exit 1
}

# Wait for banner
expect {
    "GEMINI REPL" {
        puts "✓ REPL started successfully"
    }
    timeout {
        puts "✗ Failed to start REPL"
        exit 1
    }
}

# Send exit command
send "/exit\r"
expect {
    "Goodbye!" {
        puts "✓ Exit command successful"
    }
    timeout {
        puts "✗ Exit command failed"
        exit 1
    }
}

expect eof
puts "✓ Basic test passed"