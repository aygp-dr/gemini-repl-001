#!/usr/bin/env node
// Test script to verify FIFO logging works

const fs = require('fs');
const { spawn } = require('child_process');

const fifoPath = '/tmp/gemini-repl.fifo';

// Create FIFO if it doesn't exist
try {
  fs.unlinkSync(fifoPath);
} catch (e) {
  // Ignore if doesn't exist
}

console.log('Creating FIFO...');
const mkfifo = spawn('mkfifo', [fifoPath]);

mkfifo.on('close', (code) => {
  if (code !== 0 && code !== null) {
    console.error('Failed to create FIFO');
    process.exit(1);
  }

  console.log('FIFO created. Starting log reader...');
  
  // Start reading from FIFO
  const stream = fs.createReadStream(fifoPath, { encoding: 'utf8' });
  
  stream.on('data', (data) => {
    const lines = data.trim().split('\n');
    lines.forEach(line => {
      try {
        const log = JSON.parse(line);
        console.log(`[${log.timestamp}] ${log.event}:`, log.data);
      } catch (e) {
        console.log('Raw log:', line);
      }
    });
  });

  stream.on('error', (err) => {
    console.error('Error reading FIFO:', err.message);
  });

  console.log('Monitoring logs at', fifoPath);
  console.log('Run the REPL in another terminal with:');
  console.log('  GEMINI_LOG_ENABLED=true GEMINI_LOG_TYPE=fifo make run');
});