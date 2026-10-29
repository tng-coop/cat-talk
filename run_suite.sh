#!/bin/bash
echo "Launching Incompleteness Theorem Visualization Suite..."
echo ""
echo "Stage 1: The Arithmetic Compiler (Symbols -> Numbers)"
xdot stage1_encoding.dot &

echo "Stage 2: The Proof Machine (Thinking -> Division)"
xdot stage2_proof_machine.dot &

echo "Stage 3: The Substitution Tool (Logic Splicing)"
xdot stage3_substitution.dot &

echo "Stage 4: The Diagonal Trap (Self-Reference)"
xdot stage4_diagonalization.dot &

echo "Stage 5: The Collapse (Truth vs Provability)"
xdot stage5_contradiction.dot &

echo ""
echo "All stages launched in separate windows."
