
# The Squash Rule (imax)

Squashing happens if and only if **Logic (Prop)** is the destination.

The rule for the universe level of `A -> B` is called `imax(u, v)`.

## The Rule Table

| Input A (Level u) | Output B (Level v) | Result (A -> B) | Behavior |
| :--- | :--- | :--- | :--- |
| Huge (Type 50) | **Logic (Prop / 0)** | **Prop (0)** | **SQUASHED** |
| Huge (Type 50) | Small (Type 1) | Huge (Type 50) | Balloon (Max) |
| Small (Type 1) | Huge (Type 50) | Huge (Type 50) | Balloon (Max) |

## Simple English Rule

1.  **If the Output is Logic (Prop)**: The result is ALWAYS Logic (Prop). (Squash)
2.  **Otherwise**: The result is the Maximum of Input and Output. (Balloon)

## Why?
Because statements *about* huge things don't need to be huge themselves.
"Does God exist?" is a statement about an Infinite Being, but the answer (True/False) fits in a single bit.
