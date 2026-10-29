# The `to_dual` Mechanism: A Dumb Translator

You are likely overthinking "Dualization". It is not deep mathematics. It is a **Find-and-Replace Bot**.

Imagine a translator bot that reads a sentence word-by-word.
It has a specific **Dictionary** of words it knows how to flip.
If a word is **NOT** in the dictionary, it just copies it exactly as is.

## 1. The Dictionary (The Attributes)
When we run `attribute [to_dual ...]`, we are adding entries to the bot's dictionary.

| Word (Input) | The Bot's Action (Output) | Why? |
| :--- | :--- | :--- |
| `Quiver.Hom` | **Swap inputs #3 and #4** | We added `attribute [to_dual ...]` |
| `Mono` | **Replace with `Epi`** | We added `attribute [to_dual Epi]` |
| `True` | *(Not in Dictionary)* | **Keep as `True`** |
| `trivial` | *(Not in Dictionary)* | **Keep as `trivial`** |
| `And` | *(Not in Dictionary)* | **Keep as `And`** |

## 2. The Execution (The Theorem)
Now let's run the bot on your theorem.

**Input Code:**
```lean
theorem long_arrow {a b : V} (f : a ⟶ b) : True := trivial
```

The Bot reads this line by line, symbol by symbol.

### Step-by-Step Translation

1.  **Symbol:** `theorem`
    *   **Action:** Not in dictionary. **Copy it.**
2.  **Symbol:** `long_arrow`
    *   **Action:** You told me to name the output `long_arrow_op`. **Rename it.**
3.  **Symbol:** `{a b : V}`
    *   **Action:** `V` is a variable. **Keep it.**
    *   *(Subtle Note: It implicitly knows `V` is now in the Opposite Category)*
4.  **Symbol:** `f : a ⟶ b` (This is `Quiver.Hom a b`)
    *   **Action:** `Quiver.Hom` IS in the dictionary!
    *   **Instruction:** "Use `Quiver.Hom` but SWAP args 3 (`a`) and 4 (`b`)."
    *   **Result:** `f : b ⟶ a`
5.  **Symbol:** `True`
    *   **Action:** IS `True` in the dictionary? **NO.**
    *   **Result:** **Keep `True`**.
6.  **Symbol:** `:=`
    *   **Action:** Syntax. **Copy it.**
7.  **Symbol:** `trivial`
    *   **Action:** IS `trivial` in the dictionary? **NO.**
    *   **Result:** **Keep `trivial`**.

## 3. The Output
The bot stitches the result together:

```lean
pred long_arrow_op {a b : V} (f : b ⟶ a) : True := trivial
```

## Why this is confusing
Mathematical Dualization is a deep concept ("Truth in C is Truth in C_opp").
But Lean's `to_dual` is a **shallow tool**.

It relies on the fact that most logical constants (`True`, `False`, `And`, `Or`, `Forall`, `Exists`) happen to be "Self-Dual" (meaning they mean the same thing in the opposite category).
Because they are self-dual, we **intentionally leave them out of the dictionary**. By failing to translate them, the bot accidentally does the right thing: it leaves them alone.

If `True` behaved differently in the opposite category (e.g. if it became `False`), we would have had to add:
`attribute [to_dual False] True`
But we don't, so the bot ignores it.
