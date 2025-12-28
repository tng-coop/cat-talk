# What is a Sigma Type ($\Sigma$)?

A **Sigma Type** (or **Dependent Sum Type**) is the Type Theory version of a "Generalized Pair" or "Tuple".

It is written $\sum_{(x:A)} B(x)$ and consists of pairs $(a, b)$ where:
1.  The first element $a$ is a value of type $A$.
2.  The second element $b$ is a value of type $B(a)$ — crucial: the *type* of the second part depends on the *value* of the first part.

## 1. The Simple Analogy: "The Dynamic Form"

Imagine a web form with two fields:
*   **Field 1:** "Choose your Country" (Type: String)
*   **Field 2:** "Enter your Province/State" (Type: List of Strings... *but which list?*)

The valid options for Field 2 **depend** on what you typed in Field 1.
*   If Field 1 = "USA", Field 2 must be from `["NY", "CA", ...]`.
*   If Field 1 = "Japan", Field 2 must be from `["Tokyo", "Osaka", ...]`.

This pair `(Country, Province)` is a **Sigma Type**. You cannot define the type of "Province" without first knowing the "Country".

## 2. In Logic: "Existential Quantification" ($\exists$)

In the "Propositions as Types" correspondence:
*   **Sigma Types correspond to "There Exists" ($\exists$).**

To prove "There exists an even number" ($\exists n, \text{Even}(n)$), you must provide a **Witness Pair**:
$$ (4, \text{proof\_that\_4\_is\_even}) $$

*   The first part ($4$) is the witness.
*   The second part is the proof *about* that witness.

## 3. In Your Code (`structure`)

Your `IsProduct` structure is exactly this:

```lean
structure IsProduct (A B : Obj) where
  P : Obj              -- 1. The Witness (The Object)
  lift : ...           -- 2. The Proofs (Dependent on P)
  laws : ...           -- 3. More Proofs (Dependent on P and lift)
```

This is a cascading Sigma Type:
$$ \sum_{P \in \text{Obj}} \left( \sum_{\pi_1, \pi_2} \text{UniversalProperty}(P, \pi_1, \pi_2) \right) $$

It says: "I am a package containing an object $P$, AND the data showing that *this specific P* works."

## Summary
| Name | Notation | Meaning | Code Eqivalent |
| :--- | :--- | :--- | :--- |
| **Product Type** | $A \times B$ | Pair (a, b) where types are independent. | `prod A B` |
| **Sigma Type** | $\Sigma (x:A), B(x)$ | Pair (a, b) where type of b depends on a. | `structure` or `Sigma` |
