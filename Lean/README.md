
# **Formal proofs in Lean 3**

**Author:** Florent Schaffhauser, Uni-Heidelberg, Summer Semester 2023

This is the GitHub repository for the *Introduction to Lean* part of the **(Pro)Seminar on computer-assisted mathematics**, held at the University of Heidelberg in the Summer Semester of 2023.

Below you will find the programme of the seminar. For each week, there is a corresponding `.lean` file, which you can use to practice. You can also view a markdown version of the weekly files by clicking on the corresponding `.md` files.

In order to work on the `.lean` files, several options are available:

* Download any of the files and open it in your [CoCalc](https://cocalc.com) account. *This is the recommended option to get started.*
* Go to the [GitHub webpage for this repository](https://github.com/matematiflo/Comp_assisted_math/) and open a *Codespace* (this is done directly in your browser). You can also fork the repository and then open the Codespace from within your forked copy.
* [Install *Lean 3* on your computer](https://leanprover-community.github.io/lean3/get_started.html), then fork or clone the [present repository](https://github.com/matematiflo/Comp_assisted_math/) and add the mathlib cache to it via the command line `leanproject get-mathlib-cache` (run in a terminal window, from your local copy of the repository). To check that everything is in place, you can  type `leanproject check` before you start working on the files (the answer to this last prompt should be `Everything looks fine`).

Be aware that *Lean 4* is not backwards-compatible with *Lean 3* and that the `.lean` files in this repository will not work in *Lean 4*.

**Programme of the *Lean* seminar:**

1. Definitions and equality of terms (`reflexivity`, `exact`, `apply`, `intro`, `cases`)
2. Functions and logical implications (`show`, `split`, `by_contradiction`)
3. Inductive types (`induction`, `use`, `by_cases`)
4. Formalising mathematical objects (`class`, `instance`, `structure`)
