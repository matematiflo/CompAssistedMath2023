# Chenyicolas Project 1: Gauß' algorithm in plain python

## Project description (as given)

This is the most programmation-oriented project. You are asked to write a program that lets you:

1. Input a matrix.
2. Put it in (reduced) row-echelon form.
3. (If possible) Indicate the list of elementary operations that has been performed, along with the corresponding elementary matrices.

## Implementation

In this project we implemented gauss' algorithm in an **iterative** way (support _reduced_ row-echelon form) and **recursive**
supporting row-echelon form. Although the iterative one contains some recursive functions and the recursive one
uses iterative paradigms as well.

We support different ways of generating the elementary operations and reapplying them step-by-step, or printing them
in parallel with the algorithm execution itself, "documenting its steps" along the way.

All the basic lienar algebra functions needed are implemented in `algebra.py` and the project has no external
dependencies.
