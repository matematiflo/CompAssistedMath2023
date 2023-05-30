# Chenyicolas Project 1: Gauß' algorithm in plain python

## Project description (as given)

This is the most programmation-oriented project. You are asked to write a program that lets you:
1. Input a matrix.
2. Put it in reduced row-echelon form.
3. (If possible) Indicate the list of elementary operations that has been performed, along with the corresponding elementary matrices.

## Gauß algorithm

What problem is solved...

It has 3 elementary operations. Add the multiple of another row to the current row.




To generate zeroes in the first column, the first row is used.
To generate zeroes in the 2nd column, the 2nd row is rused.
To generate zeroes in the nth column the nth row is used.

Does it have to be that way / is it always working?


### Implementation ideas / approaches

- Sort the list of rows decreasing by their absolute values from left two right (should bring all zero lines to the bottom)
- Generate a stack/queue of todos for generating zeroes at specific index locations.

## Documentation

Which types/data structures are used. Core ideas.
Mathematical properties and how we check them.

## Todo

- [x] Problem description
- [x] Implementation
- [x] Documentation
- [x] Pretty Print
- [ ] Presentation (notebook)
  - [ ] Finish
  - [ ] Upload


## Presentation Outline:

- Motivation: Algorithm itself (ops, elementary matrices)  Chenyi
- Matrix Algebra in Python (data types, functions)  
  - Outline the signatures, types    Nicolas
  - properties (check functions)
- (Demo)
- Go through code
  - don't explain the implementation, but show an example   Chenyi
- tests?!
