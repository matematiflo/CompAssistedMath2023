from fractions import Fraction
from random import uniform
from gauss_recursive import *
from algebra import *

Rational_Matrix = [
    [Fraction(2, 1), Fraction(1, 1), Fraction(0, 1), Fraction(0, 1)],
    [Fraction(3, 1), Fraction(5, 1), Fraction(-1, 1), Fraction(-3, 1)],
    [Fraction(0, 1), Fraction(3, 1), Fraction(-1, 1), Fraction(0, 1)],
    [Fraction(1, 1), Fraction(4, 1), Fraction(0, 1), Fraction(-2, 1)],
]

Real_Matrix = [[3.5, -2.0, 1.0], [-3.1, 5.6, 0.0], [4.7, 0.0, -1.3]]

Small_Matrix = [[1]]

Zero_Matrix = [[0, 0, 0], [0, 0, 0]]

Big_Matrix = [list(uniform(0, 100) for i in range(100)) for j in range(100)]

Bad_Matrix = [[0] * 5, [1] * 5, [0] * 5]

Good_Matrix = [[0.0, 2.0, 3.0], [2.0, 3.0, 4.0], [6.0, 4.0, 1.0]]

Demo_Matrix = [[4, 1, 2, 3], [2, 0.5, 1, -2], [0, 3, 0, 2], [4, -2, -1, 3]]



if __name__ == "__main__":
    gauss_rec_go(Demo_Matrix)
