from algebra import *

trace = True


def find_pivot_row_index(column: R) -> int:
    """Assuming `column` contains a non-zero value, find it's (row) index"""
    for i in range(len(column)):
        if column[i] != 0:
            return i
        else:
            i += 1
            continue


def gauss_rec(
    m: M, nowrow: int, nowcol: int, n_rows: int, n_cols: int, stack, depth: int
) -> tuple[M, list[M]]:
    """
    Recursive implementation of gauss elimination.

    1. Establish a useful toprow by finding left-most pivot row. Skip zero columns and swap rows if necessary.
    1.1 As long as zero-column, increment nowcol
    1.2 Current nowcol is guaranteed to have a non-zero entry in some row. (as it's not a zero column)
    2. Create zeroes below the pivot
    3. Solve recursively for m with `nowrow - 1` and `nowcol - 1`

    Prints the transformed matrices for each step, with a natural language description and
    returns the accumulated list of elementary_matrices.

    """

    indentation = "\t" * depth

    if trace:
        print(
            f"\n{indentation}Working on matrix of size {n_rows - nowrow} x {n_cols - nowcol}"
        )

    # Base case of recursion
    if nowrow == n_rows - 1 or nowcol == n_cols - 1:
        return m, stack

    # 1. Skip any zero columns
    # TODO: Optimization potential: Checking if nullrow can fail by returning the index of nonzero row for that column
    while is_nullrow(column(m[nowrow:], nowcol)):
        if trace:
            print(f"\n{indentation}Skipping at least one zero-column...")
        nowcol += 1
        if nowcol == n_cols - 1:
            return m, stack

    if trace:
        print(f"\n{indentation}-- Establish a useful toprow --")

    # 2. Establish a useful toprow, swap if necessary. column(m, nowcol) is guaranteed to have a pivotrow
    pivot = m[nowrow][nowcol]
    if pivot == 0:
        better_row = find_pivot_row_index(column(m[nowrow + 1:], nowcol)) + nowrow + 1
        elem_swap = S(n_rows, nowrow, better_row)
        if trace:
            stack.append(elem_swap)
        m = mult(elem_swap, m)
        if trace:
            # print(f"Swapped with good pivot row (using: S({n_rows}, {nowrow}, {find_pivot_row_index(column(m[nowrow + 1:], nowcol))}) + nowrow + 1)")
            print(
                    f"\n{indentation}Swapped row {nowrow + 1} with good pivot row {better_row + 1}\n"
            )
            show_indent(m, depth)
    elif trace:
        print(f"\n{indentation}No need to swap rows. Current pivot is fine\n")

    pivot = m[nowrow][nowcol]
    assert pivot != 0

    # TODO: normalize toprow by dividing by it's pivot simplifying the computation of inv_scalar. Leads to reduced row echelon form?!

    if trace:
        print(f"\n{indentation}-- Create zeroes below the pivot --")
    # 3. Create zeroes below the pivot
    for rowindex in range(nowrow + 1, n_rows):  # TODO: create correct range definition!
        # for rowindex in range(1, n_rows - nowrow): # TODO: check range for recursive calls! Yep, there was a off-by-one bug
        if m[rowindex][nowcol] == 0:
            continue  # entry below pivot is already 0
        else:
            inv_scalar = -(m[rowindex][nowcol] / pivot)
            elem_add = A(n_rows, rowindex, nowrow, inv_scalar)
        if trace:
            stack.append(elem_add)
        m = mult(elem_add, m)
        if trace:
            print(
                f"\n{indentation}Created 0 below pivot in row {rowindex + 1} by adding {inv_scalar} * row {nowrow + 1} to it.\n"
            )
            show_indent(m, depth)

    return gauss_rec(m, nowrow + 1, nowcol + 1, n_rows, n_cols, stack, depth + 1)


def gauss_rec_go(m: M):
    """run recursive gauss_split with initial values"""
    n_rows = len(m)
    n_cols = len(m[0])
    if n_rows == 1 and n_cols == 1:
        return m
    if m == [[0] * n_cols] * n_rows:
        return m
    print("Bring the following matrix to row_echelon form:\n")
    show(m)
    return gauss_rec(m, 0, 0, n_rows, n_cols, [], 0)

if __name__ == '__main__':
    from example import Good_Matrix, Demo_Matrix
    gauss_rec_go(Demo_Matrix)
