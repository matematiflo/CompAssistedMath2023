from algebra import *
from functools import reduce


def find_better_candidate(m: M, c: int, end_column: int, now_row: int) -> int:
    """
    Recursive function, going through the left-most non-zero column to find
    the best candidate as a first_row, that is one row with left-most pivot.

    We will start outside in, to find the left-most pivot, creating zeroes
    below it. Then we repeat the process with the inner matrix.
    """

    row_dim = len(m)

    # There is no better candidate, current toprow is already best.
    if c == end_column:
        return now_row

    col = column(m, c)

    # The first row with a non-zero entry
    for s in range(now_row + 1, row_dim):
        if col[s] != 0:
            return s
    return find_better_candidate(m, c + 1, end_column, now_row)


def gauss_algorithm_iterative(m: M, is_traced=False) -> tuple[M, int, list[M]]:
    """
    Perform Gauss algorithm (iterative)
    1. Get most-left column with non-zero values (find best row for first column, otherwise ignore this column by increasing now_column
    2. If the top-row value is zero --> SWAP R0 with last non-zero row (or put to bottom using nullrow_cnt)
    3. Make zeroes below the pivot (by adding the respective inverse multiple)
    4. Perform 1-3 with remaining rows.

    It returns the reduced matrix(in echelon form), the rank and the trace of operations
    """

    nullrow_cnt = 0
    now_row = 0
    now_column = 0
    row_dim = len(m)
    trace = []
    while now_row < row_dim - nullrow_cnt:
        (pivot_index, pivot) = get_pivot(m[now_row])

        if pivot_index == None:  # it's a nullrow
            swap = S(row_dim, now_row, row_dim - 1 - nullrow_cnt)
            trace.append(swap)
            m = mult(swap, m)
            nullrow_cnt += 1
        else:
            if pivot_index > now_column:  # there's still better pivot column at left
                better_candidate = find_better_candidate(
                    m, now_column, pivot_index, now_row
                )
                swap = S(row_dim, now_row, better_candidate)
                trace.append(swap)
                m = mult(swap, m)
                (pivot_index, pivot) = get_pivot(
                    m[now_row]
                )  # after swapping, we must get the pivot again
            col = column(m, pivot_index)
            scalar = list(map(lambda c: c / pivot, col))
            for k in range(now_row + 1, row_dim - nullrow_cnt):
                if (
                    -scalar[k] < 0 or -scalar[k] > 0
                ):  # if already 0, we don't need to do anything
                    addition = A(row_dim, k, now_row, -scalar[k])
                    trace.append(addition)
                    m = mult(addition, m)
            now_row += 1
            now_column += 1
    if is_traced:
        return (m, row_dim - nullrow_cnt, trace)
    else:
        return (m, row_dim - nullrow_cnt, [])


def normalize(m: M, is_traced=False) -> tuple[M, int, list[M]]:
    """
    Normalize makes the matrix into a reduced echelon matrix.
    It applies the gauss algorithm first, then it goes from bottom(non-zero row) to top with following steps:
    1. Normalize the pivot element of this row into 1
    2. Make the element above the pivot zero by adding the respective additive inverse.
    3. Repeat 1-2 on the above row till the first row.

    It returns a tuple with reduced matrix, the rank of the matrix and trace of operations
    """

    row_dim = len(m)
    (m, rank, trace) = gauss_algorithm_iterative(m, is_traced)
    pivots = get_pivots(m) #get all pivots to make it faster later
    for k in range(rank):
        mul = M(row_dim, rank - k - 1, 1 / pivots[rank - k - 1][1]) #normalizing
        if is_traced:
            trace.append(mul)
        m = mult(mul, m)
        col_index = pivots[rank - k - 1][0] #the column above this pivot should be cleared
        for r in range(rank - k - 1):
            if -m[r][col_index] < 0 or -m[r][col_index] > 0:
                addition = A(row_dim, r, rank - k - 1, -m[r][col_index]) #make the element zero
                if is_traced:
                    trace.append(addition)
                m = mult(addition, m)
    if is_traced:
        return (m, rank, trace)
    else:
        return (m, rank, [])

def inverse(m: M) -> M:
    """
    We can compute the inverse of an invertible matrix by simply
    multipling all elementary matrices together.
    """

    (id, rank, trace) = normalize(m, True)
    assert len(m) == len(m[0]) #if it's a square matrix
    assert rank == len(m) # if it's invertible
    trace.reverse() # matrix multiplication is not commutativ!
    return reduce(mult, trace, I(rank))
