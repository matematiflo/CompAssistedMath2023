-- Definition of a recursive BinaryTree data structure

data BinaryTree a
  = Empty -- Leaf
  | Node a (BinaryTree a) (BinaryTree a)

-- Compute the height of a given binaryHeap by just computing the height of the leftmost path.

heapHeight :: BinaryTree a -> Int
heapHeight Empty = -1
heapHeight (Node a left right) = 1 + heapHeight left

-- Note: Computing the heapHeight of an Empty BinaryTree fails (-1 instead of 0)
-- but is also not too interesting. To fix this, it's better to have a `Leaf a` Constructor
-- instead of an "invisible" Empty constructor. Then `heapHeight Empty = 0` is a fine base case.

-- calculate the height of any BinaryTree by trying all paths (bruteforce)
treeHeightUnbalanced :: BinaryTree a -> Int
treeHeightUnbalanced Empty = 0
treeHeightUnbalanced (Node a left right) = maximum [1, lh, rh]
  where
    lh = 1 + treeHeightUnbalanced left
    rh = 1 + treeHeightUnbalanced right

-- How a custom heap-based integer log_2 function could be implemented.
-- integer_log2 x = heapHeight (buildHeap (x))

t_empty :: BinaryTree Int = Empty

t_full :: BinaryTree Int = Node 1 (Node 2 Empty Empty) (Node 3 Empty Empty)
