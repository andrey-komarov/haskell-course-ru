module ITMOPrelude.Tree where

-- Всё что угодно, главное, чтобы соответствовало
-- заданию

data Tree a = Node a (Tree a) (Tree a) | Leaf

-- Пустое дерево
empty :: Tree a
empty = Leaf

-- Сделать элемент корнем дерева
insert :: a -> Tree a -> Tree a
insert x t = Node x t Leaf

-- Добавить элемент самым левым в дерево
addLeft :: a -> Tree a -> Tree a
addLeft x Leaf = Node x Leaf Leaf
addLeft x (Node y left right) = Node y (addLeft x left) right

-- Добавить элемент самым правым в дерево
addRight :: a -> Tree a -> Tree a
addRight x Leaf = Node x Leaf Leaf
addRight x (Node y left right) = Node y left $ addRight x right

-- Поворот влево
--    p              q 
--   / \            / \
--  a   q    ->    p   c 
--     / \        / \
--    b   c      a   b 
rotateLeft :: Tree a -> Tree a
rotateLeft (Node p a (Node q b c)) = Node q (Node p a b) c 

-- Поворот вправо
--      q          p
--     / \        / \
--    p   c  ->  a   q
--   / \            / \
--  a   b          b   c
rotateRight :: Tree a -> Tree a
rotateRight (Node q (Node p a b) c) = Node p a $ Node q b c


-- Аналог функции map. Применить функцию к каждому элементу дерева
tmap :: (a -> b) -> Tree a -> Tree b
tmap f Leaf = Leaf
tmap f (Node x left right) = Node (f x) (tmap f left) (tmap f right)


-- Аналог функции foldr. Унылый
tfoldr :: (a -> a -> a) -> a -> Tree a -> a
tfoldr f z Leaf = z
tfoldr f z (Node x left right) = tfoldr f z left `f` x `f` tfoldr f z right 
