




> module Natural where
>
> data Nat
>  = Zero | Next Nat
>  deriving (Eq, Show)

> natRecur :: a -> (a -> a) -> Nat -> a
> natRecur e _ Zero     = e
> natRecur e f (Next n) = f (natRecur e f n)

> nat0 = Zero
> nat1 = Next nat0
> nat2 = Next nat1
> nat3 = Next nat2
> nat4 = Next nat3
> nat5 = Next nat4
> nat6 = Next nat5
> nat7 = Next nat6
> nat8 = Next nat7
> nat9 = Next nat8
