module Data.Relation

import public Control.Relation

%default total

export infix 5 ~>
public export
0 (~>) : Rel a -> Rel a -> Type
p ~> q = {x, y : a} -> p x y -> q x y
