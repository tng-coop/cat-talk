import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Data.Int.Order.Basic

open CategoryTheory

-- Int is a Preorder (actually a LinearOrder), so it is a Category.
-- Since Int is in Type 0, and the relation is a Prop,
-- it forms a Category.{0} Int (a SmallCategory).

example : Category Int := inferInstance
