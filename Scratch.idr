module Scratch


sym' : {auto con : Type -> Type} -> {auto inj : (con a = con b) -> (a = b)} -> {p : con a} -> {q : con b} -> (p = q) -> (q = p)
sym' prf = ?sym_rhs

||| Trick: add `con` as an auto implicit helps Idris to fill in the type constructor.
negEqSym' : {auto con : Type -> Type} -> {p : con a} -> {q : con b} -> Not (p = q) -> Not (q = p)
negEqSym' f prf = f (sym' prf)
