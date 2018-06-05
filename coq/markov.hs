
data State = St String

data Pattern = Var Int
             | PLit String
             | Seq Pattern Pattern
             | Both Pattern Pattern
             | Or Pattern Pattern

data Term = Cond [Pattern Term] 
          | PLit String