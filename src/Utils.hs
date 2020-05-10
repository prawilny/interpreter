module Utils where
import AbsLattePlus

type PInfo = Maybe (Int, Int)

atPosition :: PInfo -> String
atPosition (Just (line, _)) = "line " ++ show line ++ ": "
atPosition Nothing = ": "

getPosition :: Expr PInfo -> PInfo
getPosition exp = case exp of
    EVar pi _ -> pi
    ELitInt pi _ -> pi
    ELitTrue pi -> pi
    ELitFalse pi -> pi
    EApp pi _ _ -> pi
    EString pi _ -> pi
    ENeg pi _ -> pi
    ENot pi _ -> pi
    EMul pi _ _ _ -> pi
    EAdd pi _ _ _ -> pi
    ECmp pi _ _ _ -> pi
    EAnd pi _ _ -> pi
    EOr pi _ _ -> pi
