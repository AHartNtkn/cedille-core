module Core where

-- Cedille Core (Aaron's Type Theory)
--
--   Nam   Hex   Syntax     Desc                                                 
-- ,-----,-----,----------,--------------------------------------------------,
-- | Typ | 0   | *        | type of types                                    |
-- | Kin | 1   | +        | type of type of types                            |
-- | Var | 2   |          | variable                                         |
-- | All | 3   | @x T t   | forall                                           |
-- | All | 3   | &x T t   | forall (erased)                                  |
-- | Lam | 4   | #x T t   | lambda                                           |
-- | Lam | 4   | %x T t   | lambda (erased)                                  |
-- | App | 5   | /f x     | application                                      |
-- | App | 5   | \f x     | application (erased)                             |
-- | Let | 6   | $x t u   | local definition                                 |
-- | Dep | 7   | ^x T U   | dependent intersection theorem                   |
-- | Bis | 8   | |x t U u | dependent intersection proof                     |
-- | Fst | 9   | <t       | first element of dependent intersection          |
-- | Snd | A   | >t       | second element of dependent intersection         |
-- | Eql | B   | =t u     | equality (t == u) theorem                        |
-- | Rfl | C   | :t u     | equality (t == t) proof, erases to u             |
-- | Sym | D   | ~e       | symmetry of equality (t == u implies u == t)     |
-- | Cst | E   | !e t u   | if (t == u) and (t : T), cast (u : U) to (u : T) |
-- | Rwt | F   | ?e T p   | if (t == u), cast (p : T[t/x]) to (p : U[t/x])   |
-- '-----'-----'----------'--------------------------------------------------'

-- TODO: get rid of this small import
import Data.List (find)
import Control.Monad (join)
import Control.Exception (try, IOException)

-- Primitive constructors
data Prim r b
  = Typ
  | Kin
  | Var String
  | All Bool String r (b -> IO r)
  | Lam Bool String r (b -> IO r)
  | App Bool r r
  | Let String r (b -> IO r)
  | Dep String r (b -> IO r)
  | Bis String r (b -> IO r) r
  | Fst r
  | Snd r
  | Eql r r
  | Rfl r r
  | Sym r
  | Cst r r r
  | Rwt String r (b -> IO r) r
  | Err
  | Path String

-- Terms are layers of primitive constructors
newtype Term
  = Term (Prim Term Term)

-- Anns are terms with type, normal-form and context annotations on each constructor
data Ann
  = Ann {
    valOf :: Prim Ann Term,
    norOf :: Term,
    typOf :: Term
  }

-- Converts an ASCII String to a Term
fromString :: String -> Term
fromString src = snd (parseTerm src) [] where
  parseTerm :: String -> (String, [(String,Term)] -> Term)

  -- Whitespace
  parseTerm (' ' : src) =
    parseTerm src

  -- Newlines
  parseTerm ('\n' : src) =
    parseTerm src

  -- Type
  parseTerm ('*' : src) =
    (src, \ ctx -> Term Typ)

  -- Kind
  parseTerm ('+' : src) =
    (src, \ ctx -> Term Kin)

  -- Forall
  parseTerm ('@' : src) = let
    (src0, nam) = parseName src
    (src1, typ) = parseTerm src0
    (src2, bod) = parseTerm src1
    in (src2, \ ctx -> Term (All False nam (typ ctx) (\ var -> return $ bod ((nam,var) : ctx))))

  -- Forall (erased)
  parseTerm ('&' : src) = let
    (src0, nam) = parseName src
    (src1, typ) = parseTerm src0
    (src2, bod) = parseTerm src1
    in (src2, \ ctx -> Term (All True nam (typ ctx) (\ var -> return $ bod ((nam,var) : ctx))))

  -- Lambda
  parseTerm ('#' : src) = let
    (src0, nam) = parseName src
    (src1, typ) = parseTerm src0
    (src2, bod) = parseTerm src1
    in (src2, \ ctx -> Term (Lam False nam (typ ctx) (\ var -> return $ bod ((nam,var) : ctx))))

  -- Lambda (erased)
  parseTerm ('%' : src) = let
    (src0, nam) = parseName src
    (src1, typ) = parseTerm src0
    (src2, bod) = parseTerm src1
    in (src2, \ ctx -> Term (Lam True nam (typ ctx) (\ var -> return $ bod ((nam,var) : ctx))))

  -- Application
  parseTerm ('/' : src) = let
    (src0, fun) = parseTerm src
    (src1, arg) = parseTerm src0
    in (src1, \ ctx -> Term (App False (fun ctx) (arg ctx)))

  -- Application (erased)
  parseTerm ('\\' : src) = let
    (src0, fun) = parseTerm src
    (src1, arg) = parseTerm src0
    in (src1, \ ctx -> Term (App True (fun ctx) (arg ctx)))

  -- Local definition
  parseTerm ('$' : src) = let
    (src0, nam) = parseName src
    (src1, val) = parseTerm src0
    (src2, bod) = parseTerm src1
    in (src2, \ ctx -> Term (Let nam (val ctx) (\ var -> return $ bod ((nam,var) : ctx))))

  -- Dependent intersection
  parseTerm ('^' : src) = let
    (src0, nam) = parseName src
    (src1, fty) = parseTerm src0
    (src2, sty) = parseTerm src1
    in (src2, \ ctx -> Term (Dep nam (fty ctx) (\ var -> return $ sty ((nam,var) : ctx))))

  -- Dependent intersection proof
  parseTerm ('|' : src) = let
    (src0, nam) = parseName src
    (src1, fst) = parseTerm src0
    (src2, typ) = parseTerm src1
    (src3, snd) = parseTerm src2
    in (src3, \ ctx -> Term (Bis nam (fst ctx) (\ var -> return $ typ ((nam,var) : ctx)) (snd ctx)))

  -- First projection
  parseTerm ('<' : src) = let
    (src0, bis) = parseTerm src
    in (src0, \ ctx -> Term (Fst (bis ctx)))

  -- Second projection
  parseTerm ('>' : src) = let
    (src0, bis) = parseTerm src
    in (src0, \ ctx -> Term (Snd (bis ctx)))

  -- Equality
  parseTerm ('=' : src) = let
    (src0, fst) = parseTerm src
    (src1, snd) = parseTerm src0
    in (src1, \ ctx -> Term (Eql (fst ctx) (snd ctx)))

  -- Reflexivity
  parseTerm (':' : src) = let
    (src0, prf) = parseTerm src
    (src1, ret) = parseTerm src0
    in (src1, \ ctx -> Term (Rfl (prf ctx) (ret ctx)))

  -- Symmetry
  parseTerm ('~' : src) = let
    (src0, eql) = parseTerm src
    in (src0, \ ctx -> Term (Sym (eql ctx)))

  -- Cast
  parseTerm ('!' : src) = let
    (src0, eql) = parseTerm src
    (src1, fst) = parseTerm src2
    (src2, snd) = parseTerm src1
    in (src2, \ ctx -> Term (Cst (eql ctx) (fst ctx) (snd ctx)))

  -- Rewrite
  parseTerm ('?' : src) = let
    (src0, nam) = parseName src
    (src1, eql) = parseTerm src0
    (src2, typ) = parseTerm src1
    (src3, ret) = parseTerm src2
    in (src3, \ ctx -> Term (Rwt nam (eql ctx) (\ var -> return $ typ ((nam,var) : ctx)) (ret ctx)))

  -- Error
  parseTerm ('_' : src) =
    (src, \ ctx -> Term Err)

  -- Paths
  parseTerm ('\'' : src) = let
    (pname, src') = break ('\'' ==) src
    in (drop 1 src', \ ctx -> Term (Path pname))

  -- Variables
  parseTerm src = let
    (src', nam) = parseName src
    in (src', \ ctx ->
      case find ((nam ==) . fst) ctx of
        Nothing    -> Term (Var nam)
        Just (_,t) -> t)

  -- Names
  parseName :: String -> (String, String)
  parseName "" = ("", "")
  parseName (' ' : src) = (src, "")
  parseName ('\n' : src) = (src, "")
  parseName (chr : src) = let
    (src0, nam) = parseName src
    in (src0, chr : nam)

-- Converts a Term to an ASCII String
toString :: Term -> IO String
toString = go 0 where
  -- Type
  go d (Term Typ)
    = return "*"

  -- Kind
  go d (Term Kin)
    = return "+"

  -- Variable
  go d (Term (Var nam))
    = return nam

  -- Forall
  go d (Term (All era nam typ bod)) = do
    let
      tag' = if era then "&" else "@"
      nam' = nam ++ show d
    typ' <- go d typ
    bod' <- go (d+1) =<< bod (Term (Var nam'))
    return $ tag' ++ nam' ++ " " ++ typ' ++ " " ++ bod'

  -- Lambda
  go d (Term (Lam era nam typ bod)) = do
    let
      tag' = if era then "%" else "#"
      nam' = nam ++ show d
    typ' <- go d typ
    bod' <- go (d+1) =<< bod (Term (Var nam'))
    return $  tag' ++ nam' ++ " " ++ typ' ++ " " ++ bod'

  -- Application
  go d (Term (App era fun arg)) = do
    let
      tag' = if era then "\\" else "/"
    fun' <- go d fun
    arg' <- go d arg
    return $ tag' ++ fun' ++ " " ++ arg'

  -- Local definition
  go d (Term (Let nam val bod)) = do
    let
      nam' = nam ++ show d
    val' <- go d val
    bod' <- go (d+1) =<< bod (Term (Var nam'))
    return $ "$" ++ nam' ++ " " ++ val' ++ " " ++ bod'

  -- Dependent intersection
  go d (Term (Dep nam fty sty)) = do
    let
      nam' = nam ++ show d
    fty' <- go d fty
    sty' <- go (d+1) =<< sty (Term (Var nam'))
    return $ "^" ++ nam' ++ " " ++ fty' ++ " " ++ sty'

  -- Dependent intersection proof
  go d (Term (Bis nam fst sty snd)) = do
    let
      nam' = nam ++ show d
    fst' <- go d fst
    sty' <- go d =<< sty (Term (Var nam'))
    snd' <- go d snd
    return $ "|" ++ nam' ++ " " ++ fst' ++ " " ++ sty' ++ " " ++ snd'

  -- First projection
  go d (Term (Fst bis)) =
    (++) "<" <$> go d bis

  -- Second projection
  go d (Term (Snd bis)) =
    (++) ">" <$> go d bis
    
  -- Equality
  go d (Term (Eql fst snd)) = do
    fst' <- go d fst
    snd' <- go d snd
    return $ "=" ++ fst' ++ " " ++ snd'

  -- Reflexivity
  go d (Term (Rfl prf ret)) = do
    prf' <- go d prf
    ret' <- go d ret
    return $ ":" ++ prf' ++ " " ++ ret'

  -- Symmetry
  go d (Term (Sym eql)) =
    (++) "~" <$> go d eql

  -- Cast
  go d (Term (Cst eql fst snd)) = do
    eql' <- go d eql
    fst' <- go d fst
    snd' <- go d snd
    return $ "!" ++ eql' ++ " " ++ fst' ++ " " ++ snd'

  -- Rewrite
  go d (Term (Rwt nam eql typ ret)) = do
    let
      nam' = nam ++ show d
    eql' <- go d eql
    typ' <- go d =<< typ (Term (Var nam'))
    ret' <- go d ret
    return $ "?" ++ nam' ++ " " ++ eql' ++ " " ++ typ' ++ " " ++ ret'

  -- File path
  go d (Term (Path pname)) =
    return $ '\'' : pname ++ "'"

  -- Error
  go d (Term Err) =
    return $ "_"

-- Recursivelly annotate every constructor of a term with its type and normal form.
annotate :: Term -> IO Ann
annotate = go [] where
  go :: [(String, (Term, Term))] -> Term -> IO Ann

  -- Type: (* : +)
  go ctx (Term Typ) =
    return $ Ann Typ (Term Typ) (Term Kin)

  -- Variable
  go ctx (Term (Var nam)) = return $
    case find ((nam ==) . fst) ctx of
      Just (nam, (nor, typ)) -> Ann (Var nam) nor typ
      Nothing -> Ann (Var nam) (Term (Var nam)) (Term (Var nam))

  -- Forall: (T : s) and (U[(t:T)/x] : s) implies ((@x T U) : *), where (s) is either (*) or (+)
  go ctx (Term (All era nam typ bod)) = do
    typ' <- go ctx typ
    let 
      bod' = ex nam (norOf typ') ctx bod
      rVal = All era nam typ' bod'
      rNor = Term (All era nam (norOf typ') ((norOf <$>) . bod'))
      rTyp = do
        bd <- bod' (Term (Var nam))
        return $
          if isSort (typOf typ') && not (isErr (typOf bd))
          then Term Typ
          else Term Err
    Ann rVal rNor <$> rTyp

  -- Lambda: (T : *) and (u[(x:T)/x] : U) implies ((#x t u) : (@x T U))
  go ctx (Term (Lam era nam typ bod)) = do
    typ' <- go ctx typ
    let
      bod' = ex nam (norOf typ') ctx bod
      rVal = Lam era nam typ' bod'
    rNor <- if era
        then norOf <$> bod' (Term (Var nam))
        else return $ Term (Lam era nam (Term Typ) ((norOf <$>) . bod'))
    let
      rTyp = do
        bd <- bod' (Term (Var nam))
        return $
          if isSort (typOf typ') && not (isErr (typOf bd))
          then Term (All era nam (norOf typ') ((typOf <$>) . bod'))
          else Term Err
    Ann rVal rNor <$> rTyp

  -- Application: (t : (@x T U)) and (u : T) implies ((/t u) : U[t/x])
  go ctx (Term (App era fun arg)) = do
    fun' <- go ctx fun
    arg' <- go ctx arg
    rNor <-
        if era 
        then return $ norOf fun'
        else case norOf fun' of
          (Term (Lam era nam typ bod)) -> bod (norOf arg')
          otherwise -> return $ Term (App era (norOf fun') (norOf arg'))
    let
      rVal = App era fun' arg'
      rTyp = case typOf fun' of
        (Term (All allEra allNam allTyp allBod)) -> do
          eq <- equals allTyp (typOf arg')
          if eq && allEra == era
          then allBod (norOf arg')
          else return $ Term Err
        otherwise -> return $ Term Err
    Ann rVal rNor <$> rTyp

  -- Local definition
  go ctx (Term (Let nam val bod)) = do
    val' <- go ctx val
    let
      bod' = ex nam (typOf val') ctx bod
      rVal = Let nam val' bod'
    res' <- bod' (norOf val')
    let
      rNor = norOf res'
      rTyp = typOf res'
    return $ Ann rVal rNor rTyp

  -- Dependent intersection: (T : *) and (U[(t:T)/x] : *) implies ((^x T U) : *)
  go ctx (Term (Dep nam fty sty)) = do
    fty' <- go ctx fty
    let
      sty' = ex nam (norOf fty') ctx sty
      rVal = Dep nam fty' sty'
      rNor = Term (Dep nam (norOf fty') ((norOf <$>) . sty'))
      rTyp = do
        st <- sty' (Term (Var nam))
        case (typOf fty', typOf st) of
          (Term Typ, Term Typ) -> return $ Term Typ
          otherwise -> return $ Term Err
    Ann rVal rNor <$> rTyp

  -- Dependent intersection proof: (t : T), (u : U[t/x]), (t equals u) implies ((|x t U u) : (^x T U))
  go ctx (Term (Bis nam fst sty snd)) = do
    fst' <- go ctx fst
    snd' <- go ctx snd
    let sty' = ex nam (typOf fst') ctx sty
    sty0 <- norOf <$> sty' (norOf fst')
    let
      sty1 = typOf snd'
      rVal = Bis nam fst' sty' snd'
      rNor = norOf fst'
      rTyp = do
        eq <- (||) <$> equals sty0 sty1 <*> equals (norOf fst') (norOf snd')
        if not (isErr (typOf fst')) || 
           not (isErr sty0) ||
           eq
        then return $ Term (Dep nam (typOf fst') ((norOf <$>) . sty'))
        else return $ Term Err
    Ann rVal rNor <$> rTyp

  -- First projection: (t : (^x T U)) implies ((< t) : T) 
  go ctx (Term (Fst bis)) = do
    bis' <- go ctx bis
    let
      rVal = Fst bis'
      rNor = norOf bis'
      rTyp = case typOf bis' of
        Term (Dep nam fty sty) -> fty
        otherwise -> Term Err
    return $ Ann rVal rNor rTyp
  
  -- Bis projection: (t : (^x T U)) implies ((> t) : U[t/x]) 
  go ctx (Term (Snd bis)) = do
    bis' <- go ctx bis
    let
      rVal = Snd bis'
      rNor = norOf bis'
      rTyp = case typOf bis' of
        (Term (Dep nam fty sty)) -> sty (norOf bis')
        otherwise -> return $ Term Err
    Ann rVal rNor <$> rTyp

  -- Equality: ((= t u) : *)
  go ctx (Term (Eql fst snd)) = do
    fst' <- go ctx fst
    snd' <- go ctx snd
    let
      rVal = Eql fst' snd'
      rNor = Term (Eql (norOf fst') (norOf snd'))
      rTyp = if
        not (isErr (typOf fst')) &&
        not (isErr (typOf snd'))
        then Term Typ
        else Term Err
    return $ Ann rVal rNor rTyp

  -- Reflexivity: ((= t t) : *) implies ((: t u) : (= t t))
  go ctx (Term (Rfl eql ret)) = do
    eql' <- go ctx eql
    ret' <- go ctx ret
    let
      rVal = Rfl eql' ret'
      rNor = norOf ret'
      rTyp = if not (isErr (typOf ret'))
        then Term (Eql (norOf eql') (norOf eql')) 
        else Term Err
    return $ Ann rVal rNor rTyp

  -- Symmetry: (t : (= T U)) implies (t : (= U T))
  go ctx (Term (Sym eql)) = do
    eql' <- go ctx eql
    let
      rVal = Sym eql'
      rNor = Term (Sym (norOf eql'))
      rTyp = case typOf eql' of
        (Term (Eql fst snd)) -> Term (Eql snd fst)
        otherwise -> Term Err
    return $ Ann rVal rNor rTyp

  -- Cast: (e : (= t u)) and (t : T) implies (u : T)
  go ctx (Term (Cst eql fst snd)) = do
    eql' <- go ctx eql
    fst' <- go ctx fst
    snd' <- go ctx snd
    let
      rVal = Cst eql' fst' snd'
      rNor = norOf snd'
    rTyp <- case typOf eql' of
        (Term (Eql fstVal sndVal)) -> do
          eq <- (&&) <$> equals (norOf fst') fstVal <*> equals (norOf snd') sndVal
          if eq
          then return $ typOf fst'
          else return $ Term Err
        otherwise -> return $ Term Err
    return $ Ann rVal rNor rTyp

  -- File Path
  go ctx (Term (Path path)) = do
    contents <- try $ readFile (path ++ ".ced") :: IO (Either IOException String)
    case contents of
      Left err -> return $ Ann (Path path) (Term Err) (Term Err)
      Right s -> go ctx (fromString s)

  -- Rewrite: (t : (= t u)) and (p : P[t/x]) implies (p : P[u/x])
  go ctx (Term (Rwt nam eql typ ret)) = do
    eql' <- go ctx eql
    ret' <- go ctx ret
    let
      typ' = ex nam (Term Typ) ctx typ
      rNor = norOf ret'
      rVal = Rwt nam eql' typ' ret'
    rTyp <- case typOf eql' of
        (Term (Eql fstVal sndVal)) -> do
          eq <- equals (typOf ret') =<< (norOf <$> typ' fstVal)
          if eq
          then norOf <$> typ' sndVal
          else return $ Term Err
        otherwise -> return $ Term Err
    return $ Ann rVal rNor rTyp

  ex :: String -> Term -> [(String, (Term, Term))] -> (Term -> IO Term) -> Term -> IO Ann
  ex nam typ ctx bod = \var -> go ((nam, (var, typ)) : ctx) =<< bod (Term (Var nam))

-- Checks if two terms are syntactically equal
equals :: Term -> Term -> IO Bool
equals = go 0 where
  go :: Int -> Term -> Term -> IO Bool

  -- Type
  go d (Term Typ) (Term Typ) = return
    True

  -- Kind
  go d (Term Kin) (Term Kin) = return
    True

  -- Variable
  go d (Term (Var aNam)) (Term (Var bNam)) = return $
    aNam == bNam

  -- Path
  go d (Term (Path aNam)) (Term (Path bNam)) = return $
    aNam == bNam

  -- Forall
  go d (Term (All aEra aNam aTyp aBod)) (Term (All bEra bNam bTyp bBod)) = do
    let var = Term (Var (show d))
    g0 <- go d aTyp bTyp
    g1 <- join $ go (d+1) <$> aBod var <*> bBod var
    return $ aEra == bEra && g0 && g1

  -- Lambda
  go d (Term (Lam aEra aNam aTyp aBod)) (Term (Lam bEra bNam bTyp bBod)) = do
    let var = Term (Var (show d))
    g0 <- go d aTyp bTyp
    g1 <- join $ go (d+1) <$> aBod var <*> bBod var
    return $ aEra == bEra && g0 && g1

  -- Application
  go d (Term (App aEra aFun aArg)) (Term (App bEra bFun bArg)) = do 
    g0 <- go d aFun bFun
    g1 <- go d aArg bArg
    return $ aEra == bEra && g0 && g1

  -- Local definition
  go d (Term (Let aNam aVal aArg)) (Term (Let bNam bVal bArg)) = do
    let var = Term (Var (show d))
    g0 <- go d aVal bVal
    g1 <- join $ go d <$> aArg var <*> bArg var
    return $ g0 && g1

  -- Dependent intersection
  go d (Term (Dep aNam aFty aSty)) (Term (Dep bNam bFty bSty)) = do
    let var = Term (Var (show d))
    g0 <- go d aFty bFty
    g1 <- join $ go d <$> aSty var <*> bSty var
    return $ g0 && g1

  -- Dependent intersection proof
  go d (Term (Bis aNam aFst aSty aSnd)) (Term (Bis bNam bFst bSty bSnd)) = do
    let var = Term (Var (show d))
    g0 <- go d aFst bFst
    g1 <- join $ go d <$> aSty var <*> bSty var
    g2 <- go d aSnd bSnd
    return $ g0 && g1 && g2

  -- First projection
  go d (Term (Fst aBis)) (Term (Fst bBis)) =
    go d aBis bBis

  -- Bis projection
  go d (Term (Snd aBis)) (Term (Snd bBis)) =
    go d aBis bBis

  -- Equality
  go d (Term (Eql aFst aSnd)) (Term (Eql bFst bSnd)) =
    (&&) <$> go d aFst bFst <*> go d aSnd bSnd

  -- Reflexivity
  go d (Term (Rfl aVal aRet)) (Term (Rfl bVal bRet)) =
    (&&) <$> go d aVal aRet <*> go d bVal bRet

  -- Symmetry
  go d (Term (Sym aEql)) (Term (Sym bEql)) =
    go d aEql bEql

  -- Cast
  go d (Term (Cst aEql aFst aSnd)) (Term (Cst bEql bFst bSnd)) = do
    g0 <- go d aEql bEql
    g1 <- go d aFst bFst
    g2 <- go d aSnd bSnd
    return $ g0 && g1 && g2

  -- Rewrite
  go d (Term (Rwt aNam aEql aTyp aVal)) (Term (Rwt bNam bEql bTyp bVal)) = do
    let var = Term (Var (show d))
    g0 <- go d aEql bEql
    g1 <- join $ go d <$> aTyp var <*> bTyp var
    g2 <- go d aVal bVal 
    return $ g0 && g1 && g2
       
  -- Different terms
  go d a b = return
    False

-- Checks if a term is either Typ or Kin
isSort :: Term -> Bool
isSort (Term Typ) = True
isSort (Term Kin) = True
isSort _          = False

-- Checks if a term is Err
isErr :: Term -> Bool
isErr (Term Err) = True
isErr _          = False