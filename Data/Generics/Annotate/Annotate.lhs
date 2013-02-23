> {-# LANGUAGE ImplicitParams #-}

> module Data.Generics.Annotate where

> import Language.Haskell.TH.Syntax
> import Language.Haskell.TH.Quote
> import Language.Haskell.Meta

> import Data.Maybe

> import Data.Generics.Uniplate.Operations 
> import Data.Generics.Uniplate.Data

------------------------------------------------------------
Primary annotation macro
-------------------------------------------------------------

> annotate = QuasiQuoter { quoteExp = err, quoteType = err, quotePat = err, 
>                          quoteDec = \s -> either error annotateDecs (parseDecs s) }

Annotate declarations

> annotateDecs :: [Dec] -> Q [Dec]
> annotateDecs decs = let dataName (DataD _ name _ _ _) = Just name 
>                         dataName _                    = Nothing
>                         dataCons (DataD _ _ _ cons _) = cons
>                         dataCons _                    = []
>                     in do pname <- newName "p"
>                           let ?pname = pname
>                           let ?tnames = mapMaybe dataName decs
>                           let ?conNames = concatMap (concatMap (para conName) . dataCons) decs
>                           return $ map paramDec decs                        

> conName (NormalC cname _) cs = cname : (concat cs)
> conName (RecC cname _) cs = cname : (concat cs)
> conName (InfixC _ cname _) cs = cname : (concat cs)
> conName (ForallC _ _ c) cs = (conName c cs) ++ (concat cs)

> err = const $ error "Only applies to data type definitions"

Annotate types if in the scope of the annotation
(this may be with () for usages, or VarT for declarations)

> paramTyp :: (?tnames :: [Name]) => Type -> Type -> Type
> paramTyp ty (ConT n) | (elem n ?tnames) = AppT (ConT n) ty
> paramTyp _ t = t

Annotate expressions if in the scope of the annotation block

> paramExp :: (?conNames :: [Name]) => Exp -> Exp
> paramExp (ConE n) | (elem n ?conNames) = AppE (ConE n) (TupE [])
> paramExp e = e

Annotate patterns if in the scope of the annotation block

> paramPat :: (?conNames :: [Name]) => Pat -> Pat
> paramPat (ConP n ps) | (elem n ?conNames) = ConP n (WildP:ps)
> paramPat p = p

Annotate data constructors in data declarations

> paramCon :: (?tnames :: [Name], ?pname :: Name, ?tname :: Name) => Con -> Con 
> paramCon (NormalC cname tys) =
>                 let tys' = map (\(s, t) -> (s, transform (paramTyp (VarT ?pname)) t)) tys
>                 in NormalC cname ((NotStrict, VarT ?pname):tys')
> paramCon (RecC cname vtys) =
>                 let newField = (mkName $ (nameBase ?tname) ++ "_param", NotStrict, VarT ?pname)
>                 in RecC cname (newField:vtys)
> paramCon (InfixC t1 cname t2) = NormalC cname [t1, t2, (NotStrict, VarT ?pname)]
> paramCon (ForallC tyvars ctxt con) = ForallC tyvars ctxt (paramCon con)

Annotate data type declarations and trigger annotations 
within other declarations of types, expressions, and patterns

> paramDec :: (?tnames :: [Name], ?pname :: Name, ?conNames :: [Name]) => Dec -> Dec
> paramDec (DataD ctxt name ty cons names) =
>              let ?tname = name
>              in DataD ctxt name ((PlainTV ?pname):ty) (map paramCon cons) names
> paramDec d = (transformBi paramExp) . (transformBi paramPat) . (transformBi (paramTyp (TupleT 0))) $ d

Get a list of constructor names declared in the block


------------------------------------------------------------
Secondary annotation macro
-------------------------------------------------------------

Annotate only type/data constructors from modules specified in the format {Module1, Module2}

> annotateFrom = QuasiQuoter { quoteExp = err, quoteType = err, quotePat = err, 
>                              quoteDec = annotateDecsParam }

Parameterised declaration annotations (parameterised by modules)

> annotateDecsParam s = let parse True []      = error "Block finished before '}'"
>                           parse False []     = ("","")
>                           parse m (s:ss)     | s == ' ' = parse m ss
>                           parse True (s:ss)  | s == '}' = ("", ss)
>                                              | otherwise = let (par, rest) = parse True ss
>                                                            in (s:par, rest)
>                           parse False (s:ss) | s == '{' = parse True ss
>                                              | otherwise = error "Expecting '{'"
>                           (paramsString, rest) = parse False s
>                       in 
>                         let ?fromModules = groupBy (==',') paramsString
>                         in either error (mapM paramFroms)(parseDecs rest)

Decide when to annotate something

> doAnnotate :: (?fromModules :: [String]) => Name -> (String -> Q (Maybe Name)) -> a -> a -> Q a
> doAnnotate n lookup false true = do n' <- lookup (nameBase n)
>                                     return $ case n' >>= nameModule of
>                                                Nothing -> false
>                                                Just m -> if (m `elem` ?fromModules) then true
>                                                          else false

> paramTypFrom :: (?fromModules :: [String]) => Type -> Q Type
> paramTypFrom (ConT n) | (nameBase n) == "()" = return $ TupleT 0 -- Weird fix to do with () constructor
> paramTypFrom (ConT n) = doAnnotate n lookupTypeName (ConT n) (AppT (ConT n) (TupleT 0)) 
> paramTypFrom t = return t

> paramExpFrom :: (?fromModules :: [String]) => Exp -> Q Exp
> paramExpFrom (ConE n) = doAnnotate n lookupValueName (ConE n) (AppE (ConE n) (TupE []))
> paramExpFrom e = return e

> paramPatFrom :: (?fromModules :: [String]) => Pat -> Q Pat
> paramPatFrom (ConP n ps) = doAnnotate n lookupValueName (ConP n ps) (ConP n (WildP:ps))
> paramPatFrom p = return p

> groupBy :: (a -> Bool) -> [a] -> [[a]]
> groupBy f xs = groupBy' f xs []
> groupBy' f [] r = [r]
> groupBy' f (x:xs) r | f x = (r ++ [x]):(groupBy' f xs [])
>                     | otherwise = groupBy' f xs (r ++ [x])

> paramFroms p = return p >>= (transformBiM paramTypFrom)
>                         >>= (transformBiM paramPatFrom)
>                         >>= (transformBiM paramExpFrom)

