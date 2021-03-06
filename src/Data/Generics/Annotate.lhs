> {-# LANGUAGE ImplicitParams #-}

> module Data.Generics.Annotate where

> import Language.Haskell.TH.Syntax
> import Language.Haskell.TH.Quote
> import Language.Haskell.Exts.Parser
> import qualified Language.Haskell.Exts as Exts

> import Language.Haskell.Meta

> import Data.Maybe
> import Data.List((\\), nub)

> import Data.Generics.Uniplate.Operations 
> import Data.Generics.Uniplate.Data

> import Debug.Trace

------------------------------------------------------------
Primary annotation macro
-------------------------------------------------------------

> annotate = QuasiQuoter { quoteExp = err, quoteType = err, quotePat = err, 
>                          quoteDec = \s -> do -- Pull in the origin file and extract its extensions
>                                              loc <- location
>                                              f <- runIO $ readFile (loc_filename loc) 
>                                              let exts = case (Exts.readExtensions f) of
>                                                           Nothing -> []
>                                                           Just exts' -> exts'
>                                              -- Parse the annotation fragment with these extensions
>                                              let mode = Exts.ParseMode { parseFilename = "", extensions = exts,
>                                                                     ignoreLanguagePragmas = False,
>                                                                     ignoreLinePragmas = False, fixities = Nothing }
>                                              case (parseModuleWithMode mode s) of
>                                                ParseOk (Exts.Module _ _ _ _ _ _ decls) -> annotateDecs (fmap toDec decls)
>                                                ParseFailed loc mesg -> error (show loc ++ mesg) }

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

Calculates if a type contains an annotated type 

> hasAnnotation :: (?tnames :: [Name]) => Type -> Bool
> hasAnnotation (ConT n) | (elem n ?tnames) = True
> hasAnnotation t = False
 
Compute free variables in a type

> freeVars :: Type -> [Name]
> freeVars t = nub $ (([v | VarT v <- universeBi t]) \\ [v | PlainTV v <- universeBi t]) \\ [v | KindedTV v _ <- universeBi t]

Add "ForAll" wrappers on those types (top-level) which have annotations added to them
Bit of a hack at the moment really, just trying to see if useful approach

> paramTypForall :: (?tnames :: [Name], ?pname :: Name) => Type -> Type 
> paramTypForall t | (para (\t -> \ts -> (or ts) || (hasAnnotation t)) t) =
>                      case t of
>                        (ForallT vars ctxt typ) -> ForallT ((PlainTV ?pname):vars) ctxt typ
>                        _                       -> ForallT (map PlainTV (freeVars t)) [] t
> paramTypForall t = t

Annotate expressions if in the scope of the annotation block

> paramExp :: (?conNames :: [Name]) => Exp -> Exp
> paramExp (ConE n) | (elem n ?conNames) = AppE (ConE n) (VarE (mkName "undefined")) -- AppE (ConE n) (TupE []) -- 
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
> paramDec (InstanceD ctxt typ decs) = InstanceD (transformBi (paramTyp (VarT ?pname)) ctxt) (transform (paramTyp (VarT ?pname)) $ typ) (map paramDec decs)
> paramDec d = (transformBi paramExp) . (transformBi paramPat) . (descendBi paramTypForall) . (transformBi (paramTyp (VarT ?pname))) $ d

Get a list of constructor names declared in the block

------------------------------------------------------------
Secondary annotation macro - still needs some work
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
>                         in do pname <- newName "p"
>                               let ?pname = pname in either error (mapM paramFroms) (parseDecs rest)

Decide when to annotate something

> doAnnotate :: (?fromModules :: [String]) => Name -> (String -> Q (Maybe Name)) -> a -> a -> Q a
> doAnnotate n lookup false true = do n' <- lookup (nameBase n)
>                                     return $ case n' >>= nameModule of
>                                                Nothing -> false
>                                                Just m -> if (m `elem` ?fromModules) then true
>                                                          else false

> paramTypFrom :: (?pname :: Name, ?fromModules :: [String]) => Type -> Q Type
> paramTypFrom (ConT n) | (nameBase n) == "()" = return $ TupleT 0 -- Weird fix to do with () constructor
> paramTypFrom (ConT n) = doAnnotate n lookupTypeName (ConT n) (AppT (ConT n) (TupleT 0))  -- (AppT (ConT n) (VarT ?pname))
> paramTypFrom t = return t

> paramExpFrom :: (?pname :: Name, ?fromModules :: [String]) => Exp -> Q Exp
> paramExpFrom (ConE n) = doAnnotate n lookupValueName (ConE n)  (AppE (ConE n) (TupE [])) -- (AppE (ConE n) (VarE $ mkName "undefined"))
> paramExpFrom e = return e

> paramPatFrom :: (?pname :: Name, ?fromModules :: [String]) => Pat -> Q Pat
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

                         >>= (descendBiM paramTypForallFrom)

 doAnnotat :: (?fromModules :: [String]) => Type -> Q Bool
 doAnnotat (ConT n) = do n' <- lookupTypeName (nameBase n)
                         return $ case n' >>= nameModule of
                                     Nothing -> False
                                     Just m -> if (m `elem` ?fromModules) then True
                                               else False
 doAnnotat t = return False

 paramTypForallFrom :: (?pname :: Name, ?fromModules :: [String]) => Type -> Q Type -- bit of a hack at the moment really, just trying to see if useful approach
 paramTypForallFrom t = do cond <- (para (\t -> \ts -> do cond <- doAnnotat t
                                                          conds <- sequence ts
                                                          return $ ((or conds) || cond)) t)
                           return $ if cond then ForallT [PlainTV ?pname] [] t else t


(or ts) || (hasAnnotation t)) t) then ForallT [PlainTV ?pname] [] t
                    else t
