module MetaProg.ElabCtor

import Language.Reflection
import Language.Reflection.Utils
import Pruviloj.Core

%language ElabReflection

%default total

applyCtor : TTName -> Nat -> Elab () -> Elab ()
applyCtor cn argCount tac =
  do holes <- apply (Var cn) (replicate argCount True)
     solve
     for_ holes $ \h => inHole h tac

byConstructors : Nat -> List TTName -> Elab () -> Elab ()
byConstructors Z _ _ =
  fail [TextPart "Search failed because the max depth was reached."]
byConstructors (S k) tns tac =
  case headName !goalType of
    Nothing => tac
    Just n =>
      if not (n `elem` tns)
      then tac
      else do ctors <- constructors <$> lookupDatatypeExact n
              choice (map (\(cn, args, _) =>
                            applyCtor cn
                                      (length args)
                                      (byConstructors k tns tac))
                          ctors)

autoCtor : Elab ()
autoCtor = byConstructors 1000 [`{Unit}, `{Pair}, `{Either}] nope
  where
  nope : Elab ()
  nope = do g <- snd <$> getGoal
            fail [ NamePart `{autoCtor}, TextPart "can’t solve the goal",
                   TermPart g ]

test1 : the Type ()
test1 = %runElab autoCtor

test2 : the Type ((), ())
test2 = %runElab autoCtor

test3 : Either Void ()
test3 = %runElab autoCtor

test4 : Either Void (Either Void ())
test4 = %runElab autoCtor

--test5 : Either Void (Either Void Void)
--test5 = %runElab autoCtor
