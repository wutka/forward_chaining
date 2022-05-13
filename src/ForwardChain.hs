module ForwardChain where

import Lexer
import Data.Either
import Data.Maybe
import Data.List
import qualified Data.Map as Map

-- A value in a rule can be a constant of a variable
data RuleValue =
    RuleConstant String
  | RuleVariable String
  deriving (Eq)

instance Show RuleValue where
  show (RuleConstant c) = showSymbol c
  show (RuleVariable v) = "?"++v
  
-- An assertion has a name and a list of constant values
data Assertion =
  Assertion String [String]
  deriving (Eq)

instance Show Assertion where
  show (Assertion name constants) =
    name ++ " " ++ unwords (map showSymbol constants) ++ "."

-- An antecedent can be a simple named expression, an
-- And expression with two antecedents, or an Or expression
-- with two antecedents
data Antecedent =
    SimpleExpr String [RuleValue]
  | AndExpr Antecedent Antecedent
  | OrExpr Antecedent Antecedent
  deriving (Eq)

instance Show Antecedent where
  show (SimpleExpr name values) =
    name ++ " " ++ unwords (map show values)
  show (AndExpr a1 a2) =
    "(" ++ show a1 ++ ") and (" ++ show a2 ++ ")"
  show (OrExpr a1 a2) =
    "(" ++ show a1 ++ ") or (" ++ show a2 ++ ")"
    
-- A consequent has a name and a list of values
data Consequent =
    Consequent String [RuleValue]
  deriving (Eq)

instance Show Consequent where
  show (Consequent name values) =
    name ++ " " ++ unwords (map show values)
    
-- A rule has an antecedent and a list of consequents
data Rule =
    Rule Antecedent [Consequent]
  deriving (Eq)

instance Show Rule where
  show (Rule antecedent consequents) =
    show antecedent ++ " :- " ++ intercalate ", " (map show consequents) ++ "."

-- The knowledge base contains all the known assertions and rules
data KnowledgeBase =
    KnowledgeBase [Assertion] [Rule] [Assertion] Bool
  deriving (Show, Eq)

-- VarMap is used to map variable names to values
type VarMap = Map.Map String String

data SearchContext =
  SearchContext VarMap KnowledgeBase
  deriving (Show, Eq)

isConstantValue :: RuleValue -> Bool
isConstantValue (RuleConstant _) = True
isConstantValue _ = False

isConstantConsequent :: Consequent -> Bool
isConstantConsequent (Consequent _ vs) = all isConstantValue vs

constantValue :: RuleValue -> String
constantValue (RuleConstant s) = s
constantValue _ = fail "Tried to extract constant from variable"

-- It is handy to convert an assertion into a consequent (with no
-- variables) so the same matching algorithms can be used
assertionToConsequent :: Assertion -> Consequent
assertionToConsequent (Assertion name vs) =
  Consequent name (map RuleConstant vs)

-- If a rule contains a variable, it matches an assertion value
-- automatically. Otherwise, they only match if the assertion
-- value and the rule value are the same constant
assertionValueMatch :: String -> RuleValue -> Bool
assertionValueMatch s (RuleConstant s2) = s == s2
assertionValueMatch _ (RuleVariable _) = True

-- Returns true if a consequent matches an assertion
matchAssertion :: Consequent -> Assertion -> Bool
matchAssertion (Consequent cName cs) (Assertion aName as) =
  -- Make sure the names match, and then make sure all values match
  aName == cName && length cs == length as && and (zipWith assertionValueMatch as cs)

-- For two consequent values to match, if either consequent contains
-- a variable, they match, otherwise, if they are both constants,
-- the constants have to match
consequentValueMatch :: RuleValue -> RuleValue -> Bool
consequentValueMatch (RuleConstant c1) (RuleConstant c2) = c1 == c2
consequentValueMatch _ _ = True

-- Returns true if two consequents have the same name and they
-- match in places where they each have a constant
matchConsequent :: Consequent -> Consequent -> Bool
matchConsequent (Consequent cName1 cs1) (Consequent cName2 cs2) =
  cName1 == cName2 && length cs1 == length cs2 &&  and (zipWith consequentValueMatch cs1 cs2)

-- A consequent matches a rule if it matches any of the rule's consequents
ruleMatch :: Consequent -> Rule -> Bool
ruleMatch c (Rule _ cs) =
  any (matchConsequent c) cs

-- Given a map and two rule values, if the first value is a variable
-- and the second value is a constant, update the map to map the
-- variable to the constant value
updateVarMapWithPair :: (RuleValue, RuleValue) -> VarMap -> VarMap
updateVarMapWithPair (RuleConstant _, RuleConstant _) vm = vm
updateVarMapWithPair (RuleConstant s, RuleVariable v) vm = Map.insert v s vm
updateVarMapWithPair (RuleVariable v, RuleConstant s) vm =
    Map.insert v s vm
updateVarMapWithPair (RuleVariable _, RuleVariable _) vm = vm

-- Compare two consequents and for all the variables in the first one
-- where the corresponding value in the second consequent is a constant,
-- update the map to map the variable to that constant value
updateVarMap :: VarMap -> Consequent -> Consequent -> VarMap
updateVarMap vm (Consequent _ c1) (Consequent _ c2) = foldr updateVarMapWithPair vm (zip c1 c2)

-- If a value is a variable, see if it is in the map, and if so, replace
-- it with a constant, otherwise leave the variable intact
applyMapToValue :: VarMap -> RuleValue -> RuleValue
applyMapToValue vm rc@(RuleConstant s) = rc
applyMapToValue vm rv@(RuleVariable v) =
  maybe rv RuleConstant $ Map.lookup v vm

-- Replace any variables in a consequent that have mappings in
-- the variable map
applyMapToConsequent :: Consequent -> VarMap -> Consequent
applyMapToConsequent (Consequent name v) vm = Consequent name (map (applyMapToValue vm) v)

applyMapToAntecedent :: Antecedent -> VarMap -> Antecedent
applyMapToAntecedent (SimpleExpr name v) vm = SimpleExpr name (map (applyMapToValue vm) v)
applyMapToAntecedent (AndExpr a1 a2) vm = AndExpr (applyMapToAntecedent a1 vm)
                                                  (applyMapToAntecedent a2 vm)
applyMapToAntecedent (OrExpr a1 a2) vm = OrExpr (applyMapToAntecedent a1 vm)
                                                (applyMapToAntecedent a2 vm)
                                         
-- Attempts to prove an antecedent by examining the knowledge base
proveAntecedent :: KnowledgeBase -> Antecedent -> VarMap ->  [VarMap]

-- If the antecedent is a simple expression, convert it to a consequent
-- and then attempt to prove the consequent against the knowledge base
proveAntecedent (KnowledgeBase _ _ workingAssertions _) (SimpleExpr name v) vm =
  map (updateVarMapWithAssertion vm consequent) matchingAssertions
  where
    consequent = Consequent name v
    matchingAssertions = filter (matchAssertion consequent) workingAssertions
    updateVarMapWithAssertion v c a = updateVarMap v c (assertionToConsequent a)

-- If the antecedent is an AndExpr, first prove the left antecedent. This
-- will result in a list of variable mappings. For each of these mappings,
-- apply the mapping to the second antecedent, and then try to prove
-- the second antecedent.
-- For example, given the antecedent is-foo ?x and is-bar ?y and
-- two matching assertions  is-foo "baz" and is-foo "quux", there
-- would be two maps returned in proving the first assertion, one mapping
-- ?x to "baz" and one mapping ?x to "quux". Then, this function will
-- look for all results for is-bar "baz" and then for is-bar "quux".
proveAntecedent kb (AndExpr a1 a2) vm =
  concatMap (proveAntecedentAnd2 kb a2) a1Result
  where
    a1Result = proveAntecedent kb a1 vm

-- Unlike the AndExpr, for the OrExpr we just get all the matches for
-- the left antecedent and all the matches for the right antecedent
-- and don't need to update the right with results from the left.
proveAntecedent kb (OrExpr a1 a2) vm =
  proveAntecedent kb a1 vm ++ proveAntecedent kb a2 vm

-- Apply the incoming map to the second antecedent and try to
-- prove the second antecedent
proveAntecedentAnd2 :: KnowledgeBase -> Antecedent -> VarMap -> [VarMap]
proveAntecedentAnd2 kb a2  vm =
  proveAntecedent kb (applyMapToAntecedent a2 vm) vm

addConsequent :: VarMap -> KnowledgeBase -> Consequent -> KnowledgeBase
addConsequent vm kb@(KnowledgeBase a r working changed) c =
  if notElem newAssertion working then
    KnowledgeBase a r (newAssertion:working) True
  else
    kb
  where
    newAssertion = consequentToAssertion (applyMapToConsequent c vm)
    consequentToAssertion (Consequent name vs) = Assertion name (map constantValue vs)
    
addConsequents :: [Consequent] -> KnowledgeBase -> VarMap -> KnowledgeBase
addConsequents cs kb vm =
  foldl' (addConsequent vm) kb cs
  
updateKnowledgeBaseRules :: KnowledgeBase -> [Rule] -> KnowledgeBase
updateKnowledgeBaseRules kb [] = kb
updateKnowledgeBaseRules kb ((Rule antecedent consequents):rs) =
  updateKnowledgeBaseRules newKB rs
  where
    newKB = foldl' (addConsequents consequents) kb (proveAntecedent kb antecedent Map.empty)
    
updateKnowledgeBase' :: KnowledgeBase -> KnowledgeBase
updateKnowledgeBase' kb@(KnowledgeBase _ rules _ _) =
  if changed then
    updateKnowledgeBase' (KnowledgeBase a r w False)
  else
    newKB
  where
    newKB@(KnowledgeBase a r w changed) = updateKnowledgeBaseRules kb rules

updateKnowledgeBase (KnowledgeBase a c _ _) =
  updateKnowledgeBase' (KnowledgeBase a c a False)
  
proveQuery :: Consequent -> KnowledgeBase -> [Assertion]
proveQuery c (KnowledgeBase _ _ working _) =
  filter (matchAssertion c) working

