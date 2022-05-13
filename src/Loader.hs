module Loader where

import ForwardChain
import Parser
import Lexer
import Data.Either

makeKnowledgeBase :: [Either Assertion Rule] -> KnowledgeBase
makeKnowledgeBase parsed = KnowledgeBase (lefts parsed) (rights parsed) [] False

loadFile :: String -> IO KnowledgeBase
loadFile filename = do
  contents <- readFile filename
  let parsed = parser (lexer contents)
  return $ makeKnowledgeBase parsed

parseAssertion :: String -> IO Assertion
parseAssertion s = do
  let parsed = parser (lexer $ addPeriod s)
  return $ head (lefts parsed)
  where
    addPeriod s = if last s == '.' then s else s ++ ['.']

parseRule :: String -> IO Rule
parseRule s = do
  let parsed = parser (lexer $ addPeriod s)
  return $ head (rights parsed)
  where
    addPeriod s = if last s == '.' then s else s ++ ['.']
  
parseQuery :: String -> IO Consequent
parseQuery s = do
  let parsed = queryParser (lexer s)
  return parsed
