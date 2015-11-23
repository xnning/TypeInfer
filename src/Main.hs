{-# LANGUAGE OverloadedStrings #-}

module Main where

import qualified Data.Text as T
import           System.Console.Haskeline

import           Language.Java.Pretty
import           Parser
import           PrettyPrint
import           Syntax (ClassTag(..))
import           TypeCheck


main :: IO ()
main = runInputT defaultSettings loop
  where
    loop :: InputT IO ()
    loop = do
      minput <- getInputLine "pts> "
      case minput of
        Nothing   -> return ()
        Just ""   -> loop
        Just ":q" -> return ()
        Just cmds -> dispatch cmds
    dispatch :: String -> InputT IO ()
    dispatch cmds =
      let e@(cmd:progm) = words cmds
      in case cmd of
        -- ":clr" -> do
        --   outputStrLn "Environment cleaned up!"
        --   loop [] [] -- initalBEnv initalEnv
        -- ":env" -> do
        --   outputStrLn $ "Typing environment: " ++ show env
        --   outputStrLn $ "Binding environment: " ++ show (map fst benv)
        --   loop benv env
        -- ":add" -> delegate progm "Command parse error - :add name type" $
        --   \name xs -> do
        --     outputStrLn "Added!"
        --     loop benv (extend (name, Logic) (head xs) env)
        -- ":let" -> delegate progm "Command parse error - :let name expr" $
        --   \name xs -> do
        --     outputStrLn "Added new term!"
        --     loop ((name, head xs) : benv) env
        ":e" -> processCMD progm $
          \xs -> do
            let xs' = eval xs
            outputStrLn ("\n--- Evaluation result ---\n\n" ++ (T.unpack . showExpr $ xs') ++ "\n")
            loop

        -- TODO: refactor :tp and :tl
        ":t" -> processCMD progm $
          \xs -> do
            case typecheck xs of
              Left err  -> outputStrLn . T.unpack $ err
              Right typ -> outputStrLn ("\n--- Typing result ---\n\n" ++ (T.unpack . showExpr $ typ) ++ "\n")
            loop

        _ -> processCMD e $
          \xs -> do
            outputStrLn ("\n--- Pretty printing ---\n\n" ++ (T.unpack . showExpr $ xs) ++ "\n")
            loop
      where
        processCMD expr func =
          case parseExpr . unwords $ expr of
            Left err -> do
              outputStrLn . show $ err
              loop
            Right xs -> func xs
