module Main where

import Network
import System.IO
import Text.Printf
import Data.List
import System.Exit
import Control.Monad

server = "irc.freenode.org"
port   = 6667
chan   = "#grumpytest"
nick   = "grumpybot"
 
main = do
    hSetBuffering stdout NoBuffering
    h <- connectTo server (PortNumber (fromIntegral port))
    hSetBuffering h NoBuffering
    write h "NICK" nick
    write h "USER" (nick++" 0 * :tutorial bot")
    write h "JOIN" chan
    listen h False
 
write :: Handle -> String -> String -> IO ()
write h s t = do
    hPrintf h "%s %s\r\n" s t
    printf    "> %s %s\n" s t
 
listen :: Handle -> Bool -> IO ()
listen h hasJoined = do
    t <- hGetLine h
    let s = init t
    putStrLn s
    --putStrLn $ "`" ++ clean s ++ "'"
    joined <- if (clean s) == "End of /NAMES list."
                 then do putStrLn "joined"
                         return True
                 else return hasJoined
    when joined $ if ping s then pong s else eval h (clean s)
    listen h joined
  where
    clean     = drop 1 . dropWhile (/= ':') . drop 1
 
    ping x    = "PING :" `isPrefixOf` x
    pong x    = write h "PONG" (':' : drop 6 x)

eval :: Handle -> String -> IO ()
eval h    "!quit"                = write h "QUIT" ":Exiting" >> exitWith ExitSuccess
eval h x | "!id " `isPrefixOf` x = privmsg h (drop 4 x)
eval h x | nick `isInfixOf` x    = privmsg h "How about no?"
eval _   _                       = return () -- ignore everything else

privmsg :: Handle -> String -> IO ()
privmsg h s = write h "PRIVMSG" (chan ++ " :" ++ s)
