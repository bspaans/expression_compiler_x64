-- | A self contained expression to machine code translator.
--

module Main where

import Control.Arrow
import Control.Applicative
import Control.Monad
import Data.Char
import Data.List (intercalate)
import System.Environment (getArgs)
import System.IO
import System.Process

-- | Parser combinators
--
newtype Parser a b = Parser { parse :: [a] -> [(b, [a])] } 

instance Functor (Parser a) where
  fmap f x = Parser (map (first f) . parse x)

instance Monad (Parser a) where
  return = pure 
  x >>= f = Parser (concatMap (uncurry (parse . f)) . parse x)

instance Applicative (Parser a) where 
  pure = succeed
  (<*>) = liftM2 ($) 

instance Alternative (Parser a) where
  empty = Parser (\cs -> [])
  p <|> q = Parser (\cs -> parse p cs ++ parse q cs)

infixr 3 <<|>

(<<|>) :: Parser a b -> Parser a b -> Parser a b
p <<|> q = Parser (\cs -> let r = parse p cs in if null r then parse q cs else r)

satisfy :: (a -> Bool) ->  Parser a a
satisfy p = Parser (satisfy')
  where satisfy' [] = []
        satisfy' (c:cs) = if p c then [(c, cs)] else []

symbol :: Eq a => a -> Parser a a
symbol = satisfy . (==)

token :: Eq a => [a] -> Parser a [a]
token [] = succeed []
token (c:cs) = (:) <$> symbol c <*> token cs

succeed :: a -> Parser b a
succeed x = Parser (\cs -> [(x, cs)]) 

many1 :: Parser a b -> Parser a [b]
many1 p = (:) <$> p <*> many p

choice :: [Parser s a] -> Parser s a
choice = foldr (<|>) empty

strictChoice :: [Parser s a] -> Parser s a
strictChoice = foldr (<<|>) empty

greedy p =  (:) <$> p <*> greedy p <<|> succeed []
greedy1 p = (:) <$> p <*> greedy p

chainr :: Parser s a -> Parser s (a -> a -> a) -> Parser s a
chainr pe po = h <$> many (j <$> pe <*> po) <*> pe
  where j x op = (x `op`)
        h fs x = foldr ($) x fs

chainl :: Parser s a -> Parser s (a -> a -> a) -> Parser s a
chainl pe po = h <$> pe <*> many (j <$> po <*> pe)
  where j op x = (`op` x)
        h x fs = foldl (flip ($)) x fs

eof = Parser (\cs -> if null cs then [((), [])] else [])

digit    = satisfy isDigit
space    = satisfy isSpace

natural = greedy1 digit
whiteSpace = greedy space


-- | The expression lexer
--
data Token = IntVal Int | Plus | Min | Mul | Div 
           | POpen | PClose deriving (Show, Eq)

operators = [('+', Plus), ('-', Min), ('*', Mul), ('/', Div), ('(', POpen), (')', PClose)]

operator :: Parser Char Token
operator = strictChoice (map (\(a,b) -> b <$ symbol a) operators)

tokens :: Parser Char [Token]
tokens = many (whiteSpace *> (operator <|> IntVal . read <$> natural) 
                          <* whiteSpace)

tokenize :: String -> Maybe [Token]
tokenize s = case parse (tokens <* eof) s of 
               [] -> Nothing
               (c:cs) -> Just (fst c)


-- | The expression parser
--
data Expr = SimpleVal Token | Oper Token Expr Expr deriving (Show, Eq)

pExpr :: Parser Token Expr
pExpr = pOper 

pOper :: Parser Token Expr
pOper = foldr gen pSimpleVal [[Plus, Min], [Mul, Div]]
  where gen op p = chainl p (Oper <$> choice (map symbol op))

pSimpleVal :: Parser Token Expr
pSimpleVal = SimpleVal <$> satisfy isIntVal <|> symbol POpen *> pExpr <* symbol PClose 
  where isIntVal (IntVal _) = True 
        isIntVal _          = False


parseExpr :: String -> Maybe Expr
parseExpr s = tokenize s >>= p
  where p ts = case parse (pExpr <* eof) ts of 
                 [] -> Nothing
                 (c:cs) -> Just (fst c)

-- | An algebra and fold for the Expressions
--
type ExprAlgebra e = (Int -> e, Token -> e -> e -> e)

foldExpr :: ExprAlgebra e -> Expr -> e
foldExpr (simple, oper) = f
  where f (SimpleVal (IntVal i)) = simple i
        f (Oper o e1 e2) = oper o (f e1) (f e2)

-- | An evaluator for Expr
--
evalExpr :: Expr -> Int
evalExpr = foldExpr (simple, oper)
  where simple i = i
        oper Plus = (+)
        oper Min  = (-)
        oper Mul = (*)
        oper Div = div

eval :: String -> Maybe Int
eval s = evalExpr <$> parseExpr s 
     

-- | Compiling to a stack machine
--
data Instr = Push Int | AddI  | SubI | MulI | DivI deriving (Show, Eq)

operInstr = [(Plus, AddI), (Min, SubI), (Mul, MulI), (Div, DivI)]

compileExpr :: Expr -> [Instr]
compileExpr = foldExpr (simple, oper)
  where simple = (:[]) . Push 
        oper o e1 e2 = concat[e1, e2, maybe [] (:[]) (lookup o operInstr)]

runInstr :: [Instr] -> Int
runInstr = runStack []
  where runStack (c:cs) [] = c
        runStack st (Push i:is) = runStack (i:st) is
        runStack (e2:e1:st) (AddI:is) = runStack (e1 + e2 : st) is
        runStack (e2:e1:st) (SubI:is) = runStack (e1 - e2 : st) is
        runStack (e2:e1:st) (MulI:is) = runStack (e1 * e2 : st) is
        runStack (e2:e1:st) (DivI:is) = runStack (e1 `div` e2 : st) is

test :: String -> Bool
test s = (runInstr . compileExpr <$> p) == (evalExpr <$> p)
  where p = parseExpr s


-- | Compiling to X86
--
data Register = Eax | Ebx | Esp | Ebp
data VR = Value Int | Register Register

data X86Instr = 
           Popl VR
         | Pushl VR
         | Addl VR Register
         | Subl VR Register
         | Mull VR Register
         | Divl VR Register
         | Movl VR Register
         | Leave | Ret
	 | Label String

compileExprToX86 :: Expr -> String 
compileExprToX86 expr = ".text\n" ++ (printX86 $ [Label "main", Pushl (Register Ebp), 
                                    Movl (Register Esp) Ebp] ++ compiled ++ [Leave, Ret])
  where simple v = [Pushl $ Value v]
        oper Plus = o Addl
        oper Min = o Subl
        oper Mul = o Mull
        oper Div = o Divl
        o instr e1 e2 = e1 ++ e2 ++ [Popl (Register Ebx), Popl (Register Eax), 
	                             instr (Register Ebx) Eax, Pushl (Register Eax)]
	compiled = foldExpr (simple, oper) expr

printX86 :: [X86Instr] -> String
printX86 = unlines . map p
  where p Leave = "  leave"
        p Ret   = "  ret"
	p (Popl vr) = "  pop " ++ printVR vr
	p (Pushl vr) = "  push " ++ printVR vr
	p (Addl vr r) = "  addl " ++ printVR vr ++ ", " ++ printReg r
	p (Subl vr r) = "  subl " ++ printVR vr ++ ", " ++ printReg r
	p (Divl vr r) = "  divl " ++ printVR vr ++ ", " ++ printReg r
	p (Mull vr r) = "  imull " ++ printVR vr ++ ", " ++ printReg r
        p (Movl vr r) = "  movl " ++ printVR vr ++ ", " ++ printReg r
	p (Label l) = ".globl " ++ l ++ "\n" ++ l ++ ":"

printVR :: VR -> String
printVR (Value v) = "$" ++ show v
printVR (Register r) = printReg r

printReg :: Register -> String 
printReg Eax = "%eax"
printReg Ebx = "%ebx"
printReg Ebp = "%ebp"
printReg Esp = "%esp"


-- Compile string to an executable using gcc.
--
compileString :: String -> String
compileString s = maybe (error "Invalid expression") id (compileExprToX86 <$> parseExpr s)

compile :: String -> IO ()
compile s = do writeFile "expr.s" $ compileString s
               h <- runCommand "gcc ./expr.s -o expr"
               exit <- waitForProcess h
               putStrLn $ "gcc exited with code " ++ show exit

main :: IO ()
main = do args <- getArgs 
          compile (intercalate " " args)
