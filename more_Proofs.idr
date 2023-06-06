module Main

%default total

public export
data Expr : Type where
  Num : Nat -> Expr
  Plus : Expr -> Expr -> Expr
  Times : Expr -> Expr -> Expr
  Minus : Expr -> Expr -> Expr  
%name Expr e

data OP : Type where
  PLUS : OP
  TIMES : OP
  MINUS : OP
%name OP o
  
data Expr' : Type where
  Num' : Nat -> Expr'
  Op : Expr' -> OP -> Expr' -> Expr'
%name Expr' e

exprToExpr' : Expr -> Expr'
exprToExpr' (Num k) = Num' k
exprToExpr' (Plus e1 e2) = Op (exprToExpr' e1) PLUS (exprToExpr' e2)
exprToExpr' (Times e1 e2) = Op (exprToExpr' e1) TIMES (exprToExpr' e2)
exprToExpr' (Minus e1 e2) = Op (exprToExpr' e1) MINUS (exprToExpr' e2)

expr'ToExpr : Expr' -> Expr
expr'ToExpr (Num' k) = Num k
expr'ToExpr (Op e1 PLUS e2) = Plus (expr'ToExpr e1) (expr'ToExpr e2)
expr'ToExpr (Op e1 TIMES e2) = Times (expr'ToExpr e1) (expr'ToExpr e2)
expr'ToExpr (Op e1 MINUS e2) = Minus (expr'ToExpr e1) (expr'ToExpr e2)

exprToExpr'ToExpr : (e : Expr) -> expr'ToExpr (exprToExpr' e) = e
exprToExpr'ToExpr (Num k) = Refl
exprToExpr'ToExpr (Plus  e1 e2) = 
  rewrite exprToExpr'ToExpr e1 
  in cong (Plus e1) (exprToExpr'ToExpr e2)
exprToExpr'ToExpr (Times e1 e2) =
  rewrite exprToExpr'ToExpr e1 
  in cong (Times e1) (exprToExpr'ToExpr e2)
exprToExpr'ToExpr (Minus e1 e2) =
  rewrite exprToExpr'ToExpr e1 
  in cong (Minus e1) (exprToExpr'ToExpr e2)

expr'ToExprToExpr' : (e : Expr') -> exprToExpr' (expr'ToExpr e) = e
expr'ToExprToExpr' (Num' k) = Refl
expr'ToExprToExpr' (Op e1 PLUS  e2) = 
  rewrite expr'ToExprToExpr' e1
  in cong (Op e1 PLUS) $ expr'ToExprToExpr' e2
expr'ToExprToExpr' (Op e1 TIMES e2) =
  rewrite expr'ToExprToExpr' e1
  in cong (Op e1 TIMES) $ expr'ToExprToExpr' e2
expr'ToExprToExpr' (Op e1 MINUS e2) =
  rewrite expr'ToExprToExpr' e1
  in cong (Op e1 MINUS) $ expr'ToExprToExpr' e2

naivePretty : Expr -> String
naivePretty (Num k) = show k
naivePretty (Plus  e1 e2) = naivePretty e1 ++ " + " ++ naivePretty e2
naivePretty (Minus e1 e2) = naivePretty e1 ++ " - " ++ naivePretty e2
naivePretty (Times e1 e2) = naivePretty e1 ++ " * " ++ naivePretty e2

naivePretty' : Expr -> String
naivePretty' (Num k) = show k
naivePretty' (Plus  e1 e2) = "(" ++ naivePretty' e1 ++ ") + (" ++ naivePretty' e2 ++ ")"
naivePretty' (Minus e1 e2) = "(" ++ naivePretty' e1 ++ ") - ("  ++ naivePretty' e2 ++ ")"
naivePretty' (Times e1 e2) = "(" ++ naivePretty' e1 ++ ") * (" ++ naivePretty' e2 ++ ")"

isNum : Expr -> Bool
isNum (Num _ ) = True
isNum _ = False

needsParensR : Expr -> Bool
needsParensR (Num _) = False
needsParensR (Times _ _) = False
needsParensR _ = True

needsParensL : Expr -> Bool
needsParensL (Num k) = False
needsParensL _ = True

public export
implementation Show Expr where
  show (Num k) = show k
  show (Plus  e1 e2) = (if isNum e1 then show e1 else "(" ++ show e1 ++ ")") ++ " + " ++ show e2
  show (Minus e1 e2) = (if isNum e1 then show e1 else "(" ++ show e1 ++ ")") ++ " - " ++ show e2
  show (Times e1 e2) = (if needsParensL e1 then "(" ++ show e1 ++ ")" else show e1) ++
                       " * " ++
                       (if needsParensR e2 then "(" ++ show e2 ++ ")" else show e2)

needsParens : Expr -> Bool
needsParens (Num _) = False
needsParens (Times _ _) = False
needsParens _ = True

public export
pretty : Expr -> String
pretty (Num k) = show k
pretty (Plus  e1 e2) = pretty e1 ++ " + " ++ pretty e2
pretty (Minus e1 e2) = pretty e1 ++ " - " ++ pretty e2
pretty (Times e1 e2) = (if needsParens e1 then "(" ++ show e1 ++ ")" else show e1) ++
                       " * " ++
                       (if needsParens e2 then "(" ++ show e2 ++ ")" else show e2)

public export
data SmallStep : Expr -> Expr -> Type where
  PlusNum : (x, y : Nat) -> SmallStep (Plus (Num x) (Num y)) (Num (x + y))
  MinusNum : (x, y : Nat) -> SmallStep (Minus (Num x) (Num y)) (Num (minus x y))
  TimesNum : (x, y : Nat) -> SmallStep (Times (Num x) (Num y)) (Num (x * y))
  PlusCtxtL : (e1, e1', e2 : Expr) -> SmallStep e1 e1' -> SmallStep (Plus e1 e2) (Plus e1' e2)
  PlusCtxtR : (e1, e2, e2' : Expr) -> SmallStep e2 e2' -> SmallStep (Plus e1 e2) (Plus e1 e2')
  MinusCtxtL : (e1, e1', e2 : Expr) -> SmallStep e1 e1' -> SmallStep (Minus e1 e2) (Minus e1' e2)
  MinusCtxtR : (e1, e2, e2' : Expr) -> SmallStep e2 e2' -> SmallStep (Minus e1 e2) (Minus e1 e2')
  TimesCtxtL : (e1, e1', e2 : Expr) -> SmallStep e1 e1' -> SmallStep (Times e1 e2) (Times e1' e2)
  TimesCtxtR : (e1, e2, e2' : Expr) -> SmallStep e2 e2' -> SmallStep (Times e1 e2) (Times e1 e2')
  
data EvalCtxt : Type where
  Hole : EvalCtxt
  PlusL : EvalCtxt -> Expr -> EvalCtxt
  PlusR : Expr -> EvalCtxt -> EvalCtxt
  MinusL : EvalCtxt -> Expr -> EvalCtxt
  MinusR : Expr -> EvalCtxt -> EvalCtxt
  TimesL : EvalCtxt -> Expr -> EvalCtxt
  TimesR : Expr -> EvalCtxt -> EvalCtxt
%name EvalCtxt c

fillHole : EvalCtxt -> Expr -> Expr
fillHole Hole e = e
fillHole (PlusL c e2) e = Plus (fillHole c e) e2
fillHole (PlusR e1 c) e = Plus e1 (fillHole c e)
fillHole (MinusL c e2) e = Minus (fillHole c e) e2
fillHole (MinusR e1 c) e = Minus e1 (fillHole c e)
fillHole (TimesL c e2) e = Times (fillHole c e) e2
fillHole (TimesR e1 c) e = Times e1 (fillHole c e)

data SmallStep' : Expr -> Expr -> Type where
  PlusNum' : (x, y : Nat) -> SmallStep' (Plus (Num x) (Num y)) (Num (x + y))
  MinusNum' : (x, y : Nat) -> SmallStep' (Minus (Num x) (Num y)) (Num (minus x y))
  TimesNum' : (x, y : Nat) -> SmallStep' (Times (Num x) (Num y)) (Num (x * y))
  CtxtStep : (c : EvalCtxt) -> (e1, e2 : Expr) -> SmallStep' e1 e2 -> SmallStep' (fillHole c e1) (fillHole c e2)

fillHoleStep : (e1, e2 : Expr) -> SmallStep e1 e2 -> 
               (c : EvalCtxt) -> SmallStep (fillHole c e1) (fillHole c e2)
fillHoleStep e1 e2 step Hole = step
fillHoleStep e1 e2 step (PlusL c e) = PlusCtxtL _ _ _ (fillHoleStep e1 e2 step c)
fillHoleStep e1 e2 step (PlusR e c) = PlusCtxtR _ _ _ (fillHoleStep e1 e2 step c)
fillHoleStep e1 e2 step (MinusL c e) = MinusCtxtL _ _ _ (fillHoleStep e1 e2 step c)
fillHoleStep e1 e2 step (MinusR e c) = MinusCtxtR _ _ _ (fillHoleStep e1 e2 step c)
fillHoleStep e1 e2 step (TimesL c e) = TimesCtxtL _ _ _ (fillHoleStep e1 e2 step c)
fillHoleStep e1 e2 step (TimesR e c) = TimesCtxtR _ _ _ (fillHoleStep e1 e2 step c)

step'ToStep : SmallStep' e1 e2 -> SmallStep e1 e2
step'ToStep (PlusNum' x y) = PlusNum x y
step'ToStep (MinusNum' x y) = MinusNum x y
step'ToStep (TimesNum' x y) = TimesNum x y
step'ToStep (CtxtStep c e1 e2 step) = fillHoleStep e1 e2 (step'ToStep step) c

stepToStep' : SmallStep e1 e2 -> SmallStep' e1 e2
stepToStep' (PlusNum x y) = PlusNum' x y
stepToStep' (MinusNum x y) = MinusNum' x y
stepToStep' (TimesNum x y) = TimesNum' x y
stepToStep' (PlusCtxtL e1 e1' e2 step)  = CtxtStep (PlusL Hole e2) e1 e1' (stepToStep' step)
stepToStep' (PlusCtxtR e1 e2 e2' step)  = CtxtStep (PlusR e1 Hole) e2 e2' (stepToStep' step)
stepToStep' (MinusCtxtL e1 e1' e2 step) = CtxtStep (MinusL Hole e2) e1 e1' (stepToStep' step)
stepToStep' (MinusCtxtR e1 e2 e2' step) = CtxtStep (MinusR e1 Hole) e2 e2' (stepToStep' step)
stepToStep' (TimesCtxtL e1 e1' e2 step) = CtxtStep (TimesL Hole e2) e1 e1' (stepToStep' step)
stepToStep' (TimesCtxtR e1 e2 e2' step) = CtxtStep (TimesR e1 Hole) e2 e2' (stepToStep' step)

public export
data Value : Expr -> Type where
  IsNum : (n : Nat) -> Value (Num n)

public export
progress : (e : Expr) -> Either (Value e) (e' : Expr ** SmallStep e e')
progress (Num k) = Left (IsNum k)
progress (Plus e1 e2)  with (progress e1)
  progress (Plus (Num n) e2)  | (Left (IsNum n)) with (progress e2)
    progress (Plus (Num n) (Num m))  | (Left (IsNum n)) | (Left (IsNum m)) = 
      Right (Num (n + m) ** PlusNum n m)
    progress (Plus (Num n) e2)  | (Left (IsNum n)) | (Right (e2' ** step)) = 
      Right (Plus (Num n) e2' **PlusCtxtR (Num n) e2 e2' step)
  progress (Plus e1 e2)  | (Right ((e1' ** step))) = 
    Right (Plus e1' e2 ** PlusCtxtL e1 e1' e2 step)
progress (Times e1 e2) with (progress e1)
  progress (Times (Num n) e2) | (Left (IsNum n)) with (progress e2)
    progress (Times (Num n) (Num m)) | (Left (IsNum n)) | (Left (IsNum m)) = 
      Right (Num (n * m) ** TimesNum n m)
    progress (Times (Num n) e2) | (Left (IsNum n)) | (Right ((e2' ** step))) = 
      Right (Times (Num n) e2' ** TimesCtxtR (Num n) e2 e2' step)
  progress (Times e1 e2) | (Right ((e1' ** step))) = 
    Right (Times e1' e2 ** TimesCtxtL e1 e1' e2 step)
progress (Minus e1 e2) with (progress e1)
  progress (Minus (Num n) e2) | (Left (IsNum n)) with (progress e2)
    progress (Minus (Num n) (Num m)) | (Left (IsNum n)) | (Left (IsNum m)) = 
      Right (Num (minus n m) ** MinusNum n m)
    progress (Minus (Num n) e2) | (Left (IsNum n)) | (Right ((e2' ** step))) = 
      Right (Minus (Num n) e2' ** MinusCtxtR (Num n) e2 e2' step)
  progress (Minus e1 e2) | (Right ((e1' ** step))) = 
    Right (Minus e1' e2 ** MinusCtxtL e1 e1' e2 step)

partial
interpret : Expr -> Nat
interpret (Num k) = k
interpret e@(Plus e1 e2) with (progress e)
  interpret e@(Plus _ _) | (Left (IsNum n)) impossible
  interpret e@(Plus e1 e2) | (Right ((e' ** snd))) = interpret e'
interpret e@(Times e1 e2) with (progress e)
  interpret e@(Times _ _) | (Left (IsNum n)) impossible
  interpret e@(Times e1 e2) | (Right ((e' ** snd))) = interpret e'
interpret e@(Minus e1 e2) with (progress e)
  interpret e@(Minus _ _) | (Left (IsNum n)) impossible
  interpret e@(Minus e1 e2) | (Right ((e' ** snd))) = interpret e'

public export
data MultiStep : Expr -> Expr -> Type where
  NoSteps : (e : Expr) -> MultiStep e e
  NextStep : (e1, e2, e3 : Expr) -> SmallStep e1 e2 -> MultiStep e2 e3 -> MultiStep e1 e3

public export
multiStepTrans : {e1, e2, e3 : Expr} -> MultiStep e1 e2 -> MultiStep e2 e3 -> MultiStep e1 e3
multiStepTrans (NoSteps e2) steps2 = steps2
multiStepTrans (NextStep e1 e1' e2 step1 steps1) steps2 = 
  NextStep e1 e1' e3 step1 (multiStepTrans steps1 steps2)
  
public export
oneStep : {e1, e2 : Expr} -> SmallStep e1 e2 -> MultiStep e1 e2
oneStep {e1} {e2} step = NextStep e1 e2 e2 step (NoSteps e2)

public export
stepAfter : {e1, e2, e3 : Expr} -> MultiStep e1 e2 -> SmallStep e2 e3 -> MultiStep e1 e3
stepAfter steps step = multiStepTrans steps (oneStep step)

multiPlusCtxtL : (e2 : Expr) -> MultiStep e1 e1' -> MultiStep (Plus e1 e2) (Plus e1' e2)
multiPlusCtxtL e2 (NoSteps e1) = NoSteps (Plus e1 e2)
multiPlusCtxtL e2 (NextStep e1 e1'' e1' step1 stepMany) = 
  NextStep (Plus e1 e2) (Plus e1'' e2) (Plus e1' e2) 
           (PlusCtxtL e1 e1'' e2 step1) 
           (multiPlusCtxtL e2 stepMany)
           
multiPlusCtxtR : (e1 : Expr) -> MultiStep e2 e2' -> MultiStep (Plus e1 e2) (Plus e1 e2')
multiPlusCtxtR e1 (NoSteps e2) = NoSteps (Plus e1 e2)
multiPlusCtxtR e1 (NextStep e2 e2'' e2' step steps) = 
  NextStep (Plus e1 e2) (Plus e1 e2'') (Plus e1 e2')
           (PlusCtxtR e1 e2 e2'' step)
           (multiPlusCtxtR e1 steps)

multiMinusCtxtL : (e2 : Expr) -> MultiStep e1 e1' -> MultiStep (Minus e1 e2) (Minus e1' e2)
multiMinusCtxtL e2 (NoSteps e1) = NoSteps (Minus e1 e2)
multiMinusCtxtL e2 (NextStep e1 e1'' e1' step1 stepMany) = 
  NextStep (Minus e1 e2) (Minus e1'' e2) (Minus e1' e2) 
           (MinusCtxtL e1 e1'' e2 step1) 
           (multiMinusCtxtL e2 stepMany)
           
multiMinusCtxtR : (e1 : Expr) -> MultiStep e2 e2' -> MultiStep (Minus e1 e2) (Minus e1 e2')
multiMinusCtxtR e1 (NoSteps e2) = NoSteps (Minus e1 e2)
multiMinusCtxtR e1 (NextStep e2 e2'' e2' step steps) = 
  NextStep (Minus e1 e2) (Minus e1 e2'') (Minus e1 e2')
           (MinusCtxtR e1 e2 e2'' step)
           (multiMinusCtxtR e1 steps)

multiTimesCtxtL : (e2 : Expr) -> MultiStep e1 e1' -> MultiStep (Times e1 e2) (Times e1' e2)
multiTimesCtxtL e2 (NoSteps e1) = NoSteps (Times e1 e2)
multiTimesCtxtL e2 (NextStep e1 e1'' e1' step1 stepMany) = 
  NextStep (Times e1 e2) (Times e1'' e2) (Times e1' e2) 
           (TimesCtxtL e1 e1'' e2 step1) 
           (multiTimesCtxtL e2 stepMany)
           
multiTimesCtxtR : (e1 : Expr) -> MultiStep e2 e2' -> MultiStep (Times e1 e2) (Times e1 e2')
multiTimesCtxtR e1 (NoSteps e2) = NoSteps (Times e1 e2)
multiTimesCtxtR e1 (NextStep e2 e2'' e2' step steps) = 
  NextStep (Times e1 e2) (Times e1 e2'') (Times e1 e2')
           (TimesCtxtR e1 e2 e2'' step)
           (multiTimesCtxtR e1 steps)

{-
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt

dataset = pd.read_csv('SLR_nestle.csv')
X = dataset.iloc[: , 1 ].values
Y = dataset.iloc[ : , 2 ].values
X = np.reshape(X, (-1, 1))
Y = np.reshape(Y, (-1, 1))

from sklearn.model_selection import train_test_split
X_train, X_test, Y_train, Y_test = train_test_split( X, Y, test_size = 1/4, random_state = 0) 

from sklearn.linear_model import LinearRegression
regressor = LinearRegression()
regressor = regressor.fit(X_train, Y_train)

Y_pred = regressor.predict(X_test)

plt.scatter(X_test , Y_test, color = 'red')
plt.plot(X_test , regressor.predict(X_test), color ='blue')

regressor.score(X_test,Y_test)


-}

{-
import pandas as pd
import numpy as np
import matplotlib.pyplot as plt
import math

dataset = pd.read_csv('50_Startups_1.0.csv')
X = dataset.iloc[ : , :-1].values
Y = dataset.iloc[ : ,  3 ].values
xt1=[]
xt2=[]
xt3=[]

# print(dataset)
# print(X)
# print(Y)

from sklearn.model_selection import train_test_split
X_train, X_test, Y_train, Y_test = train_test_split(X, Y, test_size = 0.2, random_state = 0)

from sklearn.linear_model import LinearRegression
regressor = LinearRegression()
regressor.fit(X_train, Y_train)

y_pred = regressor.predict(X_test)

print(y_pred)
print(Y_test)

for i in range(math.floor(X_test.size/3)):
  xt1.append(X_test[i][0])

for i in range(math.floor(X_test.size/3)):
  xt2.append(X_test[i][1])

for i in range(math.floor(X_test.size/3)):
  xt3.append(X_test[i][2])

print(xt3)

# plt.scatter(xt1, Y_test, color = 'red')
# plt.plot(xt1, y_pred, color ='blue')

# plt3d = plt.figure().gca(projection='3d')
# plt3d.view_init(azim=135)
# plt3d.plot_trisurf(xt1, xt2, xt3, color=y_pred, antialiased=True)

fig = plt.figure()
ax = fig.add_subplot(111, projection='3d')

x = xt1
y = xt2
z = y_pred
c = xt3

img = ax.scatter(x, y, z, c=c, cmap=plt.hot())
fig.colorbar(img)
plt.show()
-}