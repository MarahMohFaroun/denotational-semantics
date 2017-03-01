-- Language Engineering
-- Denotational Semantics
-- CWK2

import Prelude hiding (lookup)

-- Type Definitions (Given)

data Aexp = N Integer | V Var | Add Aexp Aexp | Mult Aexp Aexp | Sub Aexp Aexp deriving (Show)
data Bexp = TRUE | FALSE | Eq Aexp Aexp | Le Aexp Aexp | Neg Bexp | And Bexp Bexp deriving (Show)
data Stm  = Ass Var Aexp | Skip | Comp Stm Stm | If Bexp Stm Stm | While Bexp Stm | Block DecV DecP Stm | Call Pname deriving (Show)

type Var = String
type Pname = String
type DecV = [(Var,Aexp)]
type DecP = [(Pname,Stm)]

type Z = Integer
type T = Bool
type State = Var -> Z
type Loc = Z
type Store = Loc -> Z
type EnvV = Var -> Loc
type EnvP = Pname -> Store -> Store

next = 0


-- Semantic Functions 

--arithmetic expresions
a_val :: Aexp -> State -> Z
a_val (N n) s			= n
a_val (V x) s			= s x
a_val (Add a1 a2) s		= (a_val a1 s) + (a_val a2 s)
a_val (Mult a1 a2) s	= (a_val a1 s) * (a_val a2 s)
a_val (Sub a1 a2) s		= (a_val a1 s) - (a_val a2 s)

--boolean expressions
b_val :: Bexp -> State -> T
b_val (TRUE) s								= True
b_val (FALSE) s								= False
b_val (Eq a1 a2) s		
	| (a_val a1 s) == (a_val a2 s)			= True
	| otherwise 							= False
b_val (Le a1 a2) s
	| (a_val a1 s) <= (a_val a2 s)			= True
	| otherwise 							= False
b_val (Neg a1) s
	| (b_val a1 s) == False					= True
	| otherwise 							= False
b_val (And a1 a2) s
	| (b_val a1 s) && (b_val a2 s)			= True
	| otherwise 							= False

--if b then f1 else f2
cond :: (a->T, a->a, a->a) -> (a->a)
cond (p, g1, g2) s
	| p s 			= g1 s
	| otherwise		= g2 s

--fixpoint function
fix :: (a -> a) -> a
fix ff = ff (fix ff)


s :: Stm
s = (Block [("x", (N 7))] [("p", (Ass "x" (N 0)))] 
		(Block [("x", (N 5))] [] (Call "p")) 
    )

w :: Stm
w = (Block [("x", (N 8))] [("func", (Ass "x" (N 3)))] Skip)


--new location
new :: Loc -> Loc
new z = z+1 

--mapping from variable to value
lookup :: EnvV -> Store -> State
lookup env sto = sto . env 

--on input x update function f to output v
update :: Eq a => (a->b) -> b -> a -> (a->b)
update f v x y
	| x == y		= v 
	| otherwise 	= f y

--execution of statement on variables
s_ds' :: Stm -> EnvV -> Store -> Store
s_ds' (Ass x a)	env sto 	= update sto (a_val a (lookup env sto)) l 
								where l = env x
s_ds' (Skip) env sto		= sto
s_ds' (Comp s1 s2) env sto	= (s_ds' s2 env sto) . (s_ds' s1 env sto) 
s_ds' (If b s1 s2) env sto	= cond((b_val b) . (lookup env), (s_ds' s1 env), (s_ds' s2 env)) sto
s_ds' (While b s1) env sto	= fix f sto
					where f g = cond((b_val b) . (lookup env), (g . (s_ds' s1 env)), s_ds' s1 env)

--update var env and store
d_v_ds :: DecV -> (EnvV, Store) -> (EnvV, Store)
d_v_ds ((x,a):xs) (env, sto)	= d_v_ds xs (update env l x, update (update sto v l) (new l) next)
								where l = sto next;
									  v = a_val a (lookup env sto)
d_v_ds [] (env, sto)		= (env, sto)


--update proc env and store (non-recursive)
{-d_p_ds :: DecP -> EnvV -> EnvP -> EnvP
d_p_ds [(p,s)] envv envp 	= d_p_ds [(p,s)] envv (update envp g p)
								where g = s_ds s envv envp
d_p_ds [] envv envp			= envp-}


--update proc env and store (recursive)
d_p_ds :: DecP -> EnvV -> EnvP -> EnvP
d_p_ds ((p,s):ps) envv envp 	= d_p_ds ps envv (update envp (fix f) p)
								where f g = s_ds s envv (update envp g p)
d_p_ds [] envv envp			= envp

--execution of statement on variables (with procedures)
s_ds :: Stm -> EnvV -> EnvP -> Store -> Store
s_ds (Ass x a) envv envp sto 			= update sto (a_val a (lookup envv sto)) l
											where l = envv x
s_ds (Skip) envv envp sto 				= sto
s_ds (Comp s1 s2) envv envp sto			= ((s_ds s2 envv envp) . (s_ds s1 envv envp)) sto
s_ds (If b s1 s2) envv envp sto			= cond((b_val b) . (lookup envv), s_ds s1 envv envp, s_ds s2 envv envp) sto
s_ds (While b s) envv envp sto			= fix f sto
											where f g = cond((b_val b) . (lookup envv), g . (s_ds s envv envp), id)
s_ds (Block decv decp s) envv envp sto 	= s_ds s envv' envp' sto'
											where 	(envv', sto') = d_v_ds decv (envv, sto);
													envp' = d_p_ds decp envv' envp
s_ds (Call p) envv envp sto				= envp p sto

--value of location 0 reserved for next token
t :: Store
t l 
	| l==next	= 1 
	| otherwise	= undefined

--number of defined locations
n :: Z
n = s_ds s undefined undefined t next 

--factorial program
f :: DecP
f = [("fac", Block [("z", V "x")] [] (
	If (Eq (V "x") (N 1)) (Skip) (
		Comp (Ass "x" (Sub (V "x") (N 1))) (Comp (Call "fac") ( 
			Ass "y" (Mult (V "z") (V "y")))
		)
	)
     ))]

