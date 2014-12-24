-- Module CompareNat
-- Tested with Idris version 0.9.15.1
-- All functions are total. 

-- Author: artuuge@gmail.com

-- The present module defines data types and functions which can be used to compare natural numbers. 
-- In particular, one can find below the proofs that equality is an equivalence relation, and 
-- that less-or-equal and greater-or-equal are partial orders. 

-- Some of the given proofs use such features of the Idris programming language as 
-- the keyword impossible, data type Void, and the function void. 


module CompareNat

-- Assume that the natural numbers are defined in terms of 
-- two constructors: Z (zero) and S (the successor): 
-- data Nat : Type where 
--   Z : Nat
--   S : Nat -> Nat 

-- The data type (Equal m n) expresses a statement "m is equal to n".
data Equal : Nat -> Nat -> Type where 
  EqualZZ : Equal Z Z   -- this constructor provides a proof that "zero equals zero"
  EqualSS : (m : Nat) -> (n : Nat) -> (Equal m n) -> Equal (S m) (S n) 
    -- If we have a proof that m = n (i.e. an inhabitant p of the type (Equal m n)), 
    -- then EqualSS constructs a proof that "S m = S n" (intuitively: m = n implies (m + 1) = (n + 1)).

-- The equality relation is an equivalence relation, i.e. it is 
-- 1) reflexive: x = x
-- 2) symmetric: x = y implies y = x
-- 3) transitive: (x = y and y = z) imply x = z

-- proof of reflexivity of equality
equalRefl : (m : Nat) -> Equal m m   
equalRefl Z = EqualZZ   -- if x is zero, then the required proof is given by EqualZZ
equalRefl (S m) = EqualSS m m (equalRefl m)   
  -- if the argument pattern matches (S m), then we can construct the proof (S m) = (S m) from (m = m) using EqualSS

-- proof of symmetry of equality
equalSymm : (Equal m n) -> Equal n m   
equalSymm EqualZZ = EqualZZ 
  -- If the supplied argument matches EqualZZ, this implies that m and n are both zero, 
  -- so the goal type (Equal n m) reduces to (Equal Z Z), for which we have an inhabitant EqualZZ. 
equalSymm (EqualSS m n q) = EqualSS n m (equalSymm q) 
  -- q inhabits (Equal m n), and the expression (EqualSS m n q) is of type (Equal (S m) (S n)). 
  -- Therefore, the goal type becomes (Equal (S n) (S m)) and we can 
  -- construct its inhabitant using EqualSS and the recursive call to equalSymm. 
  -- The argument q is simpler than the supplied argument (EqualSS m n q). 

-- proof of transitivity of equality
equalTrans : (Equal l m) -> (Equal m n) -> Equal l n 
equalTrans EqualZZ EqualZZ = EqualZZ 
  -- If the supplied arguments both pattern match EqualZZ, 
  -- then from the first argument we conclude that l and m are both zero, and 
  -- from the second argument we conclude that m and n are both zero. 
  -- In both cases, m is zero, so there is no contradiction. 
  -- The goal type (Equal l n) reduces now to (Equal Z Z), for which we have an inhabitant EqualZZ 
equalTrans EqualZZ (EqualSS _ _ _) impossible 
  -- The pattern match for the first argument would imply that m is a zero, while 
  -- the pattern match for the second argument would imply than m is a successor. 
  -- This cannot happen, so we state this case as impossible.  
equalTrans (EqualSS _ _ _) EqualZZ impossible 
  -- Similar to the previous case, matching the first argument against the 
  -- constructor EqualSS implies that m is a successor, while the pattern match 
  -- for the second argument requires m to be zero. 
  -- The two possibilities are incompatible, so the case is impossible.
equalTrans (EqualSS l m p) (EqualSS m n q) = EqualSS l n (equalTrans p q)
  -- The expression (EqualSS l m p) inhabits the type (Equal (S l) (S m)). 
  -- The expression (EqualSS m n q) inhabits the type (Equal (S m) (S n)). 
  -- Therefore, the goal type is Equal (S l) (S n). 
  -- p is simpler than (EqualSS l m p), since EqualSS is a constructor. 
  -- similarly, q is simpler than (EqualSS m n q). 
  -- Therefore, the recursive call (equalTrans p q) will work giving us an inhabitant of (Equal l n). 
  -- It remains to use EqualSS to obtain an inhabitant of (Equal (S l) (S n)).   
----------


-- The data type (Less m n) expresses the statement "m is less than n".  
data Less : Nat -> Nat -> Type where 
  LessZS : (n : Nat) -> Less Z (S n)    -- zero is less than a successor.
  LessSS : (m : Nat) -> (n : Nat) -> (Less m n) -> Less (S m) (S n)   -- if m < n, then (S m) < (S n).

-- The relation less-than is transitive. 
lessTrans : (Less l m) -> (Less m n) -> Less l n   -- if (l < m and m < n), then l < n.
lessTrans (LessZS _) (LessZS _) impossible   -- m cannot be zero and a successor at the same time. 
lessTrans (LessZS m) (LessSS m n _) = LessZS n 
  -- The pattern match of the first argument against the constructor LessZS implies that l is zero
  -- taking into account the pattern match of the second argument, 
  -- we are looking at (Less Z (S m)) -> (Less (S m) (S n)) -> (Less Z (S n))
  -- An inhabitant of the goal type (Less Z (S n)) is provided by (LessZS n). 
lessTrans (LessSS _ _ _) (LessZS _) impossible   -- m cannot be a successor and zero at the same time. 
lessTrans (LessSS l m p) (LessSS m n q) = LessSS l n (lessTrans p q) 
  -- After pattern matching the first and the second arguments, 
  -- we look at (Less (S l) (S m)) -> (Less (S m) (S n)) -> (Less (S l) (S n)).
  -- Since p is simpler than (LessSS l m p), and q is simpler than (LessSS m n q), 
  -- we may assume that we already have (lessTrans p q) : (Less l m). 
  -- The goal type (Less (S l) (S n)) obtains then an inhabitant using LessSS. 

-- This is an auxiliary function proving that if (l = m and m < n) then (l < n). 
-- Similar comments as above apply for the impossible cases and the admissibility of the recursive call. 
spliceEqualLess : (Equal l m) -> (Less m n) -> Less l n 
spliceEqualLess EqualZZ (LessZS n) = LessZS n
spliceEqualLess EqualZZ (LessSS _ _ _) impossible
spliceEqualLess (EqualSS _ _ _) (LessZS _) impossible
spliceEqualLess (EqualSS l m p) (LessSS m n q) = LessSS l n (spliceEqualLess p q)

-- An auxiliary function similar to the previous one: we prove that if (l < m and m = n) then (l < n). 
spliceLessEqual : (Less l m) -> (Equal m n) -> Less l n
spliceLessEqual (LessZS _) EqualZZ impossible
spliceLessEqual (LessZS m) (EqualSS m n _) = LessZS n
spliceLessEqual (LessSS _ _ _) EqualZZ impossible
spliceLessEqual (LessSS l m p) (EqualSS m n q) = LessSS l n (spliceLessEqual p q)

----------

-- This data type is totally similar to (Less m n).
-- (Greater m n) corresponds to the statement "m is greater than n". 
data Greater : Nat -> Nat -> Type where 
  GreaterSZ : (m : Nat) -> Greater (S m) Z   -- a successor is greater than zero
  GreaterSS : (m : Nat) -> (n : Nat) -> (Greater m n) -> Greater (S m) (S n)    -- if (m > n), then ((S m) > (S n)).

-- The relation greater-than is transitive. 
-- The proof is constructed in the same way as lessTrans.
greaterTrans : (Greater l m) -> (Greater m n) -> Greater l n
greaterTrans (GreaterSZ _) (GreaterSZ _) impossible
greaterTrans (GreaterSZ _) (GreaterSS _ _ _) impossible
greaterTrans (GreaterSS l m _) (GreaterSZ m) = GreaterSZ l 
greaterTrans (GreaterSS l m p) (GreaterSS m n q) = GreaterSS l n (greaterTrans p q) 

-- auxiliary statement: if ((l = m) and (m > n)), then (l > n). 
spliceEqualGreater : (Equal l m) -> (Greater m n) -> Greater l n
spliceEqualGreater EqualZZ (GreaterSZ _) impossible
spliceEqualGreater EqualZZ (GreaterSS _ _ _) impossible
spliceEqualGreater (EqualSS l m _) (GreaterSZ m) = GreaterSZ l
spliceEqualGreater (EqualSS l m p) (GreaterSS m n q) = GreaterSS l n (spliceEqualGreater p q) 

-- another auxiliary statement: if ((l > m) and (m = n)), then (l > n).
spliceGreaterEqual : (Greater l m) -> (Equal m n) -> Greater l n
spliceGreaterEqual (GreaterSZ l) EqualZZ = GreaterSZ l
spliceGreaterEqual (GreaterSS _ _ _) EqualZZ impossible
spliceGreaterEqual (GreaterSZ _) (EqualSS _ _ _) impossible
spliceGreaterEqual (GreaterSS l m p) (EqualSS m n q) = GreaterSS l n (spliceGreaterEqual p q)


-- It is convenient to be able to switch between the statements "m < n" and "n > m". 
greaterFromLess : (Less m n) -> Greater n m
greaterFromLess (LessZS n) = GreaterSZ n   
  -- If we have a match on a proof "zero is less than the successor of n", then this 
  -- immediately gives us a proof "the successor of n is greater than zero"
greaterFromLess (LessSS m n p) = GreaterSS n m (greaterFromLess p) 
  -- p is explicitly (i.e. we get rid of a constructor) simpler than (LessSS m n p). 
  -- Therefore, we may assume that we have (greaterFromLess p) inhabiting (Less n m). 
  -- The constructor GreaterSS links us to the goal type in this case (Greater (S n) (S m)). 
  
-- Here we construct less-than from greater-than. 
lessFromGreater : (Greater m n) -> Less n m 
lessFromGreater (GreaterSZ m) = LessZS m
lessFromGreater (GreaterSS m n p) = LessSS n m (lessFromGreater p)

----------  

-- Assemble three possibilities equal, less-than, and greater-than, into a single data type. 
data Compare : Nat -> Nat -> Type where 
  EqualC : (Equal m n) -> Compare m n 
  LessC : (Less m n) -> Compare m n 
  GreaterC : (Greater m n) -> Compare m n 
  
-- The name of this function reminds the names of constructors EqualSS, LessSS, and GreaterSS. 
-- It is nonetheless not a constructor, but a theorem, that if a certain comparison 
-- holds between m and n, then the same is valid of the successors, (S m) and (S n).  
compareSS : (m : Nat) -> (n : Nat) -> (Compare m n) -> Compare (S m) (S n) 
compareSS m n (EqualC p) = EqualC (EqualSS m n p)
compareSS m n (LessC p) = LessC (LessSS m n p)
compareSS m n (GreaterC p) = GreaterC (GreaterSS m n p)

-- The result of comparison here is not EQ, LT, or GT, but is described by the 
-- associated types (Equal m n), (Less m n), and (Greater m n). 
-- We need to assemble them in one type (Compare m n), otherwise one cannot write a single function. 
compareNat : (m : Nat) -> (n : Nat) -> Compare m n
compareNat Z Z = EqualC EqualZZ
compareNat Z (S n) = LessC (LessZS n)
compareNat (S m) Z = GreaterC (GreaterSZ m) 
compareNat (S m) (S n) = compareSS m n (compareNat m n)

-- This function forgets the given proof of a certain comparison between m and n. 
orderingFromCompare : (Compare m n) -> Ordering 
orderingFromCompare (EqualC _) = EQ
orderingFromCompare (LessC _) = LT
orderingFromCompare (GreaterC _) = GT

-- This function yields another definition of compare on natural numbers. 
orderingNat : Nat -> Nat -> Ordering 
orderingNat m n = orderingFromCompare (compareNat m n)

-- Here we prove that (m = n) and (m < n) cannot hold at the same time. 
-- Void is an Idris type which has no inhabitants. 
-- We need to pattern match on four cases (two constructors of Equal, and two constructors of Less, 2 * 2 = 4). 
-- The impossibility of the first three cases is visible from an analysis similar to the ones above. 
excludeEqualLess : (Equal m n) -> (Less m n) -> Void
excludeEqualLess EqualZZ (LessZS _) impossible 
  -- Since the first argument matches EqualZZ, we conclude: m is zero, and n is zero. 
  -- Since the second argument matches (LessZS _), we conclude: m is zero, and n is a successor. 
  -- n cannot be zero and a successor at the same time, this is impossible. 
excludeEqualLess EqualZZ (LessSS _ _ _) impossible   -- m cannot be zero and a successor at the same time. 
excludeEqualLess (EqualSS _ _ _) (LessZS _) impossible   -- m cannot be a successor and zero at the same time. 
excludeEqualLess (EqualSS _ _ p) (LessSS _ _ q) = excludeEqualLess p q 
   -- Since p is explicitly more simple than (EqualSS _ _ p), and 
   -- since q is explicitly more simple than (EqualSS _ _ q), we can 
   -- pretend that the value (excludeEqualLess p q) : Void 
   -- has already been constructed. We can just take that value as the result. 
   -- The sequence of recursions will eventually hit one of the impossible cases, so the 
   -- value inhabiting Void is never actually constructed. 
   -- The fourth case is not considered as impossible by the type checker, and we need 
   -- to handle it using Void to have a function which is total in the perception of Idris. 


-- a proof that (m = n) and (m > n) cannot hold at the same time. 
excludeEqualGreater : (Equal m n) -> (Greater m n) -> Void
excludeEqualGreater EqualZZ (GreaterSZ _) impossible
excludeEqualGreater EqualZZ (GreaterSS _ _ _) impossible
excludeEqualGreater (EqualSS _ _ _) (GreaterSZ _) impossible
excludeEqualGreater (EqualSS _ _ p) (GreaterSS _ _ q) = excludeEqualGreater p q

-- a proof that (m < n) and (m > n) exclude each other. 
excludeLessGreater : (Less m n) -> (Greater m n) -> Void 
excludeLessGreater (LessZS _) (GreaterSZ _) impossible
excludeLessGreater (LessZS _) (GreaterSS _ _ _) impossible
excludeLessGreater (LessSS _ _ _) (GreaterSZ _) impossible
excludeLessGreater (LessSS _ _ p) (GreaterSS _ _ q) = excludeLessGreater p q 

----------

-- unite disjointly the cases less-than and equal into one: less-or-equal
data LessEqual : Nat -> Nat -> Type where    
  LessLE : (Less m n) -> LessEqual m n
  EqualLE : (Equal m n) -> LessEqual m n


-- Being less-or-equal is a partial order, i.e. this relation is 
-- 1) reflexive: x <= x 
-- 2) antisymmetric: ((x <= y) and (y <= x)) implies (x = y). 
-- 3) transitive: ((x <= y) and (y <= z)) implies (x <= z). 


-- reflexivity of less-or-equal
leqRefl : (n : Nat) -> LessEqual n n
leqRefl n = EqualLE (equalRefl n)

-- antisymmetry of less-or-equal
leqAntisymm : (LessEqual m n) -> (LessEqual n m) -> Equal m n
leqAntisymm (EqualLE p) _ = p   -- by construction, p : (Equal m n), so p yields the goal. 
leqAntisymm (LessLE _) (EqualLE q) = equalSymm q   -- by construction, q : (Equal n m), not (Equal m n), so we need to additionally invoke equalSymm. 
leqAntisymm (LessLE p) (LessLE q) = void (excludeLessGreater p (greaterFromLess q)) 
  -- void : Void -> a
  -- We pretend that we have a value in Void from excludeLessGreater, and then apply void. 
  -- The free variable a is specialized to the goal type (Equal m n). 
  -- The last case is considered as possible by the type checker, so void is necessary to achieve the totality. 

-- transitivity of less-or-equal
leqTrans : (LessEqual l m) -> (LessEqual m n) -> LessEqual l n
leqTrans (EqualLE p) (EqualLE q) = EqualLE (equalTrans p q)  
leqTrans (EqualLE p) (LessLE q) = LessLE (spliceEqualLess p q)
leqTrans (LessLE p) (EqualLE q) = LessLE (spliceLessEqual p q) 
leqTrans (LessLE p) (LessLE q) = LessLE (lessTrans p q)

---------- 

-- unite greater-than and equal into greater-or-equal
data GreaterEqual : Nat -> Nat -> Type where 
  GreaterGE : (Greater m n) -> GreaterEqual m n
  EqualGE : (Equal m n) -> GreaterEqual m n

-- Greater-or-equal is a partial order, just like less-or-equal. 

-- reflexivity of greater-or-equal
geqRefl : (n : Nat) -> GreaterEqual n n
geqRefl n = EqualGE (equalRefl n)

-- antisymmetry of greater-or-equal 
geqAntisymm : (GreaterEqual m n) -> (GreaterEqual n m) -> Equal m n
geqAntisymm (EqualGE p) _ = p
geqAntisymm (GreaterGE _) (EqualGE q) = equalSymm q
geqAntisymm (GreaterGE p) (GreaterGE q) = void (excludeLessGreater (lessFromGreater p) q)
  -- here (void : Void -> a) becomes (void : Void -> Equal m n). 
  
-- transitivity of greater-or-equal
geqTrans : (GreaterEqual l m) -> (GreaterEqual m n) -> GreaterEqual l n
geqTrans (EqualGE p) (EqualGE q) = EqualGE (equalTrans p q)  
geqTrans (EqualGE p) (GreaterGE q) = GreaterGE (spliceEqualGreater p q)
geqTrans (GreaterGE p) (EqualGE q) = GreaterGE (spliceGreaterEqual p q) 
geqTrans (GreaterGE p) (GreaterGE q) = GreaterGE (greaterTrans p q)

----------
