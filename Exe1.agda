module Exe1 where

open import Basics public

-- \section{Zipping Lists of Compatible Shape}

data List (X : Set) : Set where
  <>    :                 List X
  _,_   : X -> List X ->  List X

infixr 4 _,_

zip0 : {S T : Set} -> List S -> List T -> List (S * T)
zip0 <>        <>        = <>
zip0 (s , ss)  (t , ts)  = (s , t) , zip0 ss ts
zip0 _         _         = <>  -- a dummy value, for cases we should not reach

data Nat : Set where
  zero  :         Nat
  suc   : Nat ->  Nat

{-# BUILTIN NATURAL Nat #-}
{-# BUILTIN ZERO zero #-}
{-# BUILTIN SUC suc #-}

length : {X : Set} -> List X -> Nat
length <>        = zero
length (x , xs)  = suc (length xs)

data Vec (X : Set) : Nat -> Set where
  <>   :                               Vec X zero
  _,_  : {n : Nat} -> X -> Vec X n ->  Vec X (suc n)

zip1 : forall {n S T} -> Vec S n -> Vec T n -> Vec (S * T) n
zip1 <>       <>       = <>
zip1 (s , ss) (t , ts) = (s , t) , zip1 ss ts

vec : forall {n X} -> X -> Vec X n
vec {zero} x = <>
vec {suc n} x = x , vec x

vapp :  forall {n S T} -> Vec (S -> T) n -> Vec S n -> Vec T n
vapp <>       <>       = <>
vapp (f , fs) (s , ss) = f s , vapp fs ss

vmap : forall {n S T} -> (S -> T) -> Vec S n -> Vec T n
vmap f ss = vapp (vec f) ss

zip2 : forall {n S T} -> Vec S n -> Vec T n -> Vec (S * T) n
zip2 ss ts = vapp (vapp (vec _,_) ss) ts


--[Finite sets and projection from vectors]

data Fin : Nat -> Set where
  zero : {n : Nat} -> Fin (suc n)
  suc  : {n : Nat} -> Fin n -> Fin (suc n)

proj : forall {n X} -> Vec X n -> Fin n -> X
proj (x , xs) zero = x
proj (x , xs) (suc i) = proj xs i

tabulate : forall {n X} -> (Fin n -> X) -> Vec X n
tabulate {zero} f = <>
tabulate {suc n} f = f zero , tabulate (f o suc)

-- Functors and Applicatives

record EndoFunctor (F : Set -> Set) : Set1 where
  field
    map  : forall {S T} -> (S -> T) -> F S -> F T
open EndoFunctor {{...}} public

record Applicative (F : Set -> Set) : Set1 where
  infixl 2 _<*>_
  field
    pure    : forall {X} -> X -> F X
    _<*>_   : forall {S T} -> F (S -> T) -> F S -> F T
  applicativeEndoFunctor : EndoFunctor F
  applicativeEndoFunctor = record { map = _<*>_ o pure }
open Applicative {{...}} public

applicativeVec  : forall {n} -> Applicative \ X -> Vec X n
applicativeVec  = record { pure = vec; _<*>_ = vapp }
endoFunctorVec  : forall {n} -> EndoFunctor \ X -> Vec X n
endoFunctorVec  = applicativeEndoFunctor

applicativeFun : forall {S} -> Applicative \ X -> S -> X
applicativeFun = record
  {  pure    = \ x s -> x              -- also known as K (drop environment)
  ;  _<*>_   = \ f a s -> f s (a s)    -- also known as S (share environment)
  }

record Monad (F : Set -> Set) : Set1 where
  field
    return  : forall {X} -> X -> F X
    _>>=_   : forall {S T} -> F S -> (S -> F T) -> F T
  monadApplicative : Applicative F
  monadApplicative = record
    {  pure   = return
    ;  _<*>_  = \ ff fs -> ff >>= \ f -> fs >>= \ s -> return (f s) }
open Monad {{...}} public

monadVec : {n : Nat} -> Monad \ X -> Vec X n
monadVec = record {
    return = vec;
    _>>=_ = λ v f -> tabulate (λ i -> proj (vmap (proj o f) v) i i)
  }

applicativeId : Applicative id
applicativeId = record {
    pure = id;
    _<*>_ = id
  }

applicativeComp : forall {F G} -> Applicative F -> Applicative G -> Applicative (F o G)
applicativeComp aF aG = record {
    pure = pure {{aF}} o pure {{aG}};
    _<*>_ = λ fgf fgx -> pure {{aF}} (_<*>_ {{aG}}) <*> fgf <*> fgx
  }

record Monoid (X : Set) : Set where
  infixr 4 _&_
  field
    neut  : X
    _&_   : X -> X -> X
  monoidApplicative : Applicative \ _ -> X
  monoidApplicative = record { pure = λ _ -> neut; _<*>_ = _&_ }
open Monoid {{...}} public -- it's not obvious that we'll avoid ambiguity

--Show by construction that the pointwise product of |Applicative|s is
-- |Applicative|.
applicativeProd : forall {F G} -> Applicative F -> Applicative G -> Applicative (λ S -> F S * G S)
applicativeProd {F}{G} aF aG = record {
    pure = λ x -> pure x , pure x;
    _<*>_ = papp
  }
 where
  papp : forall {S T} -> F (S -> T) * G (S -> T) -> F S * G S -> F T * G T
  papp (fst , gst) (fs , gs) = (fst <*> fs) , (gst <*> gs)

record Traversable (F : Set -> Set) : Set1 where
  field
    traverse :  forall {G S T}{{AG : Applicative G}} ->
                (S -> G T) -> F S -> G (F T)
  traversableEndoFunctor : EndoFunctor F
  traversableEndoFunctor = record { map = traverse }
open Traversable {{...}} public

traversableVec : {n : Nat} -> Traversable \ X -> Vec X n
traversableVec = record { traverse = vtr } where
  vtr :  forall {n G S T}{{_ : Applicative G}} ->
         (S -> G T) -> Vec S n -> G (Vec T n)
  vtr {{aG}} f <>        = pure {{aG}} <>
  vtr {{aG}} f (s , ss)  = pure {{aG}} _,_ <*> f s <*> vtr f ss

transpose : forall {m n X} -> Vec (Vec X n) m -> Vec (Vec X m) n
transpose = traverse id

crush :  forall {F X Y}{{TF : Traversable F}}{{M : Monoid Y}} ->
         (X -> Y) -> F X -> Y
crush {{M = M}} =
  traverse {T = One}{{AG = monoidApplicative {{M}}}}  -- |T| arbitrary


{-Show that |Traversable| is closed under identity and composition.
What other structure does it preserve?-}
traversableId : Traversable id
traversableId = record { traverse = id }

traversableComp : forall {F G} -> Traversable F -> Traversable G -> Traversable (F o G)
traversableComp tF tG = record { traverse = traverse {{tF}} o traverse {{tG}} }

traversableProd : forall {F G} -> Traversable F -> Traversable G -> Traversable (λ S -> F S * G S)
traversableProd {F}{G} tF tG = record { traverse = ptr } where
  ptr : forall {H S T} {{_ : Applicative H}} -> (S -> H T) -> F S * G S -> H (F T * G T)
  ptr {{aH}} f (fs , gs) = pure {{aH}} _,_ <*> traverse f fs <*> traverse f gs

--\section{Arithmetic}

_+Nat_ : Nat -> Nat -> Nat
zero +Nat y = y
suc x +Nat y = suc (x +Nat y)

_*Nat_ : Nat -> Nat -> Nat
zero *Nat y = zero
suc x *Nat y = y +Nat (x *Nat y)


--\section{Normal Functors}

record Normal : Set1 where
  constructor _/_
  field
    Shape  : Set
    size   : Shape -> Nat
  <!_!>N : Set -> Set
  <!_!>N X = Sg Shape \ s -> Vec X (size s)
open Normal public
infixr 0 _/_

VecN : Nat -> Normal
VecN n = One / pure n

ListN : Normal
ListN = Nat / id


KN : Set -> Normal
KN A = A / λ _ -> 0

IN : Normal
IN = VecN 1

_+N_ : Normal -> Normal -> Normal
(ShF / szF) +N (ShG / szG) = (ShF + ShG) / vv szF <?> szG

_*N_ : Normal -> Normal -> Normal
(ShF / szF) *N (ShG / szG) = (ShF * ShG) / vv \ f g -> szF f +Nat szG g

nInj : forall {X}(F G : Normal) -> <! F !>N X + <! G !>N X -> <! F +N G !>N X
nInj F G (tt , ShF , xs) = (tt , ShF) , xs
nInj F G (ff , ShG , xs) = (ff , ShG) , xs

data _^-1_ {S T : Set}(f : S -> T) : T -> Set where
  from : (s : S) -> f ^-1 f s

nCase : forall {X} F G (s : <! F +N G !>N X) -> nInj F G ^-1 s
nCase F G ((tt , ShF) , xs) = from (tt , ShF , xs)
nCase F G ((ff , ShG) , xs) = from (ff , ShG , xs)

nOut : forall {X}(F G : Normal) -> <! F +N G !>N X -> <! F !>N X + <! G !>N X
nOut F G xs' with nCase F G xs'
nOut F G .(nInj F G xs) | from xs = xs

_++_ : forall {m n X} -> Vec X m -> Vec X n -> Vec X (m +Nat n)
_++_ <> ys = ys
_++_ (x , xs) ys = x , xs ++ ys

unAppend : forall m n {X} -> (xsys : Vec X (m +Nat n)) -> (vv _++_ {m}{n}) ^-1 xsys
unAppend zero n ys = from (<> , ys)
unAppend (suc m) n (x , xsys) with unAppend m n xsys
unAppend (suc m) n (x , .(xs ++ ys)) | from (xs , ys) = from ((x , xs) , ys)

nPair : forall {X}(F G : Normal) -> <! F !>N X * <! G !>N X -> <! F *N G !>N X
nPair F G ((ShF , xs) , (ShG , ys)) = (ShF , ShG) , (xs ++ ys)

nUnpair : forall {X} F G (s : <! F *N G !>N X) -> nPair F G ^-1 s
nUnpair F G ((ShF , ShG) , xsys)
  with unAppend (size F ShF) (size G ShG) xsys
nUnpair F G ((ShF , ShG) , .(xs ++ ys))
  | from (xs , ys) = from ((ShF , xs) , (ShG , ys))

listNMonoid : {X : Set} -> Monoid (<! ListN !>N X)
listNMonoid = record {
    neut = 0 , <>;
    _&_ = _++N_
  }
 where
  _++N_ : {X : Set} -> <! ListN !>N X -> <! ListN !>N X -> <! ListN !>N X
  (n , xs) ++N (m , ys) = (n +Nat m , xs ++ ys)

sumMonoid : Monoid Nat
sumMonoid = record { neut = 0; _&_ = _+Nat_ }

normalTraversable : (F : Normal) -> Traversable <! F !>N
normalTraversable F = record
  { traverse = \ {{aG}} f -> vv \ s xs -> pure {{aG}}  (_,_ s) <*> traverse f xs }

_oN_ : Normal -> Normal -> Normal
F oN (ShG / szG) = <! F !>N ShG / crush {{normalTraversable F}} szG

sizeT : forall {F}{{TF : Traversable F}}{X} -> F X -> Nat
sizeT {{tF}} = crush {{tF}} (\ _ -> 1)

normalT : forall F {{TF : Traversable F}} -> Normal
normalT F {{tF}} = F One / sizeT {{tF}}

shapeT : forall {F}{{TF : Traversable F}}{X} -> F X -> F One
shapeT {{tF}} = traverse {{tF}} (\ _ -> <>)

one : forall {X} -> X -> <! ListN !>N X
one x = 1 , (x , <>)

contentsT : forall {F}{{TF : Traversable F}}{X} -> F X -> <! ListN !>N X
contentsT = crush one

--[normal morphisms]

_-N>_ : Normal -> Normal -> Set
F -N> G = (s : Shape F) -> <! G !>N (Fin (size F s))

nMorph : forall {F G} -> F -N> G -> forall {X} -> <! F !>N X -> <! G !>N X
nMorph f (s , xs)  with f s
...                | s' , is = s' , map (proj xs) is

--Show how to compute the normal morphism representing a given natural
--transformation.

morphN : forall {F G} -> (forall {X} -> <! F !>N X -> <! G !>N X) -> F -N> G
morphN f s = f (s , tabulate id)

--[Hancock's tensor]
_><_ : Normal -> Normal -> Normal
(ShF / szF) >< (ShG / szG) = (ShF * ShG) / vv \ f g -> szF f *Nat szG g

fromMatrix : {m n : Nat} {X : Set} -> Vec (Vec X m) n -> Vec X (n *Nat m)
fromMatrix <> = <>
fromMatrix (col , cols) = col ++ fromMatrix cols

unfromMatrix : (m n : Nat) {X : Set} -> (elts : Vec X (n *Nat m)) -> fromMatrix {m}{n} ^-1 elts
unfromMatrix m zero <> = from <>
unfromMatrix m (suc n) elts with unAppend m (n *Nat m) elts
unfromMatrix m (suc n) .(col ++ rest) | from (col , rest) with unfromMatrix m n rest
unfromMatrix m (suc n) .(col ++ fromMatrix cols) | from (col , .(fromMatrix cols)) | from cols = from (col , cols)

toMatrix : {m n : Nat} {X : Set} -> Vec X (n *Nat m) -> Vec (Vec X m) n
toMatrix {m} {n} elts with unfromMatrix m n elts
toMatrix .(fromMatrix m) | from m = m

swap : (F G : Normal) -> (F >< G) -N> (G >< F)
swap F G (ShF , ShG) = ((ShG , ShF) , fromMatrix {size F ShF} {size G ShG} (transpose (toMatrix (tabulate id))))

crush-vec : {A : Set} (f : A → Nat) (x : A) (n : Nat) -> crush f (vec {n} x) == n *Nat f x
crush-vec f x zero = refl
crush-vec f x (suc n) = cong (_+Nat_ (f x)) (crush-vec f x n)

drop : (F G : Normal) -> (F >< G) -N> (F oN G)
drop F G (ShF , ShG) = (ShF , (vec ShG)) , k (crush-vec (size G) ShG (size F ShF))
 where
  k : {n m : Nat} -> n == m -> Vec (Fin m) n
  k {n} {.n} refl = tabulate id

--\section{Proving Equations}


record MonoidOK X {{M : Monoid X}} : Set where
  field
    absorbL  : (x : X) ->      neut & x == x
    absorbR  : (x : X) ->      x & neut == x
    assoc    : (x y z : X) ->  (x & y) & z == x & (y & z)

natMonoidOK : MonoidOK Nat
natMonoidOK = record
  {  absorbL  = \ _ -> refl
  ;  absorbR  = _+zero
  ;  assoc    = assoc+
  }  where    -- see below
  _+zero : forall x -> x +Nat zero == x
  zero   +zero                  = refl
  suc n  +zero rewrite n +zero  = refl

  assoc+ : forall x y z -> (x +Nat y) +Nat z  == x +Nat (y +Nat z)
  assoc+ zero     y z                       = refl
  assoc+ (suc x)  y z rewrite assoc+ x y z  = refl

listNMonoidOK : {X : Set} -> MonoidOK (<! ListN !>N X)
listNMonoidOK {X} = record
  { absorbL = λ _ → refl
  ; absorbR = vv ++<>
  ; assoc = vv λ xn xs -> vv λ yn ys -> vv λ zn zs -> ++assoc xn xs yn ys zn zs
  } where
  module N = MonoidOK natMonoidOK
  ++<> : (n : Nat) (xs : Vec X n) -> (n , xs) & (0 , <>) == (n , xs)
  ++<> zero <> = refl
  ++<> (suc n) (x , xs) = cong (vv λ m ys -> suc m , x , ys) (++<> n xs)

  ++assoc : forall xn (xs : Vec X xn) yn (ys : Vec X yn) zn (zs : Vec X zn) ->
    ((xn +Nat yn) +Nat zn , (xs ++ ys) ++ zs == xn +Nat (yn +Nat zn) , xs ++ (ys ++ zs))
  ++assoc 0 <> yn ys zn zs = refl
  ++assoc (suc n) (x , xs) yn ys zn zs = cong (vv λ m ys -> suc m , x , ys) (++assoc n xs yn ys zn zs)

{-
\begin{exe}[a not inconsiderable problem]
Find out what goes wrong when you try to state associativity of vector |++|,
let alone prove it. What does it tell you about our |==| setup?
\end{exe}
-}

record MonoidHom {X}{{MX : Monoid X}}{Y}{{MY : Monoid Y}}(f : X -> Y) : Set where
  field
    respNeut  :                 f neut == neut
    resp&     : forall x x' ->  f (x & x') == f x & f x'

fstHom : forall {X} -> MonoidHom {<! ListN !>N X}{Nat} fst
fstHom = record { respNeut = refl; resp& = \ _ _ -> refl }

record EndoFunctorOK F {{FF : EndoFunctor F}} : Set1 where
  field
    endoFunctorId  : forall {X} ->
      map {{FF}}{X} id == id
    endoFunctorCo  : forall {R S T}(f : S -> T)(g : R -> S) ->
      map {{FF}} f o map g == map (f o g)

{- fool'e errand
vecEndoFunctorOK : forall {n} -> EndoFunctorOK \ X -> Vec X n
vecEndoFunctorOK = record
  {  endoFunctorId  = {!!}
  ;  endoFunctorCo  = \ f g -> {!!}
  }
-}

_=1=_ :  forall {l}{S : Set l}{T : S -> Set l}
         (f g : (x : S) -> T x) -> Set l
f =1= g = forall x -> f x == g x
infix 1 _=1=_

record EndoFunctorOKP F {{FF : EndoFunctor F}} : Set1 where
  field
    endoFunctorId  : forall {X} ->
      map {{FF}}{X} id =1= id
    endoFunctorCo  : forall {R S T}(f : S -> T)(g : R -> S) ->
      map {{FF}} f o map g =1= map (f o g)

vecEndoFunctorOKP : forall {n} -> EndoFunctorOKP λ X -> Vec X n
vecEndoFunctorOKP {n} = record {
  endoFunctorId = okId n;
  endoFunctorCo = okComp n }
 where
  okId : forall {X} m -> (v : Vec X m) -> vapp (vec id) v == v
  okId zero <> = refl
  okId (suc m) (x , xs) = cong (_,_ x) (okId m xs)
  okComp : forall {R S T} m -> (f : S -> T)(g : R -> S)(v : Vec R m)
    -> vapp (vec f) (vapp (vec g) v) == vapp (vec (f o g)) v
  okComp zero _ _ <> = refl
  okComp (suc m) f g (x , xs) = cong (_,_ (f (g x))) (okComp m f g xs)

--\section{Laws for |Applicative| and |Traversable|}

record ApplicativeOKP F {{AF : Applicative F}} : Set1 where
  field
    lawId :   forall {X}(x : F X) ->
      pure {{AF}} id <*> x == x
    lawCo :   forall {R S T}(f : F (S -> T))(g : F (R -> S))(r : F R) ->
      pure {{AF}} (\ f g -> f o g) <*> f <*> g <*> r == f <*> (g <*> r)
    lawHom :  forall {S T}(f : S -> T)(s : S) ->
      pure {{AF}} f <*> pure s == pure (f s)
    lawCom :  forall {S T}(f : F (S -> T))(s : S) ->
      f <*> pure s == pure {{AF}} (\ f -> f s) <*> f
  applicativeEndoFunctorOKP : EndoFunctorOKP F {{applicativeEndoFunctor}}
  applicativeEndoFunctorOKP = record
    {  endoFunctorId = lawId
    ;  endoFunctorCo = \ f g r ->
         pure {{AF}} f <*> (pure {{AF}} g <*> r)
           << lawCo (pure f) (pure g) r !!=
         pure {{AF}} (\ f g -> f o g) <*> pure f <*> pure g <*> r
           =!! cong (\ x -> x <*> pure g <*> r) (lawHom (\ f g -> f o g) f) >>
         pure {{AF}} (_o_ f) <*> pure g <*> r 
           =!! cong (\ x -> x <*> r) (lawHom (_o_ f) g) >>
         pure {{AF}} (f o g) <*> r
           <QED>
    }


vecApplicativeOKP : {n : Nat} -> ApplicativeOKP \ X -> Vec X n
vecApplicativeOKP {n} = record {
  lawId = endoFunctorId;
  lawCo = co n;
  lawHom = hom n;
  lawCom = com n }
 where
  open EndoFunctorOKP (vecEndoFunctorOKP {n})
  co : forall {R S T} m -> (f : Vec (S -> T) m)(g : Vec (R -> S) m)(r : Vec R m)
    -> vec (λ f g -> f o g) <*> f <*> g <*> r == f <*> (g <*> r)
  co zero <> <> <> = refl
  co (suc m) (f , fs) (g , gs) (r , rs) = cong (_,_ (f (g r))) (co m fs gs rs)
  hom : forall {S T} m -> (f : S -> T)(s : S) -> vapp {m} (vec f) (vec s) == vec (f s)
  hom zero _ _ = refl
  hom (suc m) f s = cong (_,_ (f s)) (hom m f s)
  com : forall {S T} m -> (f : Vec (S -> T) m) (s : S) -> vapp f (vec s) == vapp (vec (λ f -> f s)) f
  com zero <> _ = refl
  com (suc m) (f , fs) s = cong (_,_ (f s)) (com m fs s)

--ApplicativeHomomorphisms

_-:>_ : forall (F G : Set -> Set) -> Set1
F -:> G = forall {X} -> F X -> G X

record AppHom  {F}{{AF : Applicative F}}{G}{{AG : Applicative G}}
               (k : F -:> G) : Set1 where
  field
    respPure  : forall {X}(x : X) -> k (pure x) == pure x
    respApp   : forall {S T}(f : F (S -> T))(s : F S) -> k (f <*> s) == k f <*> k s

monoidApplicativeHom :
  forall {X}{{MX : Monoid X}}{Y}{{MY : Monoid Y}}
  (f : X -> Y){{hf : MonoidHom f}} ->
  AppHom {{monoidApplicative {{MX}}}} {{monoidApplicative {{MY}}}} f
monoidApplicativeHom f {{hf}} = record
  {  respPure  = \ x -> MonoidHom.respNeut hf
  ;  respApp   = MonoidHom.resp& hf
  }

either : {A B : Set}{C : A + B -> Set}
  -> ((x : A) -> C (tt , x))
  -> ((y : B) -> C (ff , y))
  -> (xy : A + B) -> C xy
either f g (tt , x) = f x
either f g (ff , y) = g y

either' : {A B C : Set} -> (A -> C) -> (B -> C) -> (A + B -> C)
either' = either

mapEither : {A B A' B' : Set} -> (A -> A') -> (B -> B') -> (A + B) -> (A' + B')
mapEither f g = either (_,_ tt o f) (_,_ ff o g)

--Show that a homomorphism from |F| to |G| induces applicative structure
--on their pointwise sum.

homSum :  forall {F G}{{AF : Applicative F}}{{AG : Applicative G}} ->
          (f : F -:> G) -> 
          Applicative \ X -> F X + G X
homSum {F}{G}{{AF}}{{AG}} f = record {
  pure = λ x → tt , pure x;
  _<*>_ = ap }
 where
  ap : {S T : Set} -> F (S -> T) + G (S -> T) -> F S + G S -> F T + G T
  ap (tt , fst) (tt , fs) = tt , (fst <*> fs)
  ap fgst fgs = ff , (either' f id fgst <*> either' f id fgs)

homSumOKP :  forall {F G}{{AF : Applicative F}}{{AG : Applicative G}} ->
             ApplicativeOKP F -> ApplicativeOKP G ->
             (f : F -:> G) -> AppHom f ->
             ApplicativeOKP _ {{homSum f}}
homSumOKP {F}{G}{{AF}}{{AG}} FOK GOK f homf = record {
  lawId = lId;
  lawCo = co;
  lawHom = λ g s -> cong (_,_ tt) (FOK.lawHom g s);
  lawCom = com }
 where
  AS : Applicative λ X -> F X + G X
  AS = homSum f
  module FOK = ApplicativeOKP FOK
  module GOK = ApplicativeOKP GOK
  module HF = AppHom homf
  {- sometimes instance resolution is slow, so let's just be explicit -}
  pureF : {A : Set} -> A -> F A
  pureF = pure {{AF}}
  pureG : {A : Set} -> A -> G A
  pureG = pure {{AG}}
  _<*>F_ : {A B : Set} -> F (A -> B) -> F A -> F B
  _<*>F_ = _<*>_ {{AF}}
  _<*>G_ : {A B : Set} -> G (A -> B) -> G A -> G B
  _<*>G_ = _<*>_ {{AG}}
  infixl 2 _<*>F_ _<*>G_
  lId : forall {X} -> (x : F X + G X) -> pure {{AS}} id <*> x == x
  lId (tt , fx) = cong (_,_ tt) (FOK.lawId fx)
  lId {X} (ff , gx) rewrite HF.respPure (id {X = X}) = cong (_,_ ff) (GOK.lawId gx)
  compF : {A B C : Set} -> F ((B -> C) -> (A -> B) -> (A -> C))
  compF = pureF (λ f g -> f o g)
  fhomSum : {A B : Set} (x : F (A -> B) + G (A -> B)) (y : F A + G A)
    -> either' f id (x <*> y) == either' f id x <*> either' f id y
  fhomSum (tt , fab) (tt , fa) = HF.respApp fab fa
  fhomSum (tt , fab) (ff , ga) = refl
  fhomSum (ff , gab) (wa , fga) = refl
  co : forall {R S T} -> (fgst : F (S -> T) + G (S -> T))(fgrs : F (R -> S) + G (R -> S))(fgr : F R + G R)
    -> pure {{AS}} (λ f g -> f o g) <*> fgst <*> fgrs <*> fgr == fgst <*> (fgrs <*> fgr)
  co (tt , fst) (tt , frs) (tt , fr) = cong (_,_ tt) (FOK.lawCo fst frs fr)
  co (tt , fst) (tt , frs) (ff , gr) = cong (_,_ ff) (
    f (compF <*>F fst <*>F frs) <*>G gr
      =!! cong (λ grt → grt <*>G gr) (
        f (compF <*>F fst <*>F frs)
          =!! HF.respApp (compF <*>F fst) frs >>
        f (compF <*>F fst) <*>G f frs
          =!! cong (λ gst -> gst <*>G f frs) (
            f (compF <*>F fst)
              =!! HF.respApp compF fst >>
            f compF <*>G f fst
              =!! cong (λ p -> p <*>G f fst) (HF.respPure (λ f g -> f o g)) >>
            pureG (λ f g -> f o g) <*>G f fst
              <QED>) >>
        pureG (λ f g -> f o g) <*>G f fst <*>G f frs
          <QED>) >>
    pureG (λ f g -> f o g) <*>G f fst <*>G f frs <*>G gr
      =!! GOK.lawCo (f fst) (f frs) gr >>
    f fst <*>G (f frs <*>G gr)
      <QED>)
  co (tt , fst) (ff , grs) fgr = cong (_,_ ff) (
    f (compF <*>F fst) <*>G grs <*>G either f id fgr
      =!! cong (λ gst → gst <*>G grs <*>G either f id fgr) (
        f (compF <*>F fst)
          =!! HF.respApp compF fst >>
        f compF <*>G f fst
          =!! cong (λ p -> p <*>G f fst) (HF.respPure (λ f g -> f o g)) >>
        pureG (λ f g -> f o g) <*>G f fst
          <QED>) >>
    pureG (λ f g -> f o g) <*>G f fst <*>G grs <*>G either f id fgr
      =!! GOK.lawCo (f fst) grs (either f id fgr) >>
    f fst <*>G (grs <*>G either f id fgr)
      <QED>)
  co (ff , gst) fgrs fgr = cong (_,_ ff) (
    f compF <*>G gst <*>G either' f id fgrs <*>G either' f id fgr
      =!! cong (λ p -> p <*>G gst <*>G either' f id fgrs <*>G either' f id fgr) (HF.respPure (λ f g -> f o g)) >>
    pureG (λ f g -> f o g) <*>G gst <*>G either' f id fgrs <*>G either' f id fgr
      =!! GOK.lawCo gst (either f id fgrs) (either f id fgr) >>
    gst <*>G (either' f id fgrs <*>G either' f id fgr)
      << cong (λ gs → gst <*> gs) (fhomSum fgrs fgr) !!=
    gst <*>G either' f id (_<*>_ {{AS}} fgrs fgr)
      <QED>)
  com : {S T : Set} -> (g : F (S -> T) + G (S -> T)) (s : S)
    -> g <*> pure {{AS}} s == pure {{AS}} (λ h -> h s) <*> g
  com (tt , fst) s = cong (_,_ tt) (FOK.lawCom fst s)
  com (ff , gst) s = cong (_,_ ff) (
    gst <*> f (pure s)
      =!! cong (λ p -> gst <*> p) (HF.respPure s) >>
    gst <*> pure s
      =!! GOK.lawCom gst s >>
    pure {{AG}} (λ h -> h s) <*> gst
      << cong (λ p → p <*> gst) (HF.respPure (λ h -> h s)) !!=
    f (pure (λ h -> h s)) <*> gst
      <QED>)

-- traversable laws

record TraversableOKP F {{TF : Traversable F}} : Set1 where
  field
    lawId   :  forall  {X}(xs : F X) -> traverse {{TF}} id xs == xs
    lawCo   :  forall  {G}{{AG : Applicative G}}{H}{{AH : Applicative H}}
                       {R S T}(g : S -> G T)(h : R -> H S)(rs : F R) ->
               let  EH : EndoFunctor H ; EH = applicativeEndoFunctor
               in   map{H} (traverse {{TF}} g) (traverse {{TF}} h rs)
                      ==
                    traverse{{TF}}{{applicativeComp AH AG}} (map{H} g o h) rs
    lawHom  :  forall {G}{{AG : Applicative G}}{H}{{AH : Applicative H}}
                      (h : G -:> H){S T}(g : S -> G T) -> AppHom h ->
                      (ss : F S) ->
                      traverse {{TF}} (h o g) ss == h (traverse {{TF}} g ss)

-- fromNormal

Batch : Set -> Set -> Set
Batch X Y = Sg Nat \ n -> Vec X n -> Y

oneBatch : {X : Set} -> Batch X X
oneBatch {X} = 1 , k
 where
  k : Vec X 1 -> X
  k (x , <>) = x

applicativeBatch : {X : Set} -> Applicative (Batch X)
applicativeBatch {X} = record {
  pure = λ x -> 0 , pure x;
  _<*>_ = ap }
 where
  ap : {S T : Set}
    -> Sg Nat (λ n -> Vec X n -> S -> T)
    -> Sg Nat (λ n -> Vec X n -> S)
    -> Sg Nat (λ n -> Vec X n -> T)
  ap {S} {T} (m , f) (n , x) = m +Nat n , k
   where
    k : Vec X (m +Nat n) -> T
    k xsys with unAppend m n xsys
    k .(xs ++ ys) | from (xs , ys) = f xs (x ys)

{- This seems to need extensionality. Maybe I'm just doing it wrong.
applicativeBatchOK : {X : Set} -> ApplicativeOKP (Batch X)
applicativeBatchOK {X} = record {
  lawId = λ _ -> refl;
  lawCo = co;
  lawHom = λ _ _ -> refl;
  lawCom = vv com }
 where
  pureB : {S : Set} -> S -> Batch X S
  pureB = pure
  _<*>B_ : {S T : Set} -> Batch X (S -> T) -> Batch X S -> Batch X T
  _<*>B_ = _<*>_ {{applicativeBatch}}
  infixl 2 _<*>B_
  co : {R S T : Set} (f : Batch X (S -> T)) (g : Batch X (R -> S)) (r : Batch X R)
    -> pure (λ f g -> f o g) <*>B f <*>B g <*>B r == f <*>B (g <*>B r)
  co (nf , f) (ng , g) (nr , r) = {!!}
  empty-list : (v : Vec X 0) -> v == <>
  empty-list <> = refl
  com : {S T : Set} (nst : Nat) (b : Vec X nst -> S -> T) (s : S)
    -> nst , b <*>B pureB s == pureB (λ bf -> bf s) <*>B nst , b
  com zero b s = {!!}
  com (suc n) b s = {!!}
-}

fromNormal :  forall {F}{{TF : Traversable F}} -> TraversableOKP F ->
              forall {X} -> <! normalT F !>N X -> F X
fromNormal {F} {{TF}} tokf {X} (f1 , xs) = subst coherence (λ n -> Vec X n -> F X) (snd buildPlan) xs
 where
  f : One -> Batch X X
  f <> = oneBatch
  buildPlan : Batch X (F X)
  buildPlan = traverse f f1
  natApp : Applicative (λ _ -> Nat)
  natApp = monoidApplicative
  natFun : EndoFunctor (λ _ -> Nat)
  natFun = applicativeEndoFunctor
  fstBatchHom : AppHom {Batch X} fst
  fstBatchHom = record { respPure = λ _ → refl; respApp = λ _ _ → refl }
  module TOK = TraversableOKP tokf
  {- it actually doesn't matter a damn what g is, it only appears inside map {λ _ -> Nat} which ignores it -}
  g : X -> Nat
  g _ = 0
  coherence : fst buildPlan == sizeT {F} f1
  coherence =
    fst (traverse f f1)
      << TOK.lawHom {Batch X} {λ _ → Nat} fst f fstBatchHom f1 !!=
    traverse {F} {λ _ -> Nat} {One} {X} (fst o f) f1
      =!! refl >>
    map (traverse {F} {λ _ -> Nat} {X} {One} g) (traverse {F} {λ _ -> Nat} {One} {X} (fst o f) f1)
      =!! TOK.lawCo g (fst o f) f1 >>
    traverse {F} {λ _ -> Nat} {One} {One} (map g o (fst o f)) f1
      =!! refl >>
    sizeT {F} f1
      <QED>

-- fixpoints of normal functors

data Tree (N : Normal) : Set where
  <$_$> : <! N !>N (Tree N) -> Tree N

topShape : {N : Normal} -> Tree N -> Shape N
topShape <$ Sh , _ $> = Sh

NatT : Normal
NatT = Two / 0 <?> 1

zeroT : Tree NatT
zeroT = <$ tt , <> $>

sucT : Tree NatT -> Tree NatT
sucT n = <$ ff , n , <> $>

NatInd :  forall {l}(P : Tree NatT -> Set l) ->
          P zeroT ->
          ((n : Tree NatT) -> P n -> P (sucT n)) ->
          (n : Tree NatT) -> P n
NatInd P z s <$ tt , <>     $> = z
NatInd P z s <$ ff , n , <> $> = s n (NatInd P z s n)

head : forall {A m} -> Vec A (suc m) -> A
head (x , _) = x

tail : forall {A m} -> Vec A (suc m) -> Vec A m
tail (_ , xs) = xs

eq? : (N : Normal)(sheq? : (s s' : Shape N) -> Dec (s == s')) ->
      (t t' : Tree N) -> Dec (t == t')
eq? N sheq? <$ Sh1 , xs1 $> <$ Sh2 , xs2 $> with sheq? Sh1 Sh2
eq? N sheq? <$ Sh  , xs1 $> <$ .Sh , xs2 $> | tt , refl with vecEq? xs1 xs2
 where
  vecEq? : {n : Nat} (xs ys : Vec (Tree N) n) -> Dec (xs == ys)
  vecEq? {zero} <> <> = tt , refl
  vecEq? {suc n} (x , xs) (y , ys) with eq? N sheq? x y
  vecEq? {suc n} (x , xs) (.x , ys) | tt , refl with vecEq? xs ys
  vecEq? {suc n} (x , xs) (.x , .xs) | tt , refl | tt , refl = tt , refl
  vecEq? {suc n} (x , xs) (.x , ys) | tt , refl | ff , neq = ff , neq o cong tail
  vecEq? {suc n} (x , xs) (y , ys) | ff , neq = ff , neq o cong head
eq? N sheq? <$ Sh  , xs  $> <$ .Sh , .xs $> | tt , refl | tt , refl = tt , refl
eq? N sheq? <$ Sh  , xs1 $> <$ .Sh , xs2 $> | tt , refl | ff , neq = ff , neq o finish xs1 xs2
 where
  finish : (xs ys : Vec (Tree N) (size N Sh)) -> <$ Sh , xs $> == <$ Sh , ys $> -> xs == ys
  finish xs .xs refl = refl
eq? N sheq? <$ Sh1 , xs1 $> <$ Sh2 , xs2 $> | ff , neq = ff , neq o cong topShape
