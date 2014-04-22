
from pysetcomp.setcomp_z3 import *

import z3

I = z3.IntSort()
SHOW_TRANS = False

##############################################################################

x, z = z3.Ints('x z')
SetSort = mkSetSort( I )
es1, es2, es3 = z3.Consts('es1 es2 es3', SetSort)

cs = [es3 |Eq| VSet(I,1,2,3,4), es2 |Eq| VSet(I,10,20,30), es2 |Eq| Compre(x*10, x<=3, x, es3)]

checkSat( "Non-inj Comp Set Test A: Match"
         , cs, expected=z3.sat, show_trans=SHOW_TRANS)

##############################################################################

x, z = z3.Ints('x z')
SetSort = mkSetSort( I )
es1, es2, es3, es4 = z3.Consts('es1 es2 es3 es4', SetSort)

cs = [es3 |Eq| VSet(I,0,1,2,3,4), es2 |Eq| VSet(I,10,20,30), es4 |Eq| Compre(x*10, x<=3, x, es3), es2 == es4]

checkSat( "Non-inj Comp Set Test B: Non-Maximal"
         , cs, expected=z3.unsat, show_trans=SHOW_TRANS)

##############################################################################

x, z = z3.Ints('x z')
SetSort = mkSetSort( I )
es1, es2, es3 = z3.Consts('es1 es2 es3', SetSort)

cs = [es3 |Eq| VSet(I,1,2,3,4), es2 |Eq| VSet(I,0,10,20,30), es2 |Eq| Compre(x*10, x<=3, x, es3)]

checkSat( "Non-inj Comp Set Test C: Surplus range"
         , cs, expected=z3.unsat, show_trans=SHOW_TRANS)

##############################################################################

x, z = z3.Ints('x z')
SetSort = mkSetSort( I )
es1, es2, es3 = z3.Consts('es1 es2 es3', SetSort)

cs  = [es3 |Eq| VSet(I,3,6,7,8), es2 |Eq| VSet(I,0,1,2), es2 |Eq| Compre(x%3, x>=3, x, es3)]

checkSat( "Inj Comp Set Test A: Match"
         , cs, expected=z3.sat, show_trans=SHOW_TRANS)

##############################################################################

x, z = z3.Ints('x z')
SetSort = mkSetSort( I )
es1, es2, es3 = z3.Consts('es1 es2 es3', SetSort)

cs  = [es3 |Eq| VSet(I,3,6,7,8), es2 |Eq| VSet(I,0,2), es2 |Eq| Compre(x%3, x>=3, x, es3)]

checkSat( "Inj Comp Set Test B: Non-maximal"
         , cs, expected=z3.unsat, show_trans=SHOW_TRANS)

##############################################################################


x, z = z3.Ints('x z')
SetSort = mkSetSort( I )
es1, es2, es3 = z3.Consts('es1 es2 es3', SetSort)

cs  = [es3 |Eq| VSet(I,3,6,8), es2 |Eq| VSet(I,0,1,2), es2 |Eq| Compre(x%3, x>=3, x, es3)]

checkSat( "Inj Comp Set Test C: Surplus range"
         , cs, expected=z3.unsat, show_trans=SHOW_TRANS)

##############################################################################

x, z = z3.Ints('x z')
SetSort = mkSetSort( I )
es1, es2, es3 = z3.Consts('es1 es2 es3', SetSort)

cs  = [es3 |Eq| VSet(I,3,4,6,8), es2 |Eq| VSet(I,6,7), es2 |Eq| Compre(x+3, x<6, x, es3)]

checkSat( "Surj Comp Set Test A: Match"
         , cs, expected=z3.sat, show_trans=SHOW_TRANS)

##############################################################################

x, z = z3.Ints('x z')
SetSort = mkSetSort( I )
es1, es2, es3 = z3.Consts('es1 es2 es3', SetSort)

cs  = [es3 |Eq| VSet(I,1,3,4,6,8), es2 |Eq| VSet(I,6,7), es2 |Eq| Compre(x+3, x<6, x, es3)]

checkSat( "Surj Comp Set Test B: Non-maximal"
         , cs, expected=z3.unsat, show_trans=SHOW_TRANS)

##############################################################################

x, z = z3.Ints('x z')
SetSort = mkSetSort( I )
es1, es2, es3 = z3.Consts('es1 es2 es3', SetSort)

cs  = [es3 |Eq| VSet(I,3,4,6,8), es2 |Eq| VSet(I,3,6,7), es2 |Eq| Compre(x+3, x<6, x, es3)]

checkSat( "Surj Comp Set Test C: Surplus range"
         , cs, expected=z3.unsat, show_trans=SHOW_TRANS)

##############################################################################

IntPair = mkTupleSort( I, I )

tup = IntPair.tup
pi1 = IntPair.pi1

PSetSort = mkSetSort( IntPair )
ISetSort = mkSetSort( I )

es3 = z3.Const('es3', PSetSort)
es2 = z3.Const('es2', ISetSort)
x, y = z3.Ints('x y')
z = z3.Const('z', IntPair)

cs = [es3 |Eq| VSet(IntPair, tup(1,8), tup(2,5), tup(3,2), tup(3,4), tup(4,8))
     ,es2 |Eq| VSet(I,10,20,30)
     ,es2 |Eq| Compre(pi1(z)*10, pi1(z)<=3, z, es3)]

checkSat( "Tuple Set Test A: Match"
         , cs, expected=z3.sat, show_trans=SHOW_TRANS)

###############################################################################

IntPair = mkTupleSort( I, I )

tup = IntPair.tup
pi1 = IntPair.pi1

PSetSort = mkSetSort( IntPair )
ISetSort = mkSetSort( I )

es3 = z3.Const('es3', PSetSort)
es2 = z3.Const('es2', ISetSort)
x, y = z3.Ints('x y')
z = z3.Const('z', IntPair)

cs  = [es3 |Eq| VSet(IntPair, tup(1,8), tup(2,5), tup(3,2), tup(3,4), tup(4,8))
      ,es2 |Eq| VSet(I,10,20,30,40)
      ,es2 |Eq| Compre(pi1(z)*10, pi1(z)<=3, z, es3)]

checkSat( "Tuple Set Test B: Surplus range"
         , cs, expected=z3.unsat, show_trans=SHOW_TRANS)

################################################################################

x = z3.Int('x')
SetSort = mkSetSort( I )
es1, es2, es3 = z3.Consts('es1 es2 es3', SetSort) 

cs = [Compre(x, x!=x, x, es3) |Eq| Compre(x, x==x+1, x, es2)]

checkSat( "Empty Comp Set Test A: Empty sets are equal"
         , cs, expected=z3.sat, show_trans=SHOW_TRANS)
 
################################################################################

x = z3.Int('x')
SetSort = mkSetSort( I )
es1, es2, es3 = z3.Consts('es1 es2 es3', SetSort)  

cs = [es1 |Eq| Compre(x, x!=x, x, es3), es1 |Eq| Compre(x, x==x+1, x, es2), Not(IsEmpty(es1))]

checkSat( "Empty Comp Set Test B: Unsat comprehensions must be empty sets"
         , cs, expected=z3.unsat, show_trans=SHOW_TRANS)
 
##############################################################################

IntPair = mkTupleSort( I, I )

tup = IntPair.tup
pi1 = IntPair.pi1

PSetSort = mkSetSort( IntPair )
ISetSort = mkSetSort( I )

es3 = z3.Const('es3', PSetSort)
es2 = z3.Const('es2', ISetSort)
x, y = z3.Ints('x y')
z = z3.Const('z', IntPair)

# cs  = [es3 |Eq| (VSet(IntPair, tup(1,8), tup(2,5)) |union| VSet(IntPair, tup(3,2), tup(3,4), tup(4,8)) )] 
# cs += [es2 |Eq| VSet(I,10,20,30), es2 |Eq| Compre(pi1(z)*10, pi1(z)<=3, z, es3)]

cs  = [VSet(I,10,20,30) |Eq| Compre(pi1(z)*10, pi1(z)<=3, z, (VSet(IntPair, tup(1,8), tup(2,5)) |union| VSet(IntPair, tup(3,2), tup(3,4), tup(4,8)) ))]

checkSat( "Union Set Test A: Union Domain Match"
         , cs, expected=z3.sat, show_trans=SHOW_TRANS, prove_this=True)

##############################################################################

IntPair = mkTupleSort( I, I )

tup = IntPair.tup
pi1 = IntPair.pi1

PSetSort = mkSetSort( IntPair )
ISetSort = mkSetSort( I )

es3 = z3.Const('es3', PSetSort)
es2 = z3.Const('es2', ISetSort)
x, y = z3.Ints('x y')
z = z3.Const('z', IntPair)

cs  = [es3 |Eq| (VSet(IntPair, tup(1,8), tup(2,5), tup(0,5)) |union| VSet(IntPair, tup(3,2), tup(3,4), tup(4,8)) )] 
cs += [es2 |Eq| VSet(I,10,20,30), es2 |Eq| Compre(pi1(z)*10, pi1(z)<=3, z, es3)]

checkSat( "Union Set Test B: Union Domain non-maximality"
         , cs, expected=z3.unsat, show_trans=SHOW_TRANS)

##############################################################################

IntPair = mkTupleSort( I, I )

tup = IntPair.tup
pi1 = IntPair.pi1

PSetSort = mkSetSort( IntPair )
ISetSort = mkSetSort( I )

es3 = z3.Const('es3', PSetSort)
es2 = z3.Const('es2', ISetSort)
x, y = z3.Ints('x y')
z = z3.Const('z', IntPair)

cs  = [es3 |Eq| (VSet(IntPair, tup(1,8), tup(2,5)) |union| VSet(IntPair, tup(3,2), tup(3,4), tup(4,8)) )] 
cs += [es2 |Eq| VSet(I,0,10,20,30), es2 |Eq| Compre(pi1(z)*10, pi1(z)<=3, z, es3)]

checkSat( "Union Set Test C: Union Domain, Surplus range"
         , cs, expected=z3.unsat, show_trans=SHOW_TRANS)

##############################################################################

x = z3.Int('x')

SetSort = mkSetSort( I )
SetSetSort = mkSetSort( SetSort )

z = z3.Const('z', SetSort)
es2, es3 = z3.Consts('es2 es3', SetSetSort)

cs = [es3 |Eq| VSet(SetSort,VSet(I,1,2),VSet(I,2,3),VSet(I,1,5),VSet(I,3,8))
     ,es2 |Eq| VSet(SetSort,VSet(I,2,3),VSet(I,3,4))
     ,es2 |Eq| Compre(Compre(x+1, x==x, x, z), 2 |In| z, z, es3)]

checkSat( "Sets of Sets Comp Test A: Nested Comprehensions Match"
         , cs, expected=z3.sat, show_trans=SHOW_TRANS)

##############################################################################

x = z3.Int('x')

SetSort = mkSetSort( I )
SetSetSort = mkSetSort( SetSort )

z = z3.Const('z', SetSort)
es2, es3 = z3.Consts('es2 es3', SetSetSort)

cs = [es3 |Eq| VSet(SetSort,VSet(I,1,2),VSet(I,2,3),VSet(I,2,8),VSet(I,1,5),VSet(I,3,8))
     ,es2 |Eq| VSet(SetSort,VSet(I,2,3),VSet(I,3,4))
     ,es2 |Eq| Compre(Compre(x+1, x==x, x, z), 2 |In| z, z, es3)]

checkSat( "Sets of Sets Comp Test B: Nested Comprehensions Non-Maximality"
         , cs, expected=z3.unsat, show_trans=SHOW_TRANS)

##############################################################################

x = z3.Int('x')

SetSort = mkSetSort( I )
SetSetSort = mkSetSort( SetSort )

z = z3.Const('z', SetSort)
es2, es3 = z3.Consts('es2 es3', SetSetSort)

cs = [es3 |Eq| VSet(SetSort,VSet(I,1,2),VSet(I,2,3),VSet(I,1,5),VSet(I,3,8))
     ,es2 |Eq| VSet(SetSort,VSet(I,2,3),VSet(I,3,4),VSet(I,0,1,2))
     ,es2 |Eq| Compre(Compre(x+1, x==x, x, z), 2 |In| z, z, es3)]

checkSat( "Sets of Sets Comp Test C: Nested Comprehensions Surplus"
         , cs, expected=z3.unsat, show_trans=SHOW_TRANS)


##############################################################################

x = z3.Int('x')

SetSort = mkSetSort( I )

cs = [ AndCompre(x > 2, x, VSet(I,4,5,6)) ]

checkSat( "And Comprehension Test A: Match"
         , cs, expected=z3.sat, show_trans=SHOW_TRANS)

##############################################################################

x = z3.Int('x')

SetSort = mkSetSort( I )

cs = [ AndCompre(x > 2, x, VSet(I,1,4,5,6)) ]

checkSat( "And Comprehension Test B: Unsat"
         , cs, expected=z3.unsat, show_trans=SHOW_TRANS)

##############################################################################

SetSort = mkSetSort( I )
SetSetSort = mkSetSort( SetSort )

x = z3.Int('x')
s = z3.Const('s', SetSort)

cs = [ AndCompre( Compre(x+2,x<2,x,s) |Eq| Compre(x,x>=2,x,s) , s, VSet(SetSort,VSet(I,1,3),VSet(I,0,2))) ]

checkSat( "And Comprehension Test C: Nested comprehensions Match"
         , cs, expected=z3.sat, show_trans=SHOW_TRANS)

##############################################################################

SetSort = mkSetSort( I )
SetSetSort = mkSetSort( SetSort )

x = z3.Int('x')
s = z3.Const('s', SetSort)

cs = [ AndCompre( Compre(x+2,x<2,x,s) |Eq| Compre(x,x>=2,x,s) , s, VSet(SetSort,VSet(I,1,3),VSet(I,0,1))) ]

checkSat( "And Comprehension Test D: Nested comprehensions Unsat"
         , cs, expected=z3.unsat, show_trans=SHOW_TRANS)

##############################################################################

SetSort = mkSetSort( I )
SetSetSort = mkSetSort( SetSort )

x = z3.Int('x')
s = z3.Const('s', SetSort)

cs = [ OrCompre( Compre(x+2,x<2,x,s) |Eq| Compre(x,x>=2,x,s) , s, VSet(SetSort,VSet(I,1,3),VSet(I,0,1))) ]

checkSat( "Or Comprehension Test C: Nested comprehensions Match"
         , cs, expected=z3.sat, show_trans=SHOW_TRANS)

##############################################################################

SetSort = mkSetSort( I )
SetSetSort = mkSetSort( SetSort )

x = z3.Int('x')
s = z3.Const('s', SetSort)

cs = [ OrCompre( Compre(x+2,x<2,x,s) |Eq| Compre(x,x>=2,x,s) , s, VSet(SetSort,VSet(I,1,30),VSet(I,0,1))) ]

checkSat( "Or Comprehension Test C: Nested comprehensions Unsat"
         , cs, expected=z3.unsat, show_trans=SHOW_TRANS)

#############################################################################

SetSort = mkSetSort( I )

x  = z3.Int('x')
xs = z3.Const('xs', SetSort)

cs = [IsEmpty(Compre(x,x!=x,x,xs))]

checkSat( "Forall Comprehension Test A: Alway empty comprehension Match"
         , cs, expected=z3.sat, show_trans=True, prove_this=True)

#############################################################################

SetSort = mkSetSort( I )

x  = z3.Int('x')
xs,ys = z3.Consts('xs ys', SetSort)

cs = [ys |Eq| VSet(I,1,2,3), Forall([xs], IsEmpty(Compre(x,x==x,x,xs)) )]

checkSat( "Forall Comprehension Test A: Not always empty comprehension"
         , cs, expected=z3.unsat, show_trans=SHOW_TRANS)

#############################################################################

SetSort = mkSetSort( I )
x = z3.Int('x')
es1, es2, es3 = z3.Consts('es1 es2 es3', SetSort)

cs = [es3 |Eq| (Compre(x,x>=0,x,es1) |intersect| Compre(x,x<0,x,es2)), Not(IsEmpty(es3))] 

checkSat( "Intersection Comprehension Test A: Empty Intersection must be empty set" 
         , cs, expected=z3.unsat, show_trans=SHOW_TRANS)

#############################################################################

SetSort = mkSetSort( I )
x = z3.Int('x')
es1, es2, es3 = z3.Consts('es1 es2 es3', SetSort)

cs = [es3 |Eq| (Compre(x,x>=0,x,es1) |intersect| Compre(x,x<=0,x,es2)), Not(IsEmpty(es3)), Not(0 |In| es3)] 

checkSat( "Intersection Comprehension Test B: Excluding only member" 
         , cs, expected=z3.unsat, show_trans=SHOW_TRANS)

#############################################################################

SetSort = mkSetSort( I )
x, y = z3.Ints('x y')
es1, es2 = z3.Consts('es1 es2', SetSort)

cs = [y |In| Compre(x,x>=0,x,es1), y |In| Compre(x,x<0,x,es2)] 

checkSat( "Contra membership Comprehension Test A: Match" 
         , cs, expected=z3.unsat, show_trans=SHOW_TRANS)

#############################################################################

SetSort = mkSetSort( I )
x = z3.Int('x')
es1, es2 = z3.Consts('es1 es2', SetSort)

cs = [Compre(x,x>=0,x,es1) |Eq| Compre(x,x<0,x,es2), Not(IsEmpty(Compre(x,x>=0,x,es1)))] 

checkSat( "Equality of Comprehension Patterns Test A" 
         , cs, expected=z3.unsat, show_trans=SHOW_TRANS)

#############################################################################

SetSort = mkSetSort( I )
x, y = z3.Ints('x y')
es1, es2 = z3.Consts('es1 es2', SetSort)

cs = [Not(Compre(x,x>=0,x,es1) |Eq| Compre(x,x>=0,x,es1)), axiom_of_ext( I )] 

checkSat( "Equality of Comprehension Patterns Test B" 
         , cs, expected=z3.unsat, show_trans=SHOW_TRANS)

#############################################################################

SetSort = mkSetSort( I )
x = z3.Int('x')
es1 = z3.Const('es1', SetSort)

cs = [IsEmpty(Compre(x,x>=0,x,es1)), es1 |Eq| VSet(I,0)] #, axiom_of_ext( I )] #, es1 |Eq| VSet(I,0)]

checkSat( "Is Empty Test A"
         , cs, expected=z3.unsat, show_trans=SHOW_TRANS)


#############################################################################

SetSort = mkSetSort( I )
x = z3.Int('x')
es1 = z3.Const('es1', SetSort)

cs = [IsEmpty(Compre(x,x>0,x,VSet(I,0))) |implies| IsEmpty(Compre(x,x>=0,x,VSet(I,0)))] #, axiom_of_ext( I )] #, es1 |Eq| VSet(I,0)]

checkSat( "Implies Test A"
         , cs, expected=z3.unsat, show_trans=True)

#############################################################################

SetSort = mkSetSort( I )

cs = [Not(VSet(I,1,2) |subseteq| VSet(I,1,2,3))]

checkSat( "Not Test"
         , cs, expected=z3.unsat, show_trans=SHOW_TRANS )

#############################################################################

IntPair = mkTupleSort( I, I )

tup = IntPair.tup
pi1 = IntPair.pi1
pi2 = IntPair.pi2

PSetSort = mkSetSort( IntPair )

es = z3.Const('es', PSetSort)
x, y = z3.Consts('x y', IntPair)

cs = [y |In| (Compre(x,pi1(x)>pi2(x),x,es) |intersect| Compre(x,pi1(x)<pi2(x),x,es))]

checkSat( "Does not exist intersection Test A"
         , cs, expected=z3.unsat, show_trans=SHOW_TRANS)

'''
#############################################################################

SetSort = mkSetSort( I )
x = z3.Int('x')
es1 = z3.Const('es1', SetSort)

cs = [IsEmpty(Compre(x,x>=0,x,es1)) |implies| IsEmpty(Compre(x,x<=0,x,es1)), Not(IsEmpty(es1)), axiom_of_ext( I )] #, es1 |Eq| VSet(I,0)]

checkSat( "Implies Test B"
         , cs, expected=z3.unsat, show_trans=SHOW_TRANS)
'''

#############################################################################

SetSort = mkSetSort( I )
x = z3.Int('x')
es1 = z3.Const('es1', SetSort)

cs = [IsEmpty(Compre(x,x>0,x,es1)) |implies| IsEmpty(Compre(x,x>=0,x,es1)), es1 |Eq| VSet(I,0)]

checkSat( "Forall Implies Test A"
         , cs, expected=z3.unsat, show_trans=SHOW_TRANS)

#############################################################################

SetSort = mkSetSort( I )
x = z3.Int('x')
es1 = z3.Const('es1', SetSort)

cs = [Not(IsEmpty(Compre(x,x>0,x,es1)) |implies| IsEmpty(Compre(x,x>=0,x,es1)))]

checkSat( "Forall Implies Test B"
         , cs, expected=z3.sat, show_trans=SHOW_TRANS)


#############################################################################

SetSort = mkSetSort( I )
x = z3.Int('x')
es1 = z3.Const('es1', SetSort)

cs = [IsEmpty(Compre(x,x>=0,x,es1)) |implies| IsEmpty(Compre(x,x>0,x,es1))]

checkSat( "Forall Implies Test C"
         , cs, expected=z3.sat, show_trans=SHOW_TRANS, prove_this=False)

#############################################################################

SetSort = mkSetSort( I )
x,y = z3.Ints('x y')
es1,es2 = z3.Consts('es1 es2', SetSort)

cs = [y |In| (Compre(x,x%2==0,x,es1) |intersect| Compre(x,x%2==1,x,es2))]

checkSat( "Even and Odd Intersection"
        , cs, expected=z3.unsat, show_trans=SHOW_TRANS )

#############################################################################

SetSort = mkSetSort( I )
x = z3.Int('x')
es1 = z3.Const('es1', SetSort)

cs = [VSet(I,10,20,30) |Eq| Compre(x*10,x<4,x,es1)]

checkSat( "Infer set"
        , cs, expected=z3.sat, show_trans=True, show_model=True)

#############################################################################
IntPair = mkTupleSort( I, I )
tup = IntPair.tup
pi1 = IntPair.pi1

PSetSort = mkSetSort( IntPair )
ISetSort = mkSetSort( I )

ds = z3.Const('ds', PSetSort)
rs = z3.Const('rs', ISetSort)
xy = z3.Const('xy', IntPair)
x, y = z3.Ints('x y')

cs = [ds |Eq| VSet(IntPair, tup(1,8), tup(2,5), tup(3,2), tup(3,4), tup(4,8)) 
     ,rs |Eq| Compre(pi1(xy)*10, pi1(xy)<=3, xy, ds)
     ,(x * 10) |In| rs
     ,tup(x,y) |In| ds]

checkSat( "Another tuple test"
        , cs, expected=z3.sat, model_values=[x,y])

'''
#############################################################################

SetSort = mkSetSort( I )
x = z3.Int('x')
es1 = z3.Const('es1', SetSort)

cs = [ Forall([es1], IsEmpty(Compre(x,x>0,x,es1)) |implies| IsEmpty(Compre(x,x>=0,x,es1))), axiom_of_ext( I )] #, es1 |Eq| VSet(I,0)]

checkSat( "Forall Implies Test B"
         , cs, expected=z3.unsat, show_trans=True)

#############################################################################
'''
'''
## Attempt to invoke Russell's Paradox, but this results to a type error:
## 'In' relation requires two argument x and xs, such that xs is of type
## set of x's. 

SetSort = mkSetSort( I )
SetSetSort = mkSetSort( SetSort )

x  = z3.Const('x', SetSort)
es = z3.Const('es', SetSetSort)

cs = [(Compre(x, Not(x |In| x), x, es) |In| Compre(x, Not(x |In| x), x, es)) |iff| 
      Not(Compre(x, Not(x |In| x), x, es) |In| Compre(x, Not(x |In| x), x, es))]

checkSat( "Russell's Paradox"
         , cs, expected=z3.unsat, show_trans=SHOW_TRANS)
'''

