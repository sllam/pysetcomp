
'''
This file is part of pysetcomp.

pysetcomp is free software: you can redistribute it and/or modify
it under the terms of the GNU General Public License as published by
the Free Software Foundation, either version 3 of the License, or
(at your option) any later version.

pysetcomp is distributed in the hope that it will be useful,
but WITHOUT ANY WARRANTY; without even the implied warranty of
MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
GNU General Public License for more details.

You should have received a copy of the GNU General Public License
along with pysetcomp. If not, see <http://www.gnu.org/licenses/>.

pysetcomp, Prototype Alpha

Authors:
Edmund S. L. Lam      sllam@qatar.cmu.edu
Iliano Cervesato      iliano@cmu.edu

* This implementation was made possible by an NPRP grant (NPRP 09-667-1-100, Effective Programming 
for Large Distributed Ensembles) from the Qatar National Research Fund (a member of the Qatar 
Foundation). The statements made herein are solely the responsibility of the authors.
'''

import z3 as z3

from functools import partial

# Special thanks to Ferdinand Jamitzky, for infix operator recipe
# for Python:
# (http://code.activestate.com/recipes/384122-infix-operators/)
class Infix(object):
    def __init__(self, func):
        self.func = func
    def __or__(self, other):
        return self.func(other)
    def __ror__(self, other):
        return Infix(partial(self.func, other))
    def __call__(self, v1, v2):
        return self.func(v1, v2)

@Infix
def z3Implies(ps, cs):
	return z3.Implies(ps, cs)

def z3Exists(xs, f):
	if len(xs) > 0:
		return z3.Exists(xs, f)
	else:
		return f

def z3ForAll(xs, f):
	if len(xs) > 0:
		return z3.ForAll(xs, f)
	else:
		return f

# Generating ids

fresh_id = 0

def get_new_id():
	global fresh_id
	new_id = fresh_id 
	fresh_id += 1
	return new_id

def new_name( prefix ):
	return "%s%s" % (prefix,get_new_id())

# Sets

set_sort_dict = {}
set_elem_sort_dict = {}

def set_name(set_sort):
	return "set_%s" % set_sort.domain().name()

def setInfo(sort):
	return set_elem_sort_dict[sort.name()]

def setInfoFromSet(sort):
	return set_sort_dict[sort.name()]

def mkSetSort(sort):
	return setInfo(sort)['sort'] # set_elem_sort_dict[sort.name()]

def Set(n, sort):
	return z3.Const(n, setInfo(sort)['sort'])

def Sets(ns, sort):
	return z3.Consts(ns, setInfo(sort)['sort'])

def newSet(sort):
	return Set("s%s" % get_new_id(), sort)

def newSets(quantity, sort):
	ms = ' '.join( map(lambda _: "s%s" % get_new_id(),range(0,quantity)) )
	return Sets(ms, sort)

@Infix
def z3In(x, xs):
	mem_f = setInfoFromSet(xs.sort())['mem']
	return mem_f(x, xs)==True

def z3IsEmpty(xs):
	Elem = setInfoFromSet(xs.sort())['elem']
	x = z3.Const('x', Elem)
	return z3.Not( z3.Exists([x], x |z3In| xs) )

def setInfo(sort):
	if sort.name() not in set_elem_sort_dict:

		SetSort = z3.DeclareSort('mset_%s' % sort.name())

		mem_f      = z3.Function( 'mem_f_%s' % sort.name(), sort, SetSort, z3.BoolSort() )

		set_info = { 'sort':SetSort, 'elem':sort, 'mem':mem_f }
		set_sort_dict[SetSort.name()]   = set_info 
		set_elem_sort_dict[sort.name()] = set_info

	return set_elem_sort_dict[sort.name()]

# Tuples

tuple_sort_dict = {}

def tupleInfo(*sorts):
	name = 'Tup_' + '_'.join(map(lambda sort: sort.name(),sorts))
	if name not in tuple_sort_dict:
		Tuple = z3.Datatype(name)
		sort_sigs = []
		idx = 1
		for sort in sorts:
			sort_sigs.append( ('pi%s' % idx,sort) )
			idx += 1
		Tuple.declare('tup', *sort_sigs)
		Tuple = Tuple.create()
		tupInfo = { 'sort':Tuple, 'tup':Tuple.tup }
		for idx in range(1,len(sorts)+1):
			tupInfo['pi%s' % idx] = getattr(Tuple,'pi%s' % idx)
		tuple_sort_dict[name] = tupInfo
	return tuple_sort_dict[name]

def mkTupleSort(*sorts):
	return tupleInfo(*sorts)['sort']

def Tuple(n, *sorts):
	Tup = tupleInfo(*sorts)['sort']
	return z3.Const(n, Tup)

def Tuples(ns, *sorts):
	Tup = tupleInfo(*sorts)['sort']
	return z3.Consts(ns, Tup)

def mk_tup(*args):
	sorts = map(lambda arg: arg.sort() ,args)
	Tuple = tupleInfo(*sorts)['sort']
	return Tuple.tup(*args)

# Lists

list_sort_dict = {}
list_elem_sort_dict = {}

def listInfo(sort):
	name = sort.name()
	if name not in list_elem_sort_dict:
		List = z3.Datatype('List_' + sort.name())
		List.declare('cons', ('head', sort), ('tail', List))
		List.declare('nil')
		List = List.create()
		linfo = { 'sort':List, 'elem':sort, 'cons':List.cons, 'nil':List.nil }
		list_elem_sort_dict[name]   = linfo
		list_sort_dict[List.name()] = linfo
	return list_elem_sort_dict[name]

def listInfoFromList(sort):
	return list_sort_dict[sort.name()]

def mkListSort(sort):
	return listInfo(sort)['sort']

def List(n, sort):
	List = listInfo(sort)['sort']
	return z3.Const(n, List)

def Lists(ns, sort):
	List = listInfo(sort)['sort']
	return z3.Consts(ns, List)

def VList(sort, *args):
	List = listInfo(sort)['sort']
	ls = List.nil
	index = len(args)-1
	while index >= 0:
		ls = List.cons(args[index], ls)
		index -= 1
	return ls
		

# Term combinators
# Non-z3 terms are of 'dict' type.

COMPRE_SET  = 0
VANILLA_SET = 1
EQ_OP = 2
IN_OP = 3
NOT_OP = 4
EMPTY_OP = 5
UNION_OP = 6
SUBSETEQ_OP = 7
FORALL_OP = 8
EXIST_OP = 9
AND_COMP_OP = 10
OR_COMP_OP = 11
IFF_OP = 12
IMPLIES_OP = 13
INTERSECT_OP = 14
DIFF_OP = 15
AND_OP = 16
OR_OP = 17

class Term:
	def initialize(self,tid):
		self.tid = tid

class Formula:
	def initialize(self,fid):
		self.fid = fid

# { fx | gx }_(x in dom)
class Compre(Term):
	def __init__(self, tp, tg, x, td):
		self.initialize(COMPRE_SET)
		self.comp_pat = tp
		self.guard    = tg
		self.binder   = x
		self.domain   = td
	def __repr__(self):
		return "{ %s | %s }_(%s in %s)" % (self.comp_pat, self.guard, self.binder, self.domain)

class VSet(Term):
	def __init__(self, sort, *args):
		self.initialize(VANILLA_SET)
		self.sort = sort
		self.args = args
	def __repr__(self):
		return "{%s}" % (','.join(map(lambda a: "%s" % a, self.args)))

class CUnion(Term):
	def __init__(self, t1, t2):
		self.initialize(UNION_OP)
		self.term1 = t1
		self.term2 = t2
	def __repr__(self):
		return "%s \'union\' %s" % (self.term1, self.term2)
@Infix
def union(t1, t2):
	return CUnion(t1,t2)

class CIntersect(Term):
	def __init__(self, t1, t2):
		self.initialize(INTERSECT_OP)
		self.term1 = t1
		self.term2 = t2
	def __repr__(self):
		return "%s \'intersect\' %s" % (self.term1, self.term2)
@Infix
def intersect(t1, t2):
	return CIntersect(t1,t2)

class CDiff(Term):
	def __init__(self, t1, t2):
		self.initialize(DIFF_OP)
		self.term1 = t1
		self.term2 = t2
	def __repr__(self):
		return "%s \'diff\' %s" % (self.term1, self.term2)
@Infix
def diff(t1, t2):
	return CDiff(t1,t2)

# /\_(x in td) { fg }
class AndCompre(Formula):
	def __init__(self, fg, x, td):
		self.initialize(AND_COMP_OP)
		self.form = fg
		self.binder = x
		self.domain = td
	def __repr__(self):
		return "/\_(%s in %s) (%s)" % (self.binder, self.domain, self.form)

# \/_(x in td) { fg }
class OrCompre(Formula):
	def __init__(self, fg, x, td):
		self.initialize(OR_COMP_OP)
		self.form = fg
		self.binder = x
		self.domain = td
	def __repr__(self):
		return "\/_(%s in %s) (%s)" % (self.binder, self.domain, self.form)

class CEq(Formula):
	def __init__(self, t1, t2):
		self.initialize(EQ_OP)
		self.term1 = t1
		self.term2 = t2
	def __repr__(self):
		return "%s == %s" % (self.term1, self.term2) 
@Infix
def Eq(t1, t2):
	return CEq(t1,t2)

class CIn(Formula):
	def __init__(self, t1, t2):
		self.initialize(IN_OP)
		self.term1 = t1
		self.term2 = t2
	def __repr__(self):
		return "%s in %s" % (self.term1, self.term2)
@Infix
def In(t1, t2):
	return CIn(t1,t2)

class Not(Formula):
	def __init__(self, fg):
		self.initialize(NOT_OP)
		self.form = fg
	def __repr__(self):
		return "not(%s)" % (self.form)

class IsEmpty(Formula):
	def __init__(self, fg):
		self.initialize(EMPTY_OP)
		self.form = fg
	def __repr__(self):
		return "empty(%s)" % (self.form)

class CSubsetEq(Formula):
	def __init__(self, t1, t2):
		self.initialize(SUBSETEQ_OP)
		self.term1 = t1
		self.term2 = t2
	def __repr__(self):
		return "%s C= %s" % (self.term1, self.term2)
@Infix
def subseteq(t1, t2):
	return CSubsetEq(t1,t2)

class Forall(Formula):
	def __init__(self, xs, fg):
		self.initialize(FORALL_OP)
		self.vars = xs
		self.form = fg
	def __repr__(self):
		return "forall %s.(%s)" % (','.join(map(lambda v: "%s" % v,self.vars)), self.form)

class Exists(Formula):
	def __init__(self, xs, fg):
		self.initialize(EXIST_OP)
		self.vars = xs
		self.form = fg
	def __repr__(self):
		return "exists %s.(%s)" % (','.join(map(lambda v: "%s" % v,self.vars)), self.form)

class Iff(Formula):
	def __init__(self, cs1, cs2):
		self.initialize(IFF_OP)
		self.form1 = cs1
		self.form2 = cs2
	def __repr__(self):
		return "%s <-> %s" % (self.form1, self.form2)
@Infix
def iff(cs1, cs2):
	return Iff(cs1,cs2)

class Implies(Formula):
	def __init__(self, cs1, cs2):
		self.initialize(IMPLIES_OP)
		self.form1 = cs1
		self.form2 = cs2
	def __repr__(self):
		return "%s -> %s" % (self.form1, self.form2)
@Infix
def implies(cs1, cs2):
	return Implies(cs1,cs2)

class CAnd(Formula):
	def __init__(self, f1, f2):
		self.initialize(AND_OP)
		self.form1 = f1
		self.form2 = f2
	def __repr__(self):
		return "%s /\ %s" % (self.form1, self.form2)
@Infix
def And(f1, f2):
	return CAnd(f1, f2)

class COr(Formula):
	def __init__(self, f1, f2):
		self.initialize(OR_OP)
		self.form1 = f1
		self.form2 = f2
	def __repr__(self):
		return "%s \/ %s" % (self.form1, self.form2)
@Infix
def Or(f1, f2):
	return COr(f1, f2)

######## Trans Term #########

# sTerm  -->  z3Term , [z3Form] , signature
def transTerm(sTerm, trans_pref):
	if isinstance(sTerm, Compre):
		return transCompre(sTerm.comp_pat, sTerm.guard, sTerm.binder, sTerm.domain, trans_pref)
	elif isinstance(sTerm, VSet):
		return transVanilla(sTerm.sort, sTerm.args, trans_pref)
	elif isinstance(sTerm, CUnion):
		return transUnion(sTerm.term1, sTerm.term2, trans_pref)
	elif isinstance(sTerm, CIntersect):
		return transIntersect(sTerm.term1, sTerm.term2, trans_pref)
	elif isinstance(sTerm, CDiff):
		return transDiff(sTerm.term1, sTerm.term2, trans_pref)
	else: # Assume it to be z3 Term
		return (sTerm, [], [])


# sForm   -->   z3Form, [z3Form], signature
def transForm(sForm, trans_pref):
	if isinstance(sForm, CEq):
		if trans_pref['use_set_eq']:
			(tt1, t1_cons, t1_sigs) = transTerm( sForm.term1, trans_pref )
			(tt2, t2_cons, t2_sigs) = transTerm( sForm.term2, trans_pref )
			return (tt1 == tt2, t1_cons + t2_cons, t1_sigs + t2_sigs)
		else:
			(ss1_cons, t1_cons, t1_sigs) = transSubseteq(sForm.term1, sForm.term2, trans_pref)
			(ss2_cons, t2_cons, t2_sigs) = transSubseteq(sForm.term2, sForm.term1, trans_pref)
			return (z3.And(ss1_cons,ss2_cons), t1_cons + t2_cons, t1_sigs + t2_sigs)
	elif isinstance(sForm, CIn):
		(tt1, t1_cons, t1_sigs) = transTerm( sForm.term1, trans_pref )
		(tt2, t2_cons, t2_sigs) = transTerm( sForm.term2, trans_pref )
		return (tt1 |z3In| tt2, t1_cons + t2_cons, t1_sigs + t2_sigs)
	elif isinstance(sForm, Not):
		(tForm, cons, t_sigs) = transForm( sForm.form, trans_pref )
		return (z3.Not(tForm), cons, t_sigs)
		# return (z3.Not(z3.And([tForm]+cons)), [], t_sigs)
	elif isinstance(sForm, IsEmpty):
		(tt, t_cons, t_sigs) = transTerm( sForm.form, trans_pref )
		return (z3IsEmpty(tt), t_cons, t_sigs)
	elif isinstance(sForm, CSubsetEq):
		return transSubseteq(sForm.term1, sForm.term2, trans_pref)
	elif isinstance(sForm, Forall):
		(tForm, cons, t_sigs) = transForm( sForm.form, trans_pref )
		return (z3.ForAll(sForm.vars, z3.And([tForm]+cons)), [], t_sigs)
	elif isinstance(sForm, Exists):
		(tForm, cons, t_sigs) = transForm( sForm.form, trans_pref )
		return (z3.Exists(sForm.vars, z3.And([tForm]+cons)), [], t_sigs)
	elif isinstance(sForm, AndCompre):
		return transAndCompre(sForm.form, sForm.binder, sForm.domain, trans_pref)
	elif isinstance(sForm, OrCompre):
		return transOrCompre(sForm.form, sForm.binder, sForm.domain, trans_pref)
	elif isinstance(sForm, Iff):
		(tForm1, f1_cons, f1_sigs) = transForm( sForm.form1, trans_pref )
		(tForm2, f2_cons, f2_sigs) = transForm( sForm.form2, trans_pref )
		return (tForm1 == tForm2, f1_cons + f2_cons, f1_sigs + f2_sigs)
	elif isinstance(sForm, Implies):
		(tForm1, f1_cons, f1_sigs) = transForm( sForm.form1, trans_pref )
		(tForm2, f2_cons, f2_sigs) = transForm( sForm.form2, trans_pref )
		# return (z3.And([tForm1]+f1_cons) |z3Implies| z3.Exists(f2_sigs,z3.And([tForm2]+f2_cons)), [], f1_sigs)
		return (tForm1 |z3Implies| z3Exists(f2_sigs,z3.And([tForm2]+f2_cons)), f1_cons, f1_sigs)
		# return (tForm1 |z3Implies| tForm2, f1_cons + f2_cons, f1_sigs + f2_sigs)
	elif isinstance(sForm, CAnd):
		(tForm1, f1_cons, f1_sigs) = transForm( sForm.form1, trans_pref )
		(tForm2, f2_cons, f2_sigs) = transForm( sForm.form2, trans_pref )
		return (z3.And(tForm1,tForm2) , f1_cons + f2_cons, f1_sigs + f2_sigs)
	elif isinstance(sForm, COr):
		(tForm1, f1_cons, f1_sigs) = transForm( sForm.form1, trans_pref )
		(tForm2, f2_cons, f2_sigs) = transForm( sForm.form2, trans_pref )
		return (z3.Or(tForm1,tForm2) , f1_cons + f2_cons, f1_sigs + f2_sigs)
	else:
		return (sForm, [], [])

# rge == { pt | gt }_(x in dt)
def transCompre(pt, gt, x, dt, trans_pref):
	(tpt, pt_cons, pt_sig) = transTerm(pt, trans_pref)
	(tgt, gt_cons, gt_sig) = transForm(gt, trans_pref)
	(tdt, dt_cons, dt_sig) = transTerm(dt, trans_pref)
	
	SetSort = mkSetSort( tpt.sort() )
	rge  = z3.Const(new_name('rge'), SetSort)

	# Comprehension Domain Inclusion : Every x in dt must participate in comprehension (Maximality)
	# i.e. { pt | gt }_(x in dt)    subset of   rge
	# Maximality        : forall x. (exists gt_sig. x in tdt /\ tgt) <=> exists pt_sig. tpt in rge /\ pt_cons

	# z = z3.Const(new_name('z'), tpt.sort())
	# dom_incl = z3.ForAll([x], z3Exists(gt_sig, z3.And([tgt,x |z3In| tdt]+gt_cons)) == z3Exists([z]+pt_sig, z3.And([z==tpt,z |z3In| rge] + pt_cons) ) )

	dom_incl = z3.ForAll([x]+gt_sig, z3.And([tgt,x |z3In| tdt]+gt_cons) |z3Implies| z3Exists(pt_sig, z3.And([tpt |z3In| rge] + pt_cons) ) )
	
	# Comprehension Range Restriction: Every z in rge of comprehension must map to some x in dt (No surplus)
	# i.e. rge   subset of    { pt | gt }_(x in dt)
	# Range Restriction : forall z. z in rge => exists x,pt_sig,gt_sig. z = tpt /\ tgt /\ x in tdt /\ pt_cons
	z = z3.Const(new_name('z'), tpt.sort())
	rge_res = z3.ForAll([z], (z |z3In| rge) |z3Implies| z3.Exists([x] + pt_sig + gt_sig, z3.And([z==tpt,tgt,x |z3In| tdt] + gt_cons + pt_cons) ) )

	# rge_res = z3.ForAll([z], z3.Exists([x] + pt_sig + gt_sig, z3.And(gt_cons + pt_cons + [(z |z3In| rge) == z3.And(z==tpt,tgt,x |z3In| tdt)]) ))

	return ( rge, dt_cons + [dom_incl,rge_res], [rge] + dt_sig )


def transVanilla(sort, ts, trans_pref):
	
	SetSort = mkSetSort( sort )
	ms = z3.Const(new_name('ms'), SetSort)
	z  = z3.Const('z',sort)
	t_sigs = []
	t_ctxt = []
	choices = []
	for t in ts:
		(tt, t_cons, t_sig) = transTerm(t, trans_pref)
		t_sigs += t_sig
		t_ctxt += t_cons
		choices.append( z == tt )
	ms_cons = [z3.ForAll([z], (z |z3In| ms) == z3.Or( choices ) )] + t_ctxt
	
	return (ms, ms_cons, [ms] + t_sigs)

def transUnion(t1, t2, trans_pref):
	(tt1, t1_cons, t1_sig) = transTerm(t1, trans_pref)
	(tt2, t2_cons, t2_sig) = transTerm(t2, trans_pref)
	SetSort  = setInfoFromSet( tt1.sort() )['sort']
	ElemSort = setInfoFromSet( tt1.sort() )['elem']
	ms = z3.Const(new_name('ms'), SetSort)
	z  = z3.Const('z',ElemSort)	

	u_cons = z3.ForAll([z], (z |z3In| ms) == z3.Or(z |z3In| tt1, z |z3In| tt2))

	return (ms, [u_cons] + t1_cons + t2_cons, [ms] + t1_sig + t2_sig )

def transIntersect(t1, t2, trans_pref):
	(tt1, t1_cons, t1_sig) = transTerm(t1, trans_pref)
	(tt2, t2_cons, t2_sig) = transTerm(t2, trans_pref)
	SetSort  = setInfoFromSet( tt1.sort() )['sort']
	ElemSort = setInfoFromSet( tt1.sort() )['elem']
	ms = z3.Const(new_name('ms'), SetSort)
	z  = z3.Const('z',ElemSort)	

	u_cons = z3.ForAll([z], (z |z3In| ms) == z3.And(z |z3In| tt1, z |z3In| tt2))

	return (ms, [u_cons] + t1_cons + t2_cons, [ms] + t1_sig + t2_sig )

def transDiff(t1, t2, trans_pref):
	(tt1, t1_cons, t1_sig) = transTerm(t1, trans_pref)
	(tt2, t2_cons, t2_sig) = transTerm(t2, trans_pref)
	SetSort  = setInfoFromSet( tt1.sort() )['sort']
	ElemSort = setInfoFromSet( tt1.sort() )['elem']
	ms = z3.Const(new_name('ms'), SetSort)
	z  = z3.Const('z',ElemSort)	

	u_cons = z3.ForAll([z], (z |z3In| ms) == z3.And(z |z3In| tt1, z3.Not(z |z3In| tt2)))

	return (ms, [u_cons] + t1_cons + t2_cons, [ms] + t1_sig + t2_sig )

def transSubseteq(t1, t2, trans_pref):
	(tt1, t1_cons, t1_sig) = transTerm(t1, trans_pref)
	(tt2, t2_cons, t2_sig) = transTerm(t2, trans_pref)
	ElemSort = setInfoFromSet( tt1.sort() )['elem']
	z  = z3.Const('z',ElemSort)
	
	# forall z. z in tt1 ==> z in tt2
	ss_cons = z3.ForAll([z], (z |z3In| tt1) |z3Implies| (z |z3In| tt2) )

	return (ss_cons, t1_cons + t2_cons, t1_sig + t2_sig)

def transAndCompre(gt, x, dt, trans_pref):
	(tdt, dt_cons, dt_sig) = transTerm(dt, trans_pref)
	(tgt, gt_cons, gt_sig) = transForm(gt, trans_pref)
	
	# forall x. (x in tdt) ==> exists gt_sig. tgt
	if len(gt_sig) > 0:
		gt_form = z3.ForAll([x], (x |z3In| tdt) |z3Implies| z3.Exists(gt_sig, z3.And([tgt]+gt_cons)) )
	else:
		gt_form = z3.ForAll([x], (x |z3In| tdt) |z3Implies| z3.And([tgt]+gt_cons) )
	return (gt_form, dt_cons, dt_sig)

def transOrCompre(gt, x, dt, trans_pref):
	(tdt, dt_cons, dt_sig) = transTerm(dt, trans_pref)
	(tgt, gt_cons, gt_sig) = transForm(gt, trans_pref)
	
	# exists x, gt_sig. (x in tdt /\ tgt)
	gt_form = z3.Exists([x] + gt_sig, z3.And([x |z3In| tdt,tgt]+gt_cons))

	return (gt_form, dt_cons, dt_sig)

def axiom_of_ext(sort):
	SetSort = mkSetSort( sort )
	x = z3.Const('x', sort)
	ys, zs = z3.Consts('ys zs', SetSort)
	return z3.ForAll([x,ys,zs], ((x |z3In| ys) == (x |z3In| zs)) |z3Implies| (ys == zs) )

def checkSat(test_name, constrs, expected=z3.sat, model_values=[], show_trans=True, test_details=None, use_set_eq=False, show_model=False, prove_this=False):

	z3constr = []

	trans_pref = { 'use_set_eq':use_set_eq }	

	tforms = []
	gammas = []
	sigs   = []

	for cons in constrs:
		(tform, tcons, sig) = transForm( cons, trans_pref )

		sigs += sig
		tforms += [tform]
		gammas += tcons

		# tcons = z3Exists(sig, z3.And([tform] + tcons))
		z3constr += [tform] + tcons

	s = z3.Solver()
	s.add(*z3constr)
	solver_ans = s.check()

	print "=============== %s ===============" % test_name
	
	# print "%s" % test_details

	if test_details == None:
		print "Query Formula: %s" % constrs
	else:
		print test_details

	if show_trans:
		print "Translated Formula:\n%s" % z3constr

	result = "\033[32m(Correct!)\033[0m" if solver_ans==expected else "\033[31m(Wrong!)\033[0m"
	print "Answer: Solver -> %s, Expected -> %s %s" % (solver_ans, expected, result)

	if prove_this:
		if len(gammas) > 0:
			if show_trans:
				print z3ForAll(sigs, z3.And(gammas) |z3Implies| z3.And(tforms))
			z3.prove(z3ForAll(sigs, z3.And(gammas) |z3Implies| z3.And(tforms)))
		else:
			z3.prove(z3.And(tforms))	

	if solver_ans == z3.sat:
		m = s.model()
		# print m
		if show_model:
			print "A model:\n%s" % m
		else:
			for val in model_values:
				print "%s -> %s" % (val,m[val])
	

	print "========================================================\n"


