######################################################################################################################################
#
#  AUXILIAR FUNCTIONS
#
######################################################################################################################################

# Given an integer n and a set of primes pi, the function computes and returns the pi-part of n.
PiPartOfAnInteger := function(n, pi)

	local npi, p, divides, divisor;

	if not (n in Integers and Filtered(pi, p->p in Integers and IsPrime(p))=pi) then
	  Print("Error: The input must be an integer followed by a list of primes in PiPartOfAnInteger\n");
	  return fail;
	fi;

	npi:=1;
	for p in pi do
		divides := n mod p = 0;
		divisor:= 1;
		while divides do
			divisor := divisor*p;
			divides := n mod (divisor*p) = 0;
		od;
		npi := npi* divisor;
	od;
	return npi;

end;


###############################################################
# This function computes the sum of the powers a^i for 0\le i < m.

Ese := function(a,m)
  local f, i;
  for i in [1..a^m] do
    f:=1+1;
  od;
  if a=1 then 
    return m;
  else
    return (a^m-1)/(a-1);
  fi;
end;


###############################################################
# This function computes the pi part of a group element.

PiPart := function(g,pi)

  local m,mpi,mpip,x;

  m := Order(g);

  if not m in Integers and ForAll(pi,IsPrimeInt) then
    Print("Error: The input must be a group element of finite order followed by a list of prime integers in PiPart\n");
    return fail;
  fi;

  mpi := PiPartOfAnInteger(m,pi);
  mpip := m/mpi;

  x := Gcdex(mpi,mpip);

  return g^(mpip*x.coeff2);

end;


######################################################################################################################################
# In this function we check the second part of condition (D) over o of Lemma 5.1. We check that for every prime q in pi' 
# for which gcd(o,q-1)=1 there is a prime p in pi(n) intersection pi' for which p divides q-1.
ConditionOvero := function(piprime, pin, o)

	local q;

	if not (o in Integers and Filtered(pin, p->p in Integers and IsPrime(p))=pin and
	 Filtered(piprime, p->p in Integers and IsPrime(p))=piprime) then
	  Print("Error: The input must be two lists of prime integers followed by an integer in ConditionOvero \n");
	  return fail;
	fi;

	for q in piprime do
		if GcdInt(o,q-1) = 1 then
			if Filtered(IntersectionSet(piprime, pin), p->GcdInt(p,q-1)=p) = [] then
				return false;
			fi;
		fi;
	od;

	return true;

end;

######################################################################################################################################
# We use this function to get the set of parameters IN(G) defined in Lemma 5.1 for any possible metacyclic group of size "size". A summary of the function is the following: We take each possible divisor of "size" as m, then n=size/m, and we take pi' as any possible subset of the primes that divide m (because of the definition of pi'). With these parameters fixed, we take the candidates for s, r and o that satisfy the properties (A) and (D) of the Lemma that only involve them and m, n and pi, this is, all of the conditions except mpi dividing r*s. Then we go over each of them, we fix them and we see that this property is also satisfied. At last, with these parameters fixed, we separate cases for epsilon and we make sure that conditions (B) and (C) are also satisfied.

ListIn := function(size)

	local listIn, divm, i, m, n, o, s, r, x,  possibilitiespi, iter, piprime, lists, listo, listr, listr2, piwithout2, pi, mpi, mpiprime, rp, sp, op, r2, s2, o2, conditionOk, m2, n2, primeDivm, primeDivn, q, p, listaux, possibilities;

	if not (size in Integers and size>0) then
	  Print("Error: The input must be a positive integer in ListIn \n");
	  return fail;
	fi;
	
	listIn:= [];

	divm:= DivisorsInt(size);
	for i in [1..Size(divm)] do
		m:= divm[i];
		n:= size/m;
		listr:= Filtered(DivisorsInt(m), r-> (r*n) mod PiPartOfAnInteger(m, PrimeDivisors(r)) = 0);
		if m mod 4 = 0 then
			listr:= Filtered(listr, r-> r mod 4 = 0);
		fi;
		for r in listr do
			primeDivm := PrimeDivisors(m);
			primeDivn := PrimeDivisors(n);

			piprime := Difference(primeDivm, PrimeDivisors(r));
			pi := Filtered(Union(primeDivm, primeDivn), p-> not p in piprime);
			piwithout2 := Filtered(pi, p-> p<>2 );

			mpiprime:= PiPartOfAnInteger(m,piprime);
			mpi:= PiPartOfAnInteger(m,pi);

			lists:= Filtered(DivisorsInt(m), s-> PiPartOfAnInteger(s, piprime)=mpiprime and 
				n mod PiPartOfAnInteger(s,piwithout2) = 0 and (r*s) mod mpi = 0);
			listaux := List(piprime, q-> q-1);
			if listaux=[] then 
				listaux:=[1]; 
			fi;
			
			listo:= Filtered(DivisorsInt(PiPartOfAnInteger(n,pi)), o-> Lcm(listaux) mod o = 0 and
				ConditionOvero(piprime, primeDivn, o));
			for s in lists do
				for o in listo do
					conditionOk:= true;
					for p in piwithout2 do
						rp:= PiPartOfAnInteger(r,[p]);
						sp:= PiPartOfAnInteger(s,[p]);
						op:= PiPartOfAnInteger(o,[p]);
						if not (s mod rp = 0 or GcdInt(sp*op,n)<>sp*op) then
							conditionOk:=false;
						fi;
					od;
					r2:= PiPartOfAnInteger(r,[2]);
					s2:= PiPartOfAnInteger(s,[2]);
					o2:= PiPartOfAnInteger(o,[2]);

# For epsilon=1, we have to check condition (B) for the 2-part.
					if conditionOk and n mod s2 = 0 and (s mod r2 = 0 or GcdInt(s2*o2,n)<>s2*o2) then
						Add(listIn, [m,n,s,o,1,r]);
					fi;
					m2:= PiPartOfAnInteger(m,[2]);
					n2:= PiPartOfAnInteger(n,[2]);

# For epsilon=-1 we have to check condition (C).
					if conditionOk and n mod 2 = 0 and m mod 4 = 0 and (2*s) mod m2 = 0 and s2 <> n2*r2 and (n mod 4 <> 0 or m mod 8 <> 0 or o2 = n2 or s mod r2 = 0) then
						Add(listIn, [m,n,s,o,-1,r]);
					fi;
				od;
			od;
		od;
	od;

	return listIn;
end;

#########################################################################################################
# This function computes a cyclic normal subgroup of G with G/A cyclic of minimal order, if G is metacyclic. 
# Otherwise it fails.
MinimalKernel := function(G)

local D,d,can,A;

  if not(IsGroup(G)) or not IsFinite(G) then 
  	Print("Error: The input is not a finite group in MinimalKernel\n");
    return fail;
  fi;
  D := DerivedSubgroup(G);
  if not IsCyclic(D) then 
  	Print("Error: The input is not a metacyclic group in MinimalKernel\n");
    return fail;
  fi;

  if Size(D)=1 then 
    d := One(G);
  else
    d := MinimalGeneratingSet(D)[1];
  fi;

  can := Filtered(List(RationalClasses(G),x->Group(Representative(x))), y -> d in y);

  SortBy(can,Order);

  for A in can do
    if IsCyclic(G/A) then
      return A;
    fi;
  od;

  Print("Error: The input is not a metacyclic group in MinimalKernel\n");
  return fail;

end;

###############################################################################################################################
 
AreMCParameters := function(x)

	local m,n,r,s;

	if not( IsList(x) and Length(x) = 4 and ForAll(x,i -> i in Integers) and x[1]>0 and x[2]>0) then
	  Print("Error: The input must be a list of integers of length 4 in AreMCParameters\n");
	  return fail;
	fi;

	m := x[1];
	n := x[2];
	s := x[3];
	r := x[4];

	if not (s*(r-1) mod m) = 0 or not ((r^n-1) mod m) = 0 then
	  return false;
	fi;

	return true;

end;

##############################################################################################################################
# Function to generate a metacyclic group with m, n, s and r. The group is generated with a power-conjugate presentation,
# which means that operating with the group is fast and efficient.
MetacyclicGroupPC:= function(x)

	local m,n,s,r,F, col, G;
	
	G:=AreMCParameters(x); 
	if G <> true then
		Print("Error: The argument must be a list of metacyclic parameters in MetacyclicGroupPC\n");
		return fail;
	fi;

	m := x[1];
	n := x[2];
	s := x[3];
	r := x[4];
	
	if Minimum(m,n)=1 then 
		n := Maximum(n,m);
		return CyclicGroup(n);
	else
		SetInfoLevel(InfoWarning,0); 
		F:= FreeGroup(2);
		col:= SingleCollector(F, [n,m]);
		SetConjugate(col, 2, 1, F.2^r);
		SetPower(col, 1, F.2^s);
		G:=GroupByRws(col);
		SetInfoLevel(InfoWarning,1);
		return RefinedPcGroup(G);
	fi;
end;



#########################################################################################################
# This function computes a tuple [a,b,m,n,s,r,eps,o,t,m'] where G=<a><b> is a minimal factorization of the 
# input group, which must be a finite metacyclic group, INV(G)=(m,n,s,Delta), (r,eps,o)=[Delta] and 
# Delta=<t>_m'.

MinMetaFact := function(input)

	local G, A, a, pr, GA, bb, b, m, n, s, bn, y, as, ay, r, eps, p, pim, r2, pir, pip, pi, Apip, o, mp, np, sp, rp, op, ap, bp, apbp, t, apt, x, s2, n2, m2, m2p, s2p, ab, at, mprime;

	if IsGroup(input) and IsFinite(input) then
		G:=input;
	else 
		G:=AreMCParameters(input); 
		if G = true then
			G:=MetacyclicGroupPC(input);
		else
			Print("Error: The input must be a finite group or a list of parameters defining one in MinMetaFact\n");
			return fail;
		fi;	
	fi;


	A:=MinimalKernel(G);

	if A=fail then
		return fail;
	fi;

	if Size(A)=1 then 
		a:=One(G);
	else
		a := MinimalGeneratingSet(A)[1];
	fi;


  ############# Step 1-2 ############

	pr := NaturalHomomorphismByNormalSubgroup(G,A);
	GA := Image(pr);
	if Size(GA)=1 then 
		bb:=One(GA);
	else
		bb := MinimalGeneratingSet(GA)[1];
	fi;
	b := Representative(PreImages(pr,bb));
	m := Order(a);
	n := Order(G)/m;
	s := m*n/Order(b);
	bn := b^n;
	y := s;
	as := a^s;
	ay := as;
	while bn <> ay do
		ay:=ay*as;
		y:=y+s;
	od;

  ############# Step 3 ############

	pim := PrimeDivisors(m);
	r := 1;
	eps := 1;

	for p in pim do
		while IsInt(m/(p*r)) and (a^(m/(p*r)))^b = a^(m/(p*r)) do
		r:=p*r;
		od;
	od;

	if IsInt(m/4) and not IsInt(r/4) then
		eps := -1;
		r2 := 2;
		while IsInt(m/(2*r2)) and (a^(m/(2*r2)))^b = a^(-m/(2*r2)) do
			r2:=2*r2;
			r:=2*r;
		od;
	fi;

  ############# Step 4 ############

	pir := PrimeDivisors(r);
	pip := Difference(pim,pir);
	pi := Difference(PrimeDivisors(m*n),pip);
	Apip := HallSubgroup(A,pip);
	o := PiPartOfAnInteger(Order(ConjugatorAutomorphism(Apip,b)),pi);

	for p in pir do 
		mp := PiPartOfAnInteger(m,[p]);
		np := PiPartOfAnInteger(n,[p]);
		sp := PiPartOfAnInteger(s,[p]);    
		rp := PiPartOfAnInteger(r,[p]);
		op := PiPartOfAnInteger(o,[p]);
  ############# Step 4a ############
		if eps=1 or p>2 then 
			if sp>np then 
				b := b*PiPart(a,[p]);
				s := s*np/sp;
				sp := np;
			fi;
  ############# Step 4b ############    
			if rp>sp and sp*op <= np then 
				ap := PiPart(a,[p]);
				bp := PiPart(b,[p]);
				apbp := ap^bp;           
				t := 1;
				apt:=ap;
				while apbp<>apt do
					t:=t+1;
					apt:=ap*apt;
				od;
				x := Int(Inverse(ZmodnZObj(Ese(t^(n/sp),sp)/sp,mp/sp))*ZmodnZObj((r-y)/sp,mp/sp));
				a := bp^(n/sp)*a*ap^(x-1);
				m := sp*m/rp;
				n := n*rp/sp;
				if IsInt(m/8) and sp=2 and 2*r2=m2 then
					r:=4*r/r2;
					eps := -1;
				else;
					r:=r*sp/rp;
				fi;
			fi;
		fi;
	od;

  ############# Steps 5 and 6 ############    

	if eps = -1 then
		r2 := PiPartOfAnInteger(r,[2]);
		s2 := PiPartOfAnInteger(s,[2]);
		n2 := PiPartOfAnInteger(n,[2]);
		if IsInt(m/8) and n2>2 and r2 > s2 then 
			if n2 > PiPartOfAnInteger(o,[2]) then
				m2p := m/PiPartOfAnInteger(m,[2]);
				s2p := s/s2;
				a := b^(m2p*n/2*s2p)*a;
				r := r/2;
				r2:=r2/2;
			fi;
		fi;
		if s2=r2*n2 then
			b:=b*PiPart(a,[2]);
			s:=s/2;
		fi;
	fi;

	ab := a^b;           
	t := 1;
	at:=a;
	while ab<>at do
		t:=t+1;
		at:=a*at;
	od;

	mprime := PiPartOfAnInteger(m,pip);
	pir := PrimeDivisors(r);

	for p in pir do
		op := PiPartOfAnInteger(o,[p]);
		rp := PiPartOfAnInteger(r,[p]);
		sp := PiPartOfAnInteger(s,[p]);
		mp := PiPartOfAnInteger(m,[p]);
		np := PiPartOfAnInteger(n,[p]);
		if p=2 and eps = -1 then
			if op <= 2 or mp<=2*rp then
				mprime := mprime * rp;
			elif op <= np and 2*sp=mp and mp < np*rp then
				mprime := mprime * mp/2;
			else
				mprime := mprime * mp;
			fi;
		else
			mprime := mprime * Minimum(mp,op*rp,Maximum(sp,rp*sp*op/np));
		fi;
	od;

	t := t mod mprime;


	return [a,b,m,n,s,r,eps,o,t,mprime];

end;



############################################################################################################################
# 
#    DOCUMENTED AUXILIAR FUNCTIONS (without MinimalKernel and MetacyclicGroupPC and AreMCParameters)
#
############################################################################################################################

# Function to check whether a group is Metacyclic.
IsMetacyclic := function(G)

	local D,N, pabinv, mrepprimes;

	if not (IsGroup(G) and IsFinite(G)) then
		Print("Error: The input must be a finite group in IsMetacyclic\n");
		return fail;
	fi;

	if IsCyclic(G) then
		return true;
	fi;

	D := DerivedSubgroup(G);
	if not IsCyclic(D) then
		return false;
	fi;

	pabinv := List(AbelianInvariants(G),x->PrimeDivisors(x)[1]);
	mrepprimes := Maximum(List(SSortedList(pabinv),p->Size(Filtered(pabinv,x->x=p))));

	if mrepprimes >2 then 
		return false;
	fi;
	
	N := NormalSubgroups(G);
	if Filtered(N,x-> IsCyclic(x) and IsSubset(x,D) and IsCyclic(G/x)) = [] then
		return false;
	else
		return true;
	fi;

end;



############################################################################################################################
# This function computes seminvariants for a metacyclic group.

MCParameters := function(G)

	local A, a, pr, GA, bb, b, m, n, bn, x, ax, s, as, ab, t, at;

	if not (IsGroup(G) and IsFinite(G)) then
		Print("Error: The input must be a group in MCParameters\n");
		return fail;
	fi;

	A:=MinimalKernel(G);

	if A=fail then
		return fail;
	fi;

	if Size(A)=1 then 
		a:=One(G);
	else
		a := MinimalGeneratingSet(A)[1];
	fi;
	pr := NaturalHomomorphismByNormalSubgroup(G,A);
	GA := Image(pr);
	if Size(GA)=1 then 
		bb:=One(GA);
	else
		bb := MinimalGeneratingSet(GA)[1];
	fi;
	b := Representative(PreImages(pr,bb));
	m := Order(a);
	n := Order(G)/m;
	
	bn := b^n;
	x := m/Order(bn);
	ax := a^x;
	s := x;
	as := ax;
	while as <> bn do
		as := as*ax;
		s := s+x;
	od;
	
	ab := a^b;
	t := 1;
	at := a;
	while at <> ab do
		at := a*at;
		t := t+1;
	od;

	return [m,n,s,t];

end;



############################################################################################################################
#
#  MAIN FUNCTIONS
#
############################################################################################################################

# In this function we apply Algorithm 4 to a certain size N. We compute the list P of the algorithm (which is the parameters called ListIn in Lemma 5.1) for this size and then for each list of parameters we compute t, m' and s' and use them to get every possible metacyclic group of size N.

MetacyclicGroupsByOrder := function(N)

	local listIn, listParams, listM, alpha, m, n, s, piprime, pi, o, e, r, t, p, rp, sp, op, mp, np, sprime, mprime, mpi, rdelta, pidelta, piprimedelta, matches, ms, rs, epsilondelta, odelta, deltapi,  Aut, AutCyclic, i, delta, beta, orderDelta, m2, mprimepi, rg, r1;

	if N=1 then 
		return [[1,1,1,0]];
	fi;

	if not (N in Integers and N>1) then
		Print("The input must be a positive integer \n");
		return fail;
	fi;

# The following line is to avoid having the output line filled by warnings triggered by the Group function when applied to elements of ZmodnZ. 
	SetInfoLevel(InfoWarning,0);

# listIn is the set of parameters defined in Lemma 5.1, we compute it in a different function. 
# In listParams we will save the (m',n,s') from Algorithm 4 without repetitions and
# in listM we will save the parameters m, s, n, t for which G=G_{m,n,s,t}.
	listIn:= ListIn(N);
	listParams:=Set([]);
	listM:=[];
# For each set in listIn, we compute t, m' and s'.
	for i in [1..Size(listIn)] do
		m:= listIn[i][1];
		n:= listIn[i][2];
		s:= listIn[i][3];
		o:= listIn[i][4];
		e:= listIn[i][5];
		r:= listIn[i][6];

		piprime:= Difference(PrimeDivisors(m), PrimeDivisors(r));

		pi:= Filtered(PrimeDivisors(N), p-> not p in piprime);
		t:=1;
		mpi:=PiPartOfAnInteger(m,pi);
		ms:=[];
		rs:=[];
		for p in pi do
			rp:= PiPartOfAnInteger(r,[p]);
			sp:= PiPartOfAnInteger(s,[p]);
			op:= PiPartOfAnInteger(o,[p]);
			mp:= PiPartOfAnInteger(m,[p]);
			np:= PiPartOfAnInteger(n,[p]);
			Add(ms,mp);
			Add(rs, e^(p-1)+rp);

			if p<>2 or (p=2 and e=1) then
				t:=t * Minimum(op, mp/rp, Maximum(1,sp/rp, (sp*op)/np));
			else
				if GcdInt(op,2)=op or GcdInt(mp, 2*rp)=mp then
					t:=t;
				elif GcdInt(4,op)=4 and op<np and GcdInt(4*rp, mp)= 4*rp and 2*sp=mp and mp< np*rp then
					t:=t*mp/(2*rp);
				else
					t:=t*mp/rp;
				fi;
			fi;
		od;

		mprime:= PiPartOfAnInteger(m,piprime)*t*r;
		sprime:= s*t*r/mpi;

# We save m' and s' in the same list with the rest of parameters. We also save the ms and rs because we will need them later to compute t.
		listIn[i][7]:= mprime;
		listIn[i][8]:= sprime;
		listIn[i][9]:= ms;
		listIn[i][10]:= rs;

# We save the m', s', n paramenters in a list without repetitions so as not to have to compute the deltas twice.
		AddSet(listParams, [mprime, n, sprime]);
	od;

# Now we go over each (m',n,s'), we compute the deltas and we check if their parameters match any element in listIn.
	for beta in listParams do
		mprime:=beta[1];
		n:=beta[2];
		sprime:=beta[3];

# We take delta in U_^(n,s')_m' and then we take a representative of the cyclic subgroups.
		AutCyclic:= List(RationalClasses(Units(ZmodnZ(mprime))), x->Representative(x));
		Aut:= Filtered(AutCyclic, x->x*sprime = sprime*ZmodnZObj(1,mprime) and n/Order(x) in Integers);
# For each delta we compute the parameters associated to it: pi and pi', o, epsilon and r and we take the elements in listIn with matching parameters.
		for delta in Aut do
			piprimedelta:= Filtered(PrimeDivisors(mprime), p-> Int(delta) mod p <> 1);
			pidelta:= Filtered(PrimeDivisors(mprime*n), x-> not x in piprimedelta); 
			deltapi:= delta^PiPartOfAnInteger(Order(delta), piprimedelta);
			odelta:= Order(ZmodnZObj(Int(deltapi), PiPartOfAnInteger(mprime, piprimedelta)));
			epsilondelta := 1;
			if mprime mod 4 = 0 and Int(deltapi) mod 4 = -1 mod 4 then
				epsilondelta := -1;
			fi;
			orderDelta:=Order(ZmodnZObj(Int(deltapi), PiPartOfAnInteger(mprime, pidelta)));
			m2:=PiPartOfAnInteger(mprime, [2]);
			if mprime mod 4 = 0 and Int(deltapi) mod m2 = -1 mod m2 then 
				rdelta:= 2*PiPartOfAnInteger(mprime, pidelta)/orderDelta;
			else
				rdelta:= PiPartOfAnInteger(mprime, pidelta)/orderDelta;
			fi; 
			matches:= Filtered(listIn, x->x[7] = mprime and x[8]=sprime and x[2]=n and x[4]=odelta and x[5]=epsilondelta and x[6] = rdelta);
# For each match we look for the parameter t that gives the group as an invariant.
			for alpha in matches do
				m:=alpha[1];
				s:=alpha[3];
				r1:=ChineseRem(alpha[9],alpha[10]);
				mprimepi:=PiPartOfAnInteger(mprime,pidelta);
				rg := Filtered(List(RationalClass(Units(ZmodnZ(mprime)),ZmodnZObj(Int(delta),mprime)), Int), x->(x mod mprimepi)=(r1 mod mprimepi));
				t:= Minimum(List(rg, x-> ChineseRem([PiPartOfAnInteger(m,pidelta), PiPartOfAnInteger(m,piprimedelta)], [r1,x])));
				Add(listM, [alpha[1], alpha[2], alpha[3], t]);
			od;
		od;
	od;

	Sort(listM);
	
	SetInfoLevel(InfoWarning,1);
	return listM;
end;

#################################################
# If the input is a finite metacyclic group G this function outputs MCINV(G)

MCINV := function(G)

	local MMF,D;

	MMF := MinMetaFact(G);

	if MMF=fail then
		return fail;
	fi;

	SetInfoLevel(InfoWarning,0);
	D:=Group(ZmodnZObj(MMF[9],MMF[10]));
	SetInfoLevel(InfoWarning,1);
	return [MMF[3],MMF[4],MMF[5],D];

end;


#################################################
# If the input is a finite metacyclic group G this function computes a tuple [m,n,s,[t,k]] 
# such that MCINV(G) = [m,n,s,Delta] where Delta is the group of units modulo k generated by t

MCINVData := function(G)

	local MMF;

	MMF := MinMetaFact(G);

	if MMF=fail then
		return fail;
	fi;

	return [MMF[3],MMF[4],MMF[5],MMF[10],MMF[9]];

end;


#################################################
# This function computes the metacyclic invariants of a metacyclic group

MetacyclicInvariants := function(G)

	local MMF,m,n,s,r,eps,tprime,mprime,delta,pim,pir,pip,mpip,mpir,m2,r2,t,mp,rp,p;

	MMF := MinMetaFact(G);
	
	SetInfoLevel(InfoWarning,0);

	if MMF=fail then
		return fail;
	fi;


	m := MMF[3];
	n := MMF[4];
	s := MMF[5];
	r := MMF[6];
	eps := MMF[7];
	tprime := MMF[9];
	mprime := MMF[10];

	delta := Group(ZmodnZObj(tprime,mprime));

	pim := PrimeDivisors(m);
	pir := PrimeDivisors(r);
	pip := Difference(pim,pir);
	mpip := PiPartOfAnInteger(m,pip);
	mpir := PiPartOfAnInteger(m,pir);
	mp:=[];
	rp:=[];
	if pir<>[] then
		for p in pir do
			Add(mp, PiPartOfAnInteger(m,[p]));
			if p=2 then 
				Add(rp, eps + PiPartOfAnInteger(r,[p]));
			else 
				Add(rp, 1 + PiPartOfAnInteger(r,[p]));
			fi;
		od;
		t := ChineseRem(mp,rp);
	else
		t := 0;
	fi;
	while Gcd(t,mpip) <> 1 or Group(ZmodnZObj(t,mprime)) <> delta do
		t := t+mpir;
	od;

	SetInfoLevel(InfoWarning,1);

	return [m,n,s,t];

end;


##############################################################################################################################
# Function that takes two groups (as groups or as parameters defining them) and returns whether they are isomorphic or not.

AreIsomorphicMetacyclicGroups := function(G,H)

	local iG,iH;
	
	iG := MCINV(G);
	iH := MCINV(H);
	
	if iG=fail or iH=fail then
		Print("Error: Each argument of the input must be either a finite group or a list of parameters defining one in AreIsomorphicMetacyclicGroups \n");
		return fail;
	fi;

	return iG=iH;

end;

##############################################################################################################################
# ALTERNATIVE FUNCIONS 
##############################################################################################################################

##############################################################################################################################
# This function construct the group given by the following presentation 
# G=<a,b|a^m,b^n=a^s,a^b=a^t> as FreeGroup(a,b)/[a^m,b^n*a^-s,a^b*a^-t]
# The output is the [G,a,b,m,n,s,t]

GMCP := function(x)

local f,G,a,b,m,n,s,t;

m := x[1];
n := x[2];
s := x[3];
t := x[4];
f := FreeGroup("a","b");
a := f.1;
b := f.2;
G := f/[a^m,b^n*a^-s,a^b*a^-t];
a := G.1;
b := G.2;
m := Order(a);
s := s mod m;
if s=0 then 
	s := m;
fi;

return [G,a,b,m,Order(G)/m,s,t mod m];

end;
