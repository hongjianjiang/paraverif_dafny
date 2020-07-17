datatype state = I| T| C| E
type client=nat
type boolean=bool




method n_Tryinv__2_0(n:array<state>,    x:array<boolean>, 
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires n.Length==N0



requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]



requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires  p__Inv4<N0
requires i==p__Inv4
//1
requires (n[i] == I) //guard condition
ensures   (!((n[p__Inv4] == C) && (x[0] == true)))
modifies n

{
  n[i] := T;
}

method n_Tryinv__2_1(n:array<state>,    x:array<boolean>, 
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires n.Length==N0



requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]



requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((n[p__Inv4] == C) && (x[0] == true)))//2
requires (n[i] == I) //guard condition
ensures   (!((n[p__Inv4] == C) && (x[0] == true)))
modifies n

{
  n[i] := T;
}


method n_Critinv__2_0(n:array<state>,    x:array<boolean>, 
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires n.Length==N0



requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]



requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires  p__Inv4<N0
requires i==p__Inv4
//1
requires ((n[i] == T) && (x[0] == true)) //guard condition
ensures   (!((n[p__Inv4] == C) && (x[0] == true)))
modifies n
modifies x

{
  n[i] := C;
  x[0] := false;
}

method n_Critinv__2_1(n:array<state>,    x:array<boolean>, 
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires n.Length==N0



requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]



requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
//1
requires ((n[i] == T) && (x[0] == true)) //guard condition
ensures   (!((n[p__Inv4] == C) && (x[0] == true)))
modifies n
modifies x

{
  n[i] := C;
  x[0] := false;
}


method n_Exitinv__2_0(n:array<state>,    x:array<boolean>, 
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires n.Length==N0



requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]



requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires  p__Inv4<N0
requires i==p__Inv4
//1
requires (n[i] == C) //guard condition
ensures   (!((n[p__Inv4] == C) && (x[0] == true)))
modifies n

{
  n[i] := E;
}

method n_Exitinv__2_1(n:array<state>,    x:array<boolean>, 
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires n.Length==N0



requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]



requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((n[p__Inv4] == C) && (x[0] == true)))//2
requires (n[i] == C) //guard condition
ensures   (!((n[p__Inv4] == C) && (x[0] == true)))
modifies n

{
  n[i] := E;
}


method n_Idleinv__2_0(n:array<state>,    x:array<boolean>, 
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires n.Length==N0



requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]



requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires  p__Inv4<N0
requires i==p__Inv4
//1
requires (n[i] == E) //guard condition
ensures   (!((n[p__Inv4] == C) && (x[0] == true)))
modifies n
modifies x

{
  n[i] := I;
  x[0] := true;
}

method n_Idleinv__2_1(n:array<state>,    x:array<boolean>, 
N0:nat,i:nat,
p__Inv4:nat)
requires N0>0

requires n.Length==N0



requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]



requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires  p__Inv4<N0
requires i!=p__Inv4
requires (!((n[p__Inv4] == C) && (n[i] == E)))//3
requires (n[i] == E) //guard condition
ensures   (!((n[p__Inv4] == C) && (x[0] == true)))
modifies n
modifies x

{
  n[i] := I;
  x[0] := true;
}


