datatype state = I| T| C| E
type client=nat
type boolean=bool

method n_Tryinv__1_0(n:array<state>,    
N0:nat,i:nat,
p_Inv0:nat,p_Inv1:nat,x:array<boolean>)
requires N0>0
requires n.Length==N0
requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]
requires 0<=i<N0
requires p_Inv0!=p_Inv1 && p_Inv0<N0 && p_Inv1<N0
requires i==p_Inv0
//1
requires (n[i] == I) //guard condition
ensures (!((n[p_Inv0]==I) && (n[p_Inv1]==T) && (x[0]==false)))
modifies n

{
  n[i] := T;
}

method n_Tryinv__1_1(n:array<state>,    
N0:nat,i:nat,
p_Inv0:nat,p_Inv1:nat,x:array<boolean>)
requires N0>0
requires n.Length==N0
requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]
requires 0<=i<N0
requires p_Inv0!=p_Inv1 && p_Inv0<N0 && p_Inv1<N0
requires i==p_Inv1
//1
requires (n[i] == I) //guard condition
ensures (!((n[p_Inv0]==I) && (n[p_Inv1]==T) && (x[0]==false)))

modifies n

{
  n[i] := T;
}


method n_Tryinv__1_2(n:array<state>,    
N0:nat,i:nat,
p_Inv0:nat,p_Inv1:nat,x:array<boolean>)
requires N0>0

requires n.Length==N0




requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]




requires 0<=i<N0
requires p_Inv0!=p_Inv1&&p_Inv0<N0&& p_Inv1<N0
requires i!=p_Inv0&&i!=p_Inv1
requires (!((n[p_Inv0] == C) && (n[p_Inv1] == C)))//2
requires (n[i] == I) //guard condition
ensures (!((n[p_Inv0]==I) && (n[p_Inv1]==T) && (x[0]==false)))
modifies n

{
  n[i] := T;
}


method n_Critinv__1_0(n:array<state>,    
N0:nat,i:nat,
p_Inv0:nat,p_Inv1:nat,x:array<boolean>)
requires N0>0

requires n.Length==N0




requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]




requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires p_Inv0!=p_Inv1&&p_Inv0<N0&& p_Inv1<N0
requires i==p_Inv1
requires (!((n[p_Inv0] == C) && (x[0] == true)))//3
requires ((n[i] == T) && (x[0] == true)) //guard condition
ensures (!((n[p_Inv0]==I) && (n[p_Inv1]==T) && (x[0]==false)))
modifies n
modifies x

{
  n[i] := C;
  x[0] := false;
}

method n_Critinv__1_1(n:array<state>,    
N0:nat,i:nat,
p_Inv0:nat,p_Inv1:nat,x:array<boolean>)
requires N0>0

requires n.Length==N0




requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]




requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires p_Inv0!=p_Inv1&&p_Inv0<N0&& p_Inv1<N0
requires i==p_Inv0
requires (!((n[p_Inv1] == C) && (x[0] == true)))//3
requires ((n[i] == T) && (x[0] == true)) //guard condition
ensures (!((n[p_Inv0]==I) && (n[p_Inv1]==T) && (x[0]==false)))
modifies n
modifies x

{
  n[i] := C;
  x[0] := false;
}

method n_Critinv__1_2(n:array<state>,    
N0:nat,i:nat,
p_Inv0:nat,p_Inv1:nat,x:array<boolean>)
requires N0>0

requires n.Length==N0




requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]




requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires p_Inv0!=p_Inv1&&p_Inv0<N0&& p_Inv1<N0
requires i!=p_Inv0&&i!=p_Inv1
requires (!((n[p_Inv1] == C) && (n[p_Inv0] == C)))//2
requires ((n[i] == T) && (x[0] == true)) //guard condition
ensures (!((n[p_Inv0]==I) && (n[p_Inv1]==T) && (x[0]==false)))
modifies n
modifies x

{
  n[i] := C;
  x[0] := false;
}


method n_Exitinv__1_0(n:array<state>,    
N0:nat,i:nat,
p_Inv0:nat,p_Inv1:nat,x:array<boolean>)
requires N0>0

requires n.Length==N0




requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]




requires 0<=i<N0
requires p_Inv0!=p_Inv1&&p_Inv0<N0&& p_Inv1<N0
requires i==p_Inv1
//1
requires (n[i] == C) //guard condition
ensures (!((n[p_Inv0]==I) && (n[p_Inv1]==T) && (x[0]==false)))
modifies n

{
  n[i] := E;
}

method n_Exitinv__1_1(n:array<state>,    
N0:nat,i:nat,
p_Inv0:nat,p_Inv1:nat,x:array<boolean>)
requires N0>0

requires n.Length==N0




requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]




requires 0<=i<N0
requires p_Inv0!=p_Inv1&&p_Inv0<N0&& p_Inv1<N0
requires i==p_Inv0
//1
requires (n[i] == C) //guard condition
ensures (!((n[p_Inv0]==I) && (n[p_Inv1]==T) && (x[0]==false)))
modifies n

{
  n[i] := E;
}

method n_Exitinv__1_2(n:array<state>,    
N0:nat,i:nat,
p_Inv0:nat,p_Inv1:nat,x:array<boolean>)
requires N0>0

requires n.Length==N0




requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]




requires 0<=i<N0
requires p_Inv0!=p_Inv1&&p_Inv0<N0&& p_Inv1<N0
requires i!=p_Inv0&&i!=p_Inv1
requires (!((n[p_Inv1] == C) && (n[p_Inv0] == C)))//2
requires (n[i] == C) //guard condition
ensures (!((n[p_Inv0]==I) && (n[p_Inv1]==T) && (x[0]==false)))
modifies n

{
  n[i] := E;
}


method n_Idleinv__1_0(n:array<state>,    
N0:nat,i:nat,
p_Inv0:nat,p_Inv1:nat,x:array<boolean>)
requires N0>0

requires n.Length==N0




requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]




requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires p_Inv0!=p_Inv1&&p_Inv0<N0&& p_Inv1<N0
requires i==p_Inv1
//1
requires (n[i] == E) //guard condition
ensures (!((n[p_Inv0]==I) && (n[p_Inv1]==T) && (x[0]==false)))
modifies n
modifies x

{
  n[i] := I;
  x[0] := true;
}

method n_Idleinv__1_1(n:array<state>,    
N0:nat,i:nat,
p_Inv0:nat,p_Inv1:nat,x:array<boolean>)
requires N0>0

requires n.Length==N0




requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]




requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires p_Inv0!=p_Inv1&&p_Inv0<N0&& p_Inv1<N0
requires i==p_Inv0
//1
requires (n[i] == E) //guard condition
ensures (!((n[p_Inv0]==I) && (n[p_Inv1]==T) && (x[0]==false)))
modifies n
modifies x

{
  n[i] := I;
  x[0] := true;
}

method n_Idleinv__1_2(n:array<state>,    
N0:nat,i:nat,
p_Inv0:nat,p_Inv1:nat,x:array<boolean>)
requires N0>0

requires n.Length==N0




requires x.Length==N0

requires forall i,j::0<=i<n.Length&&0<=j<n.Length==>n[i]!=n[j]




requires forall i,j::0<=i<x.Length&&0<=j<x.Length==>x[i]!=x[j]

requires 0<=i<N0
requires p_Inv0!=p_Inv1&&p_Inv0<N0&& p_Inv1<N0
requires i!=p_Inv0&&i!=p_Inv1
requires (!((n[p_Inv1] == C) && (n[p_Inv0] == C)))//2
requires (n[i] == E) //guard condition
ensures (!((n[p_Inv0]==I) && (n[p_Inv1]==T) && (x[0]==false)))
modifies n
modifies x

{
  n[i] := I;
  x[0] := true;
}


