method test (a:array<int>,n:int) 
    requires a.Length > 0
    requires 0<n<a.Length
    requires forall i:int :: 0<=i<a.Length ==> a[i] >= 0
    requires forall i:int :: 0<=i< n==>a[i]>0
    ensures forall i:int :: 0<=i<a.Length ==> a[i] > 0 
    modifies a
{
    var i:=n;
    while( i<a.Length)
    invariant forall i:int :: 0<=i<a.Length ==> a[i] > 0 
    {
        if(a[i]==0){
            a[i]:=1;
        }
        i:=i+1;
    }
}