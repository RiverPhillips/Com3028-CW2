method CheckArr0(A: array<int>) returns (r: bool) 
requires A.Length > 0
ensures (A.Length == 1 ==> true) || (forall j :: 0 < j < A.Length ==> (A[j] != A[0])){
    r := true;
   if(A.Length > 1 && r) {
    var i:= 1;
    while i < A.Length
    decreases A.Length - i
    invariant 0 < i <= A.Length{
        if (A[i] == A[0]) {
            r := false;
        }
        i := i+1;
    }
   }
    return r;
}