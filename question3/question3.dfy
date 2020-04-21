method CheckArr0(A: array<int>) returns (noDuplicates: bool) 
requires A.Length > 0
ensures (A.Length == 1 ==> true) || (forall j :: 0 < j < A.Length ==> (A[j] != A[0]))
{
    noDuplicates := true;
    if(A.Length > 1) {
        var i:= 1;
        while i < A.Length
        decreases A.Length - i
        invariant 0 < i <= A.Length{
        if (A[i] == A[0]) {
            noDuplicates := false;
        }
        i := i+1;
        }
   }
    return noDuplicates;
}

method CheckArr1(A: array<int>) returns (noDuplicates: bool)
requires A.Length > 0 
ensures (A.Length == 1 ==> true) ||  (forall i, j :: 0 <= i < A.Length && 0 <=j < A.Length ==> j != i ==> (A[i] != A[j])){
    noDuplicates := true;

    if (A.Length > 1){
        var i := 0;
        while(i < A.Length && noDuplicates)
        decreases A.Length - i
        invariant 0 <= i <= A.Length
        {

            var j := i+1;
            while(j < A.Length && noDuplicates)
            decreases  A.Length - j
            invariant i < j <= A.Length
            {
                if (A[i] == A[j]) {
                    noDuplicates := false;                    
                }
                j := j+1;
            }
            i := i+1;
        }
    }

    return noDuplicates;
}