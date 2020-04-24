method CheckArr0(A: array<int>) returns (unique: bool) 
requires A.Length > 0
ensures unique <==> forall i :: 0 < i < A.Length ==> A[i] != A[0]
{
    unique := true;

    if A.Length > 1 {
      var i:= 1;

      while i < A.Length && unique
      decreases A.Length - i
      invariant i <= A.Length
      invariant unique <==> (forall j :: (0 < j < i) ==> A[j] != A[0]) 
      {
        assert A.Length > 1;
        if (A[i] == A[0]) {
            unique := false;
        }

        i := i+1;
      }
    }
   
    return unique;
}

method CheckArr1(A: array<int>) returns (unique: bool)
requires A.Length > 0 
ensures unique <==> forall i, j :: 0 <= i < A.Length && 0 <= j < A.Length && i != j ==> A[i] != A[j] {
    unique := true;

    if (A.Length > 1){
        var i := 0;

        while i < A.Length && unique
        decreases A.Length - i
        invariant 0 <= i <= A.Length
        invariant unique <==> forall x, y :: 0 <= x < i && x < y < A.Length ==> A[x] != A[y]
        {
            var j := i+1;
         
            while j < A.Length && unique
            decreases  A.Length - j
            invariant i < j <= A.Length
            invariant unique <==> forall x :: i < x < j ==> A[x] != A[i] 
            {
                if (A[i] == A[j]) {
                    unique := false;                    
                }
                j := j+1;
            }
            i := i+1;
        }
    }

    return unique;
}

//Check there are no duplicates in the first column (index 0)
method CheckM0(M: array2<int>) returns (unique: bool) 
requires 0 < M.Length1 && 0 < M.Length0
ensures unique <==> forall i,j :: 0 <= i < M.Length0 && 0 <= j < M.Length0 && i != j ==> M[i,0] != M[j,0]
{
  unique := true;

  
    if (M.Length0 > 1){
        var i := 0;

        while i < M.Length0 && unique
        decreases M.Length0 - i
        invariant 0 <= i <= M.Length0
        invariant unique <==> forall x, y :: 0 <= x < i && x < y < M.Length0 ==> M[x, 0] != M[y, 0]
        {
            var j := i+1;
         
            while j < M.Length0 && unique
            decreases  M.Length0 - j
            invariant i < j <= M.Length0
            invariant unique <==> forall x :: i < x < j ==> M[x,0] != M[i, 0] 
            {
                if (M[i,0] == M[j,0]) {
                    unique := false;                    
                }
                j := j+1;
            }
            i := i+1;
        }
    }



  return unique;
}