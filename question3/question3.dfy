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

method CheckCols(M: array2<int>) returns (unique: bool)
ensures unique <==> forall i,j,k :: 0 <= i < M.Length0 && 0 <= j < M.Length0 && 0 <= k < M.Length1 &&  j != i  ==> M[i,k] != M[j,k]
{
  unique := true;

    var k := 0;

    while k < M.Length1 && unique 
    decreases  M.Length1 - k
    invariant 0 <= k <= M.Length1
    invariant unique <==> forall x, y, z :: 0 <= x <= M.Length0 && x < y < M.Length0 && 0 <= z < k ==> M[x, z] != M[y, z]
    {
      if (M.Length0 > 1){
          var i := 0;

          while i < M.Length0 && unique
          decreases M.Length0 - i
          invariant 0 <= i <= M.Length0
          invariant unique <==> forall x, y :: 0 <= x < i && x < y < M.Length0 ==> M[x, k] != M[y, k]
          {
              var j := i+1;
          
              while j < M.Length0 && unique
              decreases  M.Length0 - j
              invariant i < j <= M.Length0
              invariant unique <==> forall x :: i < x < j ==> M[x,k] != M[i, k] 
              {
                  if (M[i,k] == M[j,k]) {
                      unique := false;                    
                  }

                  assert unique ==> M[i,k] != M[j,k];
                  assert !unique ==> M[i,k] == M[j, k];

                  j := j+1;
              }
              i := i+1;
          }
      }
      k := k+1;
  }

  return unique;
}


method CheckRows(M: array2<int>) returns (unique: bool)
ensures unique <==> forall i,j,k :: 0 <= i < M.Length1 && 0 <= j < M.Length1 && 0 <= k < M.Length0 &&  j != i  ==> M[k,i] != M[k,j]
{
  unique := true;

    var k := 0;

    while k < M.Length0 && unique 
    decreases  M.Length0 - k
    invariant 0 <= k <= M.Length0
    invariant unique <==> forall x, y, z :: 0 <= x <= M.Length1 && x < y < M.Length1 && 0 <= z < k ==> M[z, x] != M[z, y]
    {
      if (M.Length1 > 1){
          var i := 0;

          while i < M.Length1 && unique
          decreases M.Length1 - i
          invariant 0 <= i <= M.Length1
          invariant unique <==> forall x, y :: 0 <= x < i && x < y < M.Length1 ==> M[k, x] != M[k, y]
          {
              var j := i+1;
          
              while j < M.Length1 && unique
              decreases  M.Length1 - j
              invariant i < j <= M.Length1
              invariant unique <==> forall x :: i < x < j ==> M[k, x] != M[k, i] 
              {
                  if (M[k, i] == M[k, j]) {
                      unique := false;                    
                  }
                  j := j+1;
              }
              i := i+1;

          }
      }
      k := k+1;
  }

  return unique;
}

method CheckMatrix(M: array2<int>) returns (unique: bool)
ensures unique ==> (forall i,j,k :: 0 <= i < M.Length1 && 0 <= j < M.Length1 && 0 <= k < M.Length0 &&  j != i  ==> M[k,i] != M[k,j]) && (forall i,j,k :: 0 <= i < M.Length0 && 0 <= j < M.Length0 && 0 <= k < M.Length1 &&  j != i  ==> M[i,k] != M[j,k]) {
  var rowsUnique:bool;
  rowsUnique := CheckRows(M);

  var colsUnique:bool;
  colsUnique := CheckCols(M);

  return colsUnique && rowsUnique;
}