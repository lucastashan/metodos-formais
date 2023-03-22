ghost function Fat(n:nat): nat
{
    if n == 0
    then 1
    else n * Fat(n-1)
}

method Fatorial(n:nat) returns (x: nat)
    ensures x == Fat(n)
{
    x := 1;
    var i := 1;
    while i < n
        invariant 0 <= i <= n
        invariant x == Fat(i)
    {
        x := x * i;
        i := i + 1;
    }
    // assert i == 0 && 
    // assert x == Fat(n);
}