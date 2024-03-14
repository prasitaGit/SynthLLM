//ind needs to start from 0 here, as we are determining the first odd
//take the parameter length instead of recomputing everytime
//return -1 if all are even
int firstoddIndex(int a[], unsigned ind, unsigned length)
{
    if(ind == length)
    {
        return -1;
    }
    else if(a[ind] % 2 == 1)
    {//odd element found; immediately return the index ind
        return ind;
    }
    else
    {
        return firstoddIndex(a, ind + 1, length);
    }
}