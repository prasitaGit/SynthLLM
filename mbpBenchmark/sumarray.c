//ind needs to start from 0 here, as we are determining the first odd - return -1 if not found; 
//sum will be initialized to 0
//take the parameter length instead of recomputing everytime
int sumarray(int a[], int sum, unsigned ind, unsigned length)
{
    if(ind == length)
    {
        return sum;
    }
    else
    {
        return sumarray(a, sum + a[ind], ind + 1, length);
    }
}