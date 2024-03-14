//ind needs to start from length - 1 here, as we are determining the last element
//sum will be initialized to 0
//take the parameter length instead of recomputing everytime
int lastelempos(int a[], int ele, int ind, unsigned length)
{
    if(ind < 0)
    {
        return -1;
    }
    else if(a[ind] == ele)
    {
        return ind;
    }
    else
    {
        return lastelempos(a, ele, ind - 1, length);
    }
}