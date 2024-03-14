//take the parameter length instead of recomputing everytime
//1-indexed: k can range from 1 to length
//return -1 if k is oob
int getkthElement(unsigned a[], int k, unsigned length)
{
    if(k < 1 || k > length)
    {
        return -1;
    }
    else
    {
        return a[k - 1];
    }
}