//returns the number
//smallest missing number from a sorted array: increasing order
//ind starts from 0
//assume length >= 1
int findSmallestMissingNum(int a[], unsigned ind, unsigned length)
{
    if(ind == length - 1)
    {
        return a[ind] + 1;
    }
    else if((a[ind + 1] - a[ind]) > 1 )
    {
        return a[ind] + 1;
    }
    else
    {
        return findSmallestMissingNum(a, ind + 1, length);
    }
    
}