//returns the number
//ind starts from 0
//length >= 1
//length of the array is atleast 1 -> specs.
int findSmallestNum(int a[], int min, unsigned ind, unsigned length)
{
    if(ind == length)
    {
        return min;
    }
    else if(ind == 0)
    {
        return findSmallestNum(a,a[ind], ind + 1, length);
       
    }
    else if(min > a[ind])
    {
        return findSmallestNum(a,a[ind], ind + 1, length);
    }
    //else
    //{
        return findSmallestNum(a, min, ind + 1, length);
    //}
    
}