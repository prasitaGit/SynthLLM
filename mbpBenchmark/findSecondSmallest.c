//returns the second minimum
//ind starts from 1
//length of the array is atleast 1 -> specs.
//min1 and min2 both point to a[0]
int findSecondSmallestNum(int a[], int min1, int min2, unsigned ind, unsigned length)
{
    if(ind == length)
    {
        return min2;
    }
    else if(min1 > a[ind])
    {//min1 becomes a[ind]; min2 becomes
        return findSecondSmallestNum(a, a[ind], min1, ind + 1, length);
    }
    //else if(min2 > a[ind])
    //{
        return findSecondSmallestNum(a, min1, a[ind], ind + 1, length);
    //}
   
}