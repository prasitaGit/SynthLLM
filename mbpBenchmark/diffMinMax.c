//ind needs to start from 0 here, as we are determining the first odd - return -1 if not found; 
//difference between max and min elements of the array
//assume min and max points to the first element of the array
//assume length of the array is at least 1
//difference will always be non-negative
int diffMinMax(int a[], int min, int max, unsigned ind, unsigned length)
{
    if(ind == length)
    {
        return (max - min);
    }
    else
    {
        if(min > a[ind])
        {
            min = a[ind];
        }
        if(max < a[ind])
        {
            max = a[ind];
        }
        return diffMinMax(a, min, max, ind + 1, length);
    }
}