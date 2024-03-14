//ind starts from 0
//returns false if array is not sorted, otherwise true.
#include <stdbool.h>
bool checkSorted(int a[], unsigned ind, unsigned length)
{
    if(ind == length - 1)
    {
        return true;
    }
    else if(a[ind] > a[ind + 1])
    {
        return false;
    }
    else
    {
        return checkSorted(a, ind + 1, length);
    }
}