//ind needs to start from 0 here, as we are determining the first odd - return -1 if not found; 
//sum will be initialized to 0
//take the parameter length instead of recomputing everytime
//has to be i, i + 1
#include <stdbool.h>
bool containsConsecutiveNumbers(int a[], unsigned ind, unsigned length)
{
    if(ind == length - 1)
    {
        return false;
    }
    else if(a[ind] + 1 == a[ind + 1])
    {
        return true;
    }
    else
    {
        return containsConsecutiveNumbers(a, ind + 1, length);
    }
}