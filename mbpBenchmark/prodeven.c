//determine if the product of all elements of array is even or not
//prod = 1 at the beginning;
//length is >= 1
#include <stdbool.h>
bool prodeven(unsigned a[], unsigned prod, unsigned ind, unsigned length)
{
    if(ind == length)
    {
        if(prod % 2 == 0)
        {
            return true;
        }
        else
        {
            return false;
        }
    }
    else
    {
        return prodeven(a, prod * a[ind], ind + 1, length);
    }
}