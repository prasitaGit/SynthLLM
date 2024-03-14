//array has only one element
//ind is initialized to 0
//no elements differ
#include <stdbool.h>
bool detArrayHasOnlyOneElement(int a[], unsigned ind, unsigned length)
{
    if(ind == length - 1)
    {//distinct elements indeed
        return true;
    }
    else if(a[ind] != a[ind + 1])
    {//non-equal elements -> false
        return false;
    }
    else
    {
        return detArrayHasOnlyOneElement(a, ind + 1, length);
    }
   
}