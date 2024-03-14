//array has odd elements at odd indices
#include <stdbool.h>
bool isOddAtIndexOdd(int a[], unsigned ind, unsigned length)
{
    if(ind == length)
    {
        return true;
    }
    else if(ind % 2 == 1 && a[ind] % 2 == 0)
    {//odd index, even element
        return false;
    }
    else
    {
        return isOddAtIndexOdd(a, ind + 1, length);
    }
   
}