//returns true if all numbers are same, and false otherwise
//ind starts from 0
#include <stdbool.h>
bool allNumsSame(int a[], unsigned ind, unsigned length)
{
    if(ind >= length - 1)
    {//all are same
        return true;
    }
    else if(a[ind] != a[ind + 1])
    {
        return false;
    }
    else
    {
        return allNumsSame(a, ind + 1, length);
    }
    
}