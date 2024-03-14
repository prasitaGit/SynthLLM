//returns true 
//ind starts from 0
#include <stdbool.h>
bool checkGreaterthanAll(int a[], int n, unsigned ind, unsigned length)
{
    if(ind == length)
    {
        return true;
    }
    else if(n <= a[ind])
    {
        return false;
    }
    else
    {
        return checkGreaterthanAll(a,n, ind + 1, length);
    }
    
}