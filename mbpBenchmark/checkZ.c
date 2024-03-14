//ind needs to start from 0 here, as we are determining the first odd - return -1 if not found; 
//sum will be initialized to 0
//take the parameter length instead of recomputing everytime
//check the ascii now
#include <stdbool.h>
bool checkZ(int a[], unsigned ind, unsigned length)
{
    if(ind == length)
    {
        return false;
    }
    else if(a[ind] == 122 || a[ind] == 90)
    {
        return true;
    }
    else
    {
        return checkZ(a, ind + 1, length);
    }
}