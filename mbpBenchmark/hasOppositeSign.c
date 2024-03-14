#include <stdbool.h>
bool hasOppositeSign(int a, int b) 
{
    if(a < 0 && b > 0 || a > 0 && b < 0)
    {
        return true;
    }
    else
    {
       return false;
    }
}