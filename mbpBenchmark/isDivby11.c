#include <stdbool.h>
bool isDivBy11(int n)
{
    if(n % 11 == 0)
    {
        return true;
    }
    else
    {
        return false;
    }
}