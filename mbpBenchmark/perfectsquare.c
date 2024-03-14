//assume its a non-neg number, otherwise it is pointless
//start val with 0
#include <stdbool.h>
bool perfectsquare(unsigned num, unsigned val)
{
    if(val > num)
    {
        return false;
    }
    else if(val * val == num)
    {
        return true;
    }
    else
    {
        return perfectsquare(num, val + 1);
    }
}