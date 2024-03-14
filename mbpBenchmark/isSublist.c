//calls another ecursive function for linear search
//for every element of a, linear search in b
//start searching from 0: more intuitive
#include <stdbool.h>
bool isSublistOne(int a[], int b[], unsigned indA, unsigned indB, unsigned ind, unsigned lengthA, unsigned lengthB)
{//0 to lengthA -> indA; 0 to lengthA -> indB; ind starts from 0
    if((lengthB - ind) < lengthA)
    {
        return false;
    }
    else if(indA == lengthA)
    {//all matched, so return true
        return true;
    }
    else if(a[indA] == b[indB])
    {
        return isSublistOne(a, b, indA + 1, indB + 1, ind, lengthA, lengthB);
    }
    else
    {//not equal
        return isSublistOne(a, b, 0, ind + 1, ind + 1, lengthA, lengthB);
    }
}