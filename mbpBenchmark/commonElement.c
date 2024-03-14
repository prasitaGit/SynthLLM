#include<stdbool.h>
//just one function : no helper
//indA, indB are both initialized to 0
bool commonElementOne(int a[], int b[], unsigned indA, unsigned indB, unsigned lengthA, unsigned lengthB)
{
    if(indA == lengthA)
    {//no common element exists
        return false;
    }
    else if(indB == lengthB)
    {//increment indB by 1
        return commonElementOne(a, b ,indA + 1, 0, lengthA, lengthB);
    }
    else if(a[indA] == b[indB])
    {//common element found
        return true;
    }
    else
    {//increment indB
        return commonElementOne(a, b, indA, indB + 1, lengthA, lengthB);
    }
}