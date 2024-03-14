//start div with 2
#include <stdbool.h>
bool isPrime(int n, int div)
{
   if(n ==2 || n == 3)
   {
        return true;
   }
   else if(div >= n)
   {//does not make sense to continue if div has equaled n; n is prime
        return true;
   }
   else if(n % div == 0)
   {
        return false;
   }
   else
   {
     return isPrime(n, div + 1);
   }
}