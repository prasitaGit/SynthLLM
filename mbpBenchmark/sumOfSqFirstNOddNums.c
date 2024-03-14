//sum of squares of first n odd numbers (starting with 1)
// sum = 0 (at the beginning)
//c = 1 (at the beginning)
//num = 1 (at the beginning)
unsigned sumOfSqofFirstNOddNums(unsigned n, unsigned sum, unsigned num, unsigned c)
{
   if(n == c)
   {
        return (sum + num * num);
   }
   return sumOfSqofFirstNOddNums(n, sum + num * num, num + 2, c + 1);
}