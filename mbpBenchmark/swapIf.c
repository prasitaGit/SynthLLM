/*Corresponds to sepcification: {x |-> a * y |-> b}void swapIf(int* x, int* y){if x < y then x |-> b * y |-> a else x |-> b + 5 * y |-> a + 5}*/
void swapif(int *x, int *y)
{
    int a2 = *x;
    int b2 = *y;
    if(a2 < b2)
    {
        *y = a2;
        *x = b2;
    }
    else
    {
        *y = a2 + 5;
        *x = b2 + 5;
    }

}