/*Corresponds to sepcification: {x |-> a * y |-> b}void swaponlyX(int* x, int* y){ x |-> b * y |-> b}*/
void swaponlyX(int *x, int *y)
{
    *x = *y;
}