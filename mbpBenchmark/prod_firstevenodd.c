//take the parameter length instead of recomputing everytime
//assign prod to a[0]
//assume length is at least 1
int prod_firsteveodd(int a[], int prod, unsigned ind, unsigned length)
{
    if(ind == length)
    {//all even or all odd
        return -1;
    }
    else if(a[ind] % 2 == 0 && prod % 2 == 1)
    {//present element is even and prod was odd
        return prod * a[ind];
    }
    else if(a[ind] % 2 == 1 && prod % 2 == 0)
    {//present element is odd and prod was even
        return prod * a[ind];
    }
    else
    {
        return prod_firsteveodd(a, prod, ind + 1, length);
    }
}