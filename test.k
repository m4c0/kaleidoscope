# extern sin(x);

def a() 3;
def b(x) a() + x;
def c(x y) b(x) + b(y);

c(5, 6);
c(12, 0);
