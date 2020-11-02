from start import *

def AND(x, *args):
    if len(x)==0:
        return
    if len(args) == 0:
        i=len(x)-1
    else:
        i=args[0]
    if i == 0:
        return x[i]
    else:
        return AND(x, i-1) & x[i]

def OR(x, *args):
    if len(x)==0:
        return
    if len(args) == 0:
        i=len(x)-1
    else:
        i=args[0]
    if i == 0:
        return x[i]
    else:
        return OR(x, i-1) | x[i]

def EQUIV(x, *args):
    if len(x)==0:
        return
    if len(args) == 0:
        i=len(x)-1
    else:
        i=args[0]
    if i == 0:
        return x[i]
    else:
        return EQUIV(x, i-1) - x[i]

def syj201(n):
    """
    LHS(2*N+1) => RHS(2*N+1) with
    RHS(m) = &&_{i=1..m} p(i),
    LHS(m) = &&_{i=1..m} ((p(i)<=>p(i+1)) => c(m))
    where addition is computed modulo m, and with
    c(N) = &&_{i=1..N} p(i)
    """
    n = 2*n + 1#odd
    p = [Sentence("p"+str(i+1)) for i in range(n)]
    c = AND(p)
    lhs = AND([(p[i] - p[(i+1)%n])>>c for i in range(n)])
    rhs = c
    return lhs >> rhs

def syj202(n):
    """
    Suppose there are N holes and N+1 pigeons to put in the
    holes. Every pigeon is in a hole and no hole contains more
    than one pigeon. Prove that this is impossible. The size is
    the number of pigeons.
    LHS(N) => RHS(N) with 
    LHS(N) = &&_{p=1..N+1} (||_{h=1,..N} o(p,h) )
    RHS(N) = ||_{h=1..N, p1=1..{N+1}, p2={p1+1}..{N+1}} s(p1,p2,h)
    with s(p1,p2,h) = o(p1,h) & o(p2,h)

    Unsolved for n>=10
    """
    p = [[Sentence("p"+str(i+1)+"_"+str(j+1)) for j in range(n)] for i in range(n+1)]

    lhs = AND([ OR([p[i][j] for j in range(n)]) for i in range(n+1)])
    rhs = []
    for h in range(n):
        for p1 in range(n+1):
            for p2 in range(p1+1, n+1):
                rhs.append(p[p1][h] & p[p2][h])
    return lhs >> OR(rhs)

def syj203(n):
    """
    (((&&_{i=1..N} p(i)) | (||_{i=1..N} (p(i)=>f)))=>f)=>f
    """

    p = [Sentence("p"+str(i+1)) for i in range(n)]
    return ~~(AND(p) | OR([~x for x in p]))

def syj204(n):
    """(p(N) & &&_{i=1..N} (p(i) => p(i) => p(i-1))) => p(0)"""
    p = [Sentence("p"+str(i+1)) for i in range(n+1)]
    return (p[n] & AND([p[i] >> (p[i] >> p[i-1]) for i in range(1, n+1)])) >> p[0]

def syj205(n):
    """
    ((A & B(N) & C1(N)) => f) & ((C2(N) & B(N) & A) => f) with
    A = (a(0) => f), B(N) = ((b(N) => b(0)) => a(N)),
    C1(N) = (&&_{i=1..n} ((b(i-1) => a(i)) => a(i-1))),
    C2(N) = (&&_{i=n..1} ((b(i-1) => a(i)) => a(i-1)))
    """
    a = [Sentence("a"+str(i+1)) for i in range(n+1)]
    b = [Sentence("b"+str(i+1)) for i in range(n+1)]
    A = ~a[0]
    B = (b[n] >> b[0]) >> a[n]
    C1 = AND([(b[i-1] >> a[i]) >> a[i-1] for i in range(1, n+1)])
    C2 = AND([(b[i-1] >> a[i]) >> a[i-1] for i in range(n, 0, -1)])

    return (~(A & B & C1) & ~(C2 & B & A))

def syj206(n):
    """
    (..(( p(1) <=> p(2)) <=> p(3)) <=> .. <=> p(N))  <=> (p(N) <=> ( p(N-1) <=> (.. (p(2) <=> p(1)) ) ))
    Permutation of <=>

    for some reason my program says syj206(n) is a non-theorem for n>=3, even though it is a valid theorem.
    Oops, nevermind. I was doing order of operations wrong.
    """
    p = [Sentence("p"+str(i+1)) for i in range(n)]
    return EQUIV(p) - EQUIV(p[::-1]) #incorrect order of operations. look at the parenthesis.

def syj207(n):
    """
    LHS(2*N) -> (p0 | RHS(2*N) | ~p0)
    RHS(m) = &&_{i=1..m} p(i),
    LHS(m) = &&_{i=1..m} ((p(i)<=>p(i+1)) => c(m))
    where addition is computed modulo m, and with
    c(N) = &&_{i=1..N} p(i)

    Not a theorem!
    """
    n = 2*n#even
    p = [Sentence("p"+str(i+1)) for i in range(n)]
    c = AND(p)
    lhs = AND([(p[i] - p[(i+1)%n])>>c for i in range(n)])
    rhs = c
    p0 = Sentence("p0")
    return lhs >> (p0 | rhs | ~p0)

def syj208(n):
    """
    Suppose there are N holes and N+1 pigeons to put in the
    holes. Every pigeon is in a hole and no hole contains more
    than one pigeon. Prove that this is impossible. The size is
    the number of pigeons.
    LHS(N) => RHS(N) with 
    LHS(N) = &&_{p=1..N+1} (||_{h=1,..N-1} o(p,h) | ~~o(p,N) )
    RHS(N) = ||_{h=1..N, p1=1..{N+1}, p2={p1+1}..{N+1}} s(p1,p2,h)
    with s(p1,p2,h) = o(p1,h) & o(p2,h)

    Not a theorem!
    """
    p = [[Sentence("p"+str(i+1)+"_"+str(j+1)) for j in range(n)] for i in range(n+1)]

    if n==1:
        return (~~p[0][0] & ~~p[1][0]) >> (p[0][0] | p[1][0])
    lhs = AND([ OR([p[i][j] for j in range(n-1)]) | ~~p[i][n-1] for i in range(n+1)])
    rhs = []
    for h in range(n):
        for p1 in range(n+1):
            for p2 in range(p1+1, n+1):
                rhs.append(p[p1][h] & p[p2][h])
    return lhs >> OR(rhs)

def syj209(n):
    """
    ((&&_{i=1..N} p(i) | ~~p(1)=>f | ||_{i=2..N} (p(i)=>f))=>f)=>f

    Supposed to be a non-theorem, but my program found a proof :thinking:
    """

    p = [Sentence("p"+str(i+1)) for i in range(n)]
    if n>1:
        return ~~(AND(p) | ~~~p[0] | OR([~x for x in p[1:]]))
    else:
        return ~~(AND(p) | ~~~p[0])

def syj210(n):
    """
    (~~p(N) & &&_{i=1..N} (p(i) => p(i) => p(i-1))) => p(0)
    non-theorem
    """
    p = [Sentence("p"+str(i+1)) for i in range(n+1)]
    return (~~p[n] & AND([p[i] >> (p[i] >> p[i-1]) for i in range(1, n+1)])) >> p[0]

def syj211(n):
    """
    (A & B(N) & C(N)) => f with
    A = (a(0) => f), B(N) = (~~b(N) => b(0) => a(N)),
    C(N) = (&&_{i=1..n} ((~~b(i-1) => a(i)) => a(i-1))),

    Supposed to be a non-theorem, but my program found a proof
    """
    a = [Sentence("a"+str(i+1)) for i in range(n+1)]
    b = [Sentence("b"+str(i+1)) for i in range(n+1)]
    A = ~a[0]
    B = (~~b[n] >> b[0]) >> a[n]
    C = AND([(~~b[i-1] >> a[i]) >> a[i-1] for i in range(1, n+1)])

    return ~(A & B & C)

def syj212(n):
    """
    (..(( ~~p(1) <=> p(2)) <=> p(3)) <=> .. <=> p(N))  <=> (p(N) <=> ( p(N-1) <=> (.. (p(2) <=> p(1)) ) ))
    Permutation of <=>

    Not a theorem    
    """
    p = [Sentence("p"+str(i+1)) for i in range(n)]
    q = p[:]
    q[0] = ~~p[0]
    return EQUIV(q) - EQUIV(p[::-1])


from multiprocessing import Process
import time

processes = []
TESTS = 10

def reset():
    for i in processes:
        i.terminate()
    
        
def trial_set(meth, test, label):
    keep_going = 1
    for n in range(1, 20):
        if keep_going==0:
            break
        keep_going = 0
        for i in range(TESTS):
            # We create a Process
            action_process = Process(target=single_trial, args=(meth, test, label, n))
            processes.append(action_process)
            action_process.start()
            action_process.join(timeout=5)
            action_process.terminate()
            del processes[-1]

            strout = open("data.txt", "r").read()
            if len(strout.strip()) == 0:
                print(label+"\t"+str(n)+"\tDNF\tNA\n", end="")
            else:
                print(strout, end="")
                keep_going += 1
            open("data.txt","w").close()
            
##            f = open("errors.txt", "r")
##            print(f.read(), end="")
##            f.close()
##            open("errors.txt","w").close()


def single_trial(meth, test, label, n):
    try:
        start = time.time()
        ptn = prove(test(n), method=meth, verbose=0)
        end = time.time()
        f = open("data.txt", "a")
        f.write(label + "\t" + str(n) + "\t" + str(end-start) + "\t" + str(-1 if ptn==None else ptn.getSize()) + "\n")
        f.close()
    except:
        pass

f = open("data.txt","w")
f.close()
f = open("errors.txt","w")
f.close()
if __name__=="__main__":
    for test in [(syj201, "syj201"), (syj202, "syj202"), (syj203, "syj203"), (syj204, "syj204"), (syj205, "syj205"), (syj206, "syj206"), (syj207, "syj207"),
                 (syj208, "syj208"), (syj209, "syj209"), (syj210, "syj210"), (syj211, "syj211"), (syj212, "syj212")]:
        for meth in [(randomDFS, "basic"), (randomDFS_noRepeats, "no_reps"), (randomDFS_LJT, "LJT")]:

            trial_set(meth[0], test[0], meth[1]+"\t"+test[1])
            
