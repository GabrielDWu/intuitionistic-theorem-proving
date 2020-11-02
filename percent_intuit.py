from start import *
import random

##size = []
##
##def init_size(num_vars):
##    global size
##    num_ops = 3
##    size.append(-999999999)
##    size.append(num_vars)
##    for i in range(2, 15):
##        tot = 0
##        for j in range(1, i):
##            tot += size[j]*size[i-j]
##        size.append(tot*num_ops)


def rand_tree(n):
    """generates a random complete binary tree with n leaves"""
    if n==2:
        return [[0,1],[0,2]]
    x = rand_tree(n-1) #edges
    random.shuffle(x)
    edge = x.pop()
    x.append([edge[0], 2*n-3])
    x.append([2*n-3, edge[1]])
    x.append([2*n-3, 2*n-2])

    return x

def rand_sentence(num_vars, sz):
    p = [Sentence("P"+str(i)) for i in range(num_vars)]
    if sz == 1:
        return p[0]

    tree = rand_tree(sz)
    random.shuffle(tree)
    adj = [[] for i in range(2*sz-1)]
    for edge in tree:
        adj[edge[0]].append(edge[1])

    return dfs(p,  adj, 0)

def dfs(p, adj, node):
    if len(adj[node]) == 0:
        return random.choice(p)
    op = random.randint(1, 3)
    if random.randint(1, 2) == 1:
        if op==1:
            return dfs(p, adj, adj[node][0]) | dfs(p, adj, adj[node][1])
        elif op==2:
            return dfs(p, adj, adj[node][0]) & dfs(p, adj, adj[node][1])
        elif op==3:
            return dfs(p, adj, adj[node][0]) >> dfs(p, adj, adj[node][1])
    else:
        if op==1:
            return ~dfs(p, adj, adj[node][0]) | dfs(p, adj, adj[node][1])
        elif op==2:
            return ~dfs(p, adj, adj[node][0]) & dfs(p, adj, adj[node][1])
        elif op==3:
            return ~dfs(p, adj, adj[node][0]) >> dfs(p, adj, adj[node][1])


def percent_intuit(num_vars, sz):
    tot = 0
    taut = 0
    intuit = 0
    while taut < 200 and tot < 10000:
        
        x = rand_sentence(num_vars, sz)
        p = prove(x, verbose=False)
        tot += 1
        if p != False:
            taut += 1
            if p!=None:
                intuit += 1

                print(intuit, taut)

    if taut > 0:
        return intuit/taut, taut/tot
    else:
        return -1, taut/tot

table_it = []
table_tt = []
for i in range(1, 10):
    table_it.append([])
    table_tt.append([])
    for j in range(1, 10):
        x, y = percent_intuit(i, j)
        table_it[-1].append(x)
        table_tt[-1].append(y)

print("table it")
for x in table_it:
    print("\t".join([str(round(y, 5)) for y in x]))
print("table tt")
for x in table_tt:
    print("\t".join([str(round(y, 5)) for y in x]))
