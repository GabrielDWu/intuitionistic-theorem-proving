from start import *

class SAT:
    def __init__(self, *args):
        
        if len(args) >= 1:
            
            if type(args[0]) == int:
                self.n = args[0]    #Number of variables
                self.clauses = args[1]  #Given variable i: ~i is represented by 2*i and i is represented by 2*i+1 in clauses
                
            elif type(args[0]) == Sentence:
                self.n, self.clauses  = toCNF(args[0])


def toCNF(sentence):
    """Conjunctive Normal Form. (A | B | ... F) & (P | Q | ... | Z) & ...
        Returns n and a list of lists of integers"""
    lettersCNF = CNFRecurse(sentence)
    mapping = {}    #Maps variables to ids
    next_available = 0

    numbersCNF = []
    for disjunction in lettersCNF:
        new = []
        for var in disjunction:
            if var.atom:
                if var.id not in mapping.keys():
                    mapping[var.id] = next_available
                    next_available += 1
                new.append(mapping[var.id]*2 + 1)

            elif var.op == Name.NOT:   #Must be a not
                if var.left.id not in mapping.keys():
                    mapping[var.left.id] = next_available
                    next_available += 1
                new.append(mapping[var.left.id]*2)
        numbersCNF.append(new)

    return next_available, numbersCNF

def CNFRecurse(sentence):
    """Returns a list of lists of atomic (or ~atom) Sentences."""
    if sentence.atom:
        return [[Sentence(sentence.id)]]

    if sentence.op == Name.AND:
        return CNFRecurse(sentence.left) + CNFRecurse(sentence.right)
    
    if sentence.op == Name.OR:
        
        left, right = CNFRecurse(sentence.left), CNFRecurse(sentence.right)
        conjunction = []

        #Distribute all pairs
        for dis1 in left:
            for dis2 in right:
                conjunction.append(dis1 + dis2)

        return conjunction

    if sentence.op == Name.IMP:
        return CNFRecurse(~sentence.left | sentence.right)
    
    if sentence.op == Name.NOT:
        if sentence.left.atom:
            return [[~Sentence(sentence.left.id)]]
        if sentence.left.op == Name.OR:
            return CNFRecurse(~sentence.left.left & ~sentence.left.right)
        if sentence.left.op == Name.AND:
            return CNFRecurse(~sentence.left.left | ~sentence.left.right)
        if sentence.left.op == Name.NOT:
            return CNFRecurse(sentence.left.left)
        if sentence.left.op == Name.IMP:
            return CNFRecurse(sentence.left.left & ~sentence.left.right)
        
def toNNF(sentence):
    "Negation Normal Form. All nots are on atoms, and (P >> Q) has been converted to (~P | Q)."""
    
    if sentence.atom:
        return Sentence(sentence.id)

    if sentence.op == Name.IMP:
        return toNNF(~sentence.left | sentence.right)

    if sentence.op == Name.NOT:
        if sentence.left.atom:
            return ~toNNF(sentence.left)
        if sentence.left.op == Name.OR:
            return toNNF(~sentence.left.left) & toNNF(~sentence.left.right)
        if sentence.left.op == Name.AND:
            return toNNF(~sentence.left.left) | toNNF(~sentence.left.right)
        if sentence.left.op == Name.NOT:
            return toNNF(sentence.left.left)
        if sentence.left.op == Name.IMP:
            return toNNF(sentence.left.left) & toNNF(~sentence.left.right)

    return Sentence(toNNF(sentence.left), sentence.op, toNNF(sentence.right))
    
        
def SAT_solve(sat):
    """clauses is a list of lists in CNF. n is the number of variables."""

    #Initialize watchlist
    watchlist = [[] for d in range(2*sat.n)]
    for clause in sat.clauses:
        watchlist[clause[0]].append(clause)
    
    tried_0 = [False]*sat.n
    tried_1 = [False]*sat.n

    assignment = [None]*sat.n
    d = 0
    while True:
        if d == sat.n:
            #print(assignment)
            return True   #Valid assignment

        worked = False
        
        if not(tried_0[d]):
            tried_0[d] = True
            assignment[d] = False
            if updateWatchlist(watchlist, assignment, 2*d+1):
                worked = True
            else:
                assignment[d] = None

        elif not(tried_1[d]):
            tried_1[d] = True
            assignment[d] = True
            if updateWatchlist(watchlist, assignment, 2*d):
                worked = True
            else:
                assignment[d] = None

        else:
            if d == 0:
                return False
            assignment[d], tried_0[d], tried_1[d] = None, False, False
            d -= 1
            
        if worked:
            d += 1
            
            

def updateWatchlist(watchlist, assignment, blocked):
    """Reassigns all watchers of the given variable"""
    for i in range(len(watchlist[blocked]), 0, -1):
        clause = watchlist[blocked][i-1]
        worked = False
        
        for literal in clause:
            if assignment[literal>>1] is None or assignment[literal>>1] == literal & 1:
                watchlist[literal].append(clause)
                worked = True
                break

        if not(worked): #Could not find another watchlist to put clause on.
            watchlist[blocked] = watchlist[blocked][:i]
            return False

    return True
            
def classicalTautology(sentence):
    """Returns true iff the sentence is a tautology in classical logic"""
    return not(SAT_solve(SAT(~sentence)))    
