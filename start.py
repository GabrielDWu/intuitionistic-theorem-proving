class Sequent:

    def __init__(self, antecedent, succedent):
        self.ant = antecedent   #List of antecedents
        self.succ = succedent   #A single succedent (because we are in IPL)

    def __str__(self):
        return ", ".join(map(str, self.ant)) + " ⊢ " + str(self.succ)

    def __hash__(self):
        return sum( map(hash, map(str, self.ant)) ) + hash("suc" + str(self.succ))

    def __eq__(self, other):
        """If a sequent is exactly the same as another, except allowing for a different permuation of ant"""
        return hash(self) == hash(other)

    
class Sentence:
    """A formula made of propositional variables"""
    
    def __init__(self, *args):
        
        if len(args) == 1:
            self.atom = True
            self.id = args[0]

            self.size = 1

        else:
            self.atom = False
            self.left = args[0]     #Left Formula
            self.op = args[1]       #Operator
            self.size = 1+self.left.size
            if self.op != Name.NOT:
                self.right = args[2]    #Right Formula
                self.size += self.right.size

    def notToImpF(self):
        if self.atom:
            return Sentence(self.id)

        if self.op == Name.NOT:
            return Sentence(self.left.notToImpF(), Name.IMP, Name.F)

        return Sentence(self.left.notToImpF(), self.op, self.right.notToImpF())

    def __eq__(self, other):
        """If a sentence is exactly the same as another sentence"""

        #Consider replacing with a hash function later on?
        
        if self.atom and other.atom:
            return self.id == other.id

        if self.atom != other.atom:
            return False

        if self.op != other.op:
            return False

        if self.op == Name.NOT:
            return self.left == other.left
        
        return self.left == other.left and self.right == other.right

    def __str__(self):

        if self.atom:
            return str(self.id)

        if self.op == Name.NOT:
            return Name.NOT+str(self.left)
        
        return "("+str(self.left)+" "+str(self.op)+" "+str(self.right)+")"

    def __or__(a, b):
        return Sentence(a, Name.OR, b)

    def __and__(a, b):
        return Sentence(a, Name.AND, b)

    def __rshift__(a, b):
        return Sentence(a, Name.IMP, b)
    
    def __invert__(a):
        return Sentence(a, Name.NOT)

    def __sub__(a, b):
        return (a >> b) & (b >> a)

class ProofTreeNode:
    """A node on a tree of sequents that follow the rules of inference"""

    def __init__(self, seq, *args):
        self.seq = seq
        self.inf = None
        self.children = None
        self.depth = 0
        self.size = None        
        
        if len(args):
            self.parent = args[0]   #Parent ProofTree
            self.depth = self.parent.depth + 1

    def infer(self, x):
        """Sets the inference rule and children of the Node"""
        self.inf = x[0]
        self.children = [ProofTreeNode(seq, self) for seq in x[1]]

        return self.children

    def clear(self):
        self.inf = None
        self.children = None

    def plaintext(self):
        """Returns a list of lines which represent a human-readable proof tree"""
        overhang = 6 #The width of the inference rule label

        strseq = str(self.seq)
        
        width = len(strseq) + overhang
        out = []
        if self.children is not None and len(self.children) > 0:
            stacks = [ptn.plaintext() for ptn in self.children]
            height = max([len(x) for x in stacks])

            #Pad empty lines at the top
            for i in range(len(self.children)):
                stacks[i] = [" "*len(stacks[i][0])]*(height-len(stacks[i])) + stacks[i]

            for i in range(height):
                out.append("  ".join([stacks[j][i] for j in range(len(self.children))]).ljust(width))
            width = max(width, len(out[0]))

        if self.inf is not None:
            out.append(("—"*(width-overhang)+" "+self.inf).ljust(width))
        
            
        out.append((" "*((width-overhang-len(strseq))//2) + strseq).ljust(width))
        
        return out

    def sizeRecurse(self):

        if self.size is not None:
            return self.size
        
        if self.children is None:
            self.size = 1
        else:
            self.size = 1 + sum([child.sizeRecurse() for child in self.children])

        return self.size

    def resetSize(self):

        if self.size is None:
            return
        
        self.size = None
        if self.children is not None:
            for child in self.children:
                child.resetSize()

    def getSize(self):
        size = self.sizeRecurse()
        self.resetSize()

        return size
    
    def __str__(self):
        return "\n".join(self.plaintext())

    

class Name: 
    AND = "∧"
    OR = "∨"
    IMP = "→"
    NOT = "¬"
    
    F = Sentence("⊥")

    init = "Init"
    fL = "⊥L"
    andL = "∧L"
    andR = "∧R"
    orL = "∨L"
    orR1 = "∨R1"
    orR2 = "∨R2"
    impL = "→L"
    impR = "→R"
    perm = "Perm"

    impL1 = "→L1"
    impL2 = "→L2"
    impL3 = "→L3"
    impL4 = "→L4"
    

##           -- Inference rules --              ##

def init(seq, i):
    """
    ———————— Init
    A, Γ ⊢ A
    """
    if initcheck(seq, i):
        return Name.init, []
    raise Exception("Cannot apply Init to " + str(seq) + " with A=" + str(seq.ant[i]))

def initcheck(seq, i):
    return seq.ant[i] == seq.succ

def fL(seq, i):
    """
    ————————— ⊥L
    ⊥, Γ ⊢ G
    """
    if fLcheck(seq, i):
        return Name.fL, []
    raise Exception("Cannot apply ⊥L to " + str(seq) + " because " + str(seq.ant[i]) + " is not ⊥")

def fLcheck(seq, i):
    return seq.ant[i] == Name.F

def andL(seq, i):
    """
    A, B, Γ ⊢ G
    ——————————— ∧L
    A∧B, Γ ⊢ G
    """
    if andLcheck(seq, i):
        return Name.andL, [Sequent(seq.ant[:i] + [seq.ant[i].left, seq.ant[i].right] + seq.ant[i+1:], seq.succ)]
    raise Exception("Cannot apply ∧L to " + str(seq) + " with A∧B=" + str(seq.ant[i]))

def andLcheck(seq, i):
    return not seq.ant[i].atom and seq.ant[i].op == Name.AND

def andR(seq):
    """
    Γ ⊢ A     Γ ⊢ B
    ——————————————— ∧R
        Γ ⊢ A∧B
    """
    if andRcheck(seq):
        return Name.andR, [Sequent(seq.ant, seq.succ.left), Sequent(seq.ant, seq.succ.right)]
    raise Exception("Cannot apply ∧R to " + str(seq))

def andRcheck(seq):
    return not seq.succ.atom and seq.succ.op == Name.AND

def orL(seq, i):
    """
    A, Γ ⊢ G   B, Γ ⊢ G
    ——————————————————— ∨L
        A∨B, Γ ⊢ G
    """
    if orLcheck(seq, i):
        return Name.orL, [Sequent(seq.ant[:i] + [seq.ant[i].left] + seq.ant[i+1:], seq.succ), Sequent(seq.ant[:i] + [seq.ant[i].right] + seq.ant[i+1:], seq.succ)]
    raise Exception("Cannot apply ∨L to " + str(seq) + " with A∨B=" + str(seq.ant[i]))

def orLcheck(seq, i):
    return not seq.ant[i].atom and seq.ant[i].op == Name.OR


def orR1(seq):
    """
     Γ ⊢ A
    ———————— ∨R1
    Γ ⊢ A∨B
    """
    if orR1check(seq):
        return Name.orR1, [Sequent(seq.ant, seq.succ.left)]
    raise Exception("Cannot apply ∨R1 to " + str(seq))

def orR1check(seq):
    return not seq.succ.atom and seq.succ.op == Name.OR


def orR2(seq):
    """
     Γ ⊢ B
    ———————— ∨R2
    Γ ⊢ A∨B
    """
    if orR2check(seq):
        return Name.orR2, [Sequent(seq.ant, seq.succ.right)]
    raise Exception("Cannot apply ∨R2 to " + str(seq))

def orR2check(seq):
    return not seq.succ.atom and seq.succ.op == Name.OR

#This rule is not included in LJT
def impL(seq, i):
    """
    A→B, Γ ⊢ A     B, Γ ⊢ G
    ——————————————————————— →L
           A→B, Γ ⊢ G
    """
    if impLcheck(seq, i):
        return Name.impL, [Sequent(seq.ant, seq.ant[i].left), Sequent(seq.ant[:i] + [seq.ant[i].right] + seq.ant[i+1:], seq.succ)]
    raise Exception("Cannot apply →L to " + str(seq) + " with A→B=" + str(seq.ant[i]))

def impLcheck(seq, i):
    return not seq.ant[i].atom and seq.ant[i].op == Name.IMP

def impR(seq):
    """
    A, Γ ⊢ B
    ———————— →R
    Γ ⊢ A→B
    """
    if impRcheck(seq):
        return Name.impR, [Sequent([seq.succ.left] + seq.ant, seq.succ.right)]
    raise Exception("Cannot apply →R to " + str(seq))

def impRcheck(seq):
    return not seq.succ.atom and seq.succ.op == Name.IMP

##           -- Special LJT Inference Rules --             ##
def impL1(seq, i):
    """
     B, A, Γ ⊢ G
    ————————————— →L1  [A being atomic and not ⊥]
    A→B, A, Γ ⊢ G
    """
    if impL1check(seq, i):
        return Name.impL1, [Sequent(seq.ant[:i] + [seq.ant[i].right] + seq.ant[i+1:], seq.succ)]
    raise Exception("Cannot apply →L1 to " + str(seq) + " with A→B=" + str(seq.ant[i]))

def impL1check(seq, i):
    return not seq.ant[i].atom and seq.ant[i].op == Name.IMP and seq.ant[i].left.atom and seq.ant[i].left != Name.F and seq.ant[i].left in seq.ant

def impL2(seq, i):
    """
    A→(B→C), Γ ⊢ G
    ——————————————— →L2
    (A∧B)→C, Γ ⊢ G
    """
    if impL2check(seq, i):
        return Name.impL2, [Sequent(seq.ant[:i] + [seq.ant[i].left.left >> (seq.ant[i].left.right >> seq.ant[i].right)] + seq.ant[i+1:], seq.succ)]
    raise Exception("Cannot apply →L2 to " + str(seq) + " with (A∧B)→C=" + str(seq.ant[i]))

def impL2check(seq, i):
    return not seq.ant[i].atom and seq.ant[i].op == Name.IMP and not seq.ant[i].left.atom and seq.ant[i].left.op == Name.AND

def impL3(seq, i):
    """
    A→C, B→C, Γ ⊢ G
    ——————————————— →L3
    (A∨B)→C, Γ ⊢ G
    """
    if impL3check(seq, i):
        return Name.impL3, [Sequent(seq.ant[:i] + [seq.ant[i].left.left >> seq.ant[i].right, seq.ant[i].left.right >> seq.ant[i].right] + seq.ant[i+1:], seq.succ)]
    raise Exception("Cannot apply →L3 to " + str(seq) + " with (A∨B)→C=" + str(seq.ant[i]))

def impL3check(seq, i):
    return not seq.ant[i].atom and seq.ant[i].op == Name.IMP and not seq.ant[i].left.atom and seq.ant[i].left.op == Name.OR

def impL4(seq, i):
    """
    B→C, Γ ⊢ (A→B)    C, Γ ⊢ G
    —————————————————————————— →L4
          (A→B)→C, Γ ⊢ G
    """
    if impL4check(seq, i):
        return Name.impL4, [Sequent(seq.ant[:i] + [seq.ant[i].left.right >> seq.ant[i].right] + seq.ant[i+1:], seq.ant[i].left),
                            Sequent(seq.ant[:i] + [seq.ant[i].right] + seq.ant[i+1:], seq.succ)]
    raise Exception("Cannot apply →L4 to " + str(seq) + " with (A→B)→C=" + str(seq.ant[i]))

def impL4check(seq, i):
    return not seq.ant[i].atom and seq.ant[i].op == Name.IMP and not seq.ant[i].left.atom and seq.ant[i].left.op == Name.IMP


##           -- Heuristical Provers --             ##
from random import shuffle, randint
from time import time
from sat import *
from sys import setrecursionlimit

setrecursionlimit(100000000)

def prove(statement, **kwargs):
    """DFS to find the proof tree. Guaranteed to find a proof if it exists with depth < max_depth, but may take a long time."""
    
    if "max_depth" not in kwargs.keys():
        max_depth = 1000
    else:
        max_depth = kwargs["max_depth"]

    verbose = True
    if "verbose" in kwargs.keys(): verbose = kwargs["verbose"]

    check_taut = True
    if "check_taut" in kwargs.keys(): check_taut = kwargs["check_taut"]

    method = randomDFS_LJT
    if "method" in kwargs.keys(): method = kwargs["method"]

    if verbose: print("Goal Sentence:", statement)

    if check_taut and not(classicalTautology(statement)):
        if verbose: print("Statement is not a classical tautology, so it cannot be proven in IPL.")
        return False
    else:
        if verbose:  print("Statement is a classical tautology.")
    
    ptn = ProofTreeNode(Sequent([], statement.notToImpF()))

    global debug_ptn
    debug_ptn = ptn

    start = time()
    if method == randomDFS:
        success = randomDFS(ptn, max_depth)
    elif method == randomDFS_noRepeats:
        success = randomDFS_noRepeats(ptn, max_depth, {})
    elif method == randomDFS_LJT:
        success = randomDFS_LJT(ptn, max_depth, {})
    

    if verbose: print("Elapsed:", int((time() - start)*1000), "ms")
    if success:
        if verbose:
            print("Success.")
            if ptn.getSize() <= 1000:
                print("Printing...")
                print(str(ptn))
            else: print("Proof is too long to print.")
        return ptn
    else:
        if verbose:
            print("Could not find a proof.")
        return None

def randomDFS(ptn, max_depth):
    """Applies inference rules in a random order. Returns true if the subtree becomes resolved."""
    
    if ptn.depth > max_depth:
        return False

    seq = ptn.seq    

    order = list(range(2, 9))
    shuffle(order)
    order = [0, 1] + order #Always check init first
    order_ind = 0
    ind = 0

    if seq.ant:
        rand_start = randint(0, len(seq.ant)-1)  #What index it starts at when it needs to decide which sentence to apply a rule to.
    
    while order_ind < len(order):
        inf = order[order_ind]
        action = None

        if seq.ant:
            adjusted_ind = (rand_start + ind)%len(seq.ant)
        
        if inf == 0:
            if ind < len(seq.ant):
                if initcheck(seq, adjusted_ind):
                    action = init(seq, adjusted_ind)
                ind += 1
            else:
                ind = 0
                order_ind += 1

        elif inf == 1:
            if ind < len(seq.ant):
                if fLcheck(seq, adjusted_ind):
                    action = fL(seq, adjusted_ind)
                ind += 1
            else:
                ind = 0
                order_ind += 1
        
        elif inf == 2:
            if ind < len(seq.ant):
                if andLcheck(seq, adjusted_ind):
                    action = andL(seq, adjusted_ind)
                ind += 1
            else:
                ind = 0
                order_ind += 1

        elif inf == 3:
            if andRcheck(seq):
                action = andR(seq)
            order_ind += 1

        elif inf == 4:
            if ind < len(seq.ant):
                if orLcheck(seq, adjusted_ind):
                    action = orL(seq, adjusted_ind)
                ind += 1
            else:
                ind = 0
                order_ind += 1

        elif inf == 5:
            if orR1check(seq):
                action = orR1(seq)
            order_ind += 1

        elif inf == 6:
            if orR2check(seq):
                action = orR2(seq)
            order_ind += 1

        elif inf == 7:
            if ind < len(seq.ant):
                if impLcheck(seq, adjusted_ind):
                    action = impL(seq, adjusted_ind)
                ind += 1
            else:
                ind = 0
                order_ind += 1

        elif inf == 8:
            if impRcheck(seq):
                action = impR(seq)
            order_ind += 1

        if action != None:
            newNodes = ptn.infer(action)
            resolved = True
            
            for node in newNodes:
                if not(randomDFS(node, max_depth)):
                    ptn.clear()
                    resolved = False
                    break

            if resolved:
                return True
        
    return False

def randomDFS_noRepeats(ptn, max_depth, complete):
    """Applies inference rules in a random order. Returns true if the subtree becomes resolved.
    Does not allow repeats of an unresolved sequent, and does not redo the work of already resolved sequents.
    complete is a dictionary which maps sequents to either ints or ProofTreeNodes. An int means that it hasn't been resolved at that starting depth."""
        
    if ptn.depth > max_depth:
        return False
    
    seq = ptn.seq

    if seq in complete.keys():
        status = complete[seq]
        if type(status) == int:   #This is a repeat of an ancestor, or a previously failed attempt
            if ptn.depth < status:  #Previously, it just might have been too high up to work. We can try again.
                complete[seq] = ptn.depth
            else:
                return False    #We already tried this at a smaller depth. It is impossible for it to work now.
        else:
            ptn.inf, ptn.children = status.inf, status.children
            return True
    else:
        complete[seq] = ptn.depth   #It will be an integer until it is resolved
        
    order = list(range(2, 9))
    shuffle(order)
    order = [0, 1] + order #Always check init first
    order_ind = 0
    ind = 0

    if seq.ant:
        rand_start = randint(0, len(seq.ant)-1)  #What index it starts at when it needs to decide which sentence to apply a rule to.
    
    while order_ind < len(order):
        inf = order[order_ind]
        action = None

        if seq.ant:
            adjusted_ind = (rand_start + ind)%len(seq.ant)
        
        if inf == 0:
            if ind < len(seq.ant):
                if initcheck(seq, adjusted_ind):
                    action = init(seq, adjusted_ind)
                ind += 1
            else:
                ind = 0
                order_ind += 1

        elif inf == 1:
            if ind < len(seq.ant):
                if fLcheck(seq, adjusted_ind):
                    action = fL(seq, adjusted_ind)
                ind += 1
            else:
                ind = 0
                order_ind += 1
        
        elif inf == 2:
            if ind < len(seq.ant):
                if andLcheck(seq, adjusted_ind):
                    action = andL(seq, adjusted_ind)
                ind += 1
            else:
                ind = 0
                order_ind += 1

        elif inf == 3:
            if andRcheck(seq):
                action = andR(seq)
            order_ind += 1

        elif inf == 4:
            if ind < len(seq.ant):
                if orLcheck(seq, adjusted_ind):
                    action = orL(seq, adjusted_ind)
                ind += 1
            else:
                ind = 0
                order_ind += 1

        elif inf == 5:
            if orR1check(seq):
                action = orR1(seq)
            order_ind += 1

        elif inf == 6:
            if orR2check(seq):
                action = orR2(seq)
            order_ind += 1

        elif inf == 7:
            if ind < len(seq.ant):
                if impLcheck(seq, adjusted_ind):
                    action = impL(seq, adjusted_ind)
                ind += 1
            else:
                ind = 0
                order_ind += 1

        elif inf == 8:
            if impRcheck(seq):
                action = impR(seq)
            order_ind += 1

        if action != None:
            newNodes = ptn.infer(action)
            resolved = True
            
            for node in newNodes:
                if not(randomDFS_noRepeats(node, max_depth, complete)):
                    ptn.clear()
                    resolved = False
                    break

            if resolved:
                complete[seq] = ptn
                return True
        
    return False

def randomDFS_LJT(ptn, max_depth, complete):
    """Applies inference rules in a random order, using the LJT system. Repeats within a subtree are guaranteed to be impossible.
    Returns true if the subtree becomes resolved.
    Does not redo the work of already resolved sequents.
    complete is a dictionary which maps sequents to either ints or ProofTreeNodes. An int means that it hasn't been resolved at that starting depth."""
    
    if ptn.depth > max_depth:
        return False
    
    seq = ptn.seq

    if seq in complete.keys():
        status = complete[seq]
        if type(status) == int:   #This is a repeat of an ancestor, or a previously failed attempt
            if ptn.depth < status:  #Previously, it just might have been too high up to work. We can try again.
                complete[seq] = ptn.depth
            else:
                return False    #We already tried this at a smaller depth. It is impossible for it to work now.
        else:
            ptn.inf, ptn.children = status.inf, status.children
            return True
    else:
        complete[seq] = ptn.depth   #It will be an integer until it is resolved
        
    order = list(range(2, 12))
    shuffle(order)
    order = [0, 1] + order #Always check init first
    order_ind = 0
    ind = 0

    if seq.ant:
        rand_start = randint(0, len(seq.ant)-1)  #What index it starts at when it needs to decide which sentence to apply a rule to.
    
    while order_ind < len(order):
        inf = order[order_ind]
        action = None

        if seq.ant:
            adjusted_ind = (rand_start + ind)%len(seq.ant)
        
        if inf == 0:
            if ind < len(seq.ant):
                if initcheck(seq, adjusted_ind):
                    action = init(seq, adjusted_ind)
                ind += 1
            else:
                ind = 0
                order_ind += 1

        elif inf == 1:
            if ind < len(seq.ant):
                if fLcheck(seq, adjusted_ind):
                    action = fL(seq, adjusted_ind)
                ind += 1
            else:
                ind = 0
                order_ind += 1
        
        elif inf == 2:
            if ind < len(seq.ant):
                if andLcheck(seq, adjusted_ind):
                    action = andL(seq, adjusted_ind)
                ind += 1
            else:
                ind = 0
                order_ind += 1

        elif inf == 3:
            if andRcheck(seq):
                action = andR(seq)
            order_ind += 1

        elif inf == 4:
            if ind < len(seq.ant):
                if orLcheck(seq, adjusted_ind):
                    action = orL(seq, adjusted_ind)
                ind += 1
            else:
                ind = 0
                order_ind += 1

        elif inf == 5:
            if orR1check(seq):
                action = orR1(seq)
            order_ind += 1

        elif inf == 6:
            if orR2check(seq):
                action = orR2(seq)
            order_ind += 1

        elif inf == 7:
            if ind < len(seq.ant):
                if impL1check(seq, adjusted_ind):
                    action = impL1(seq, adjusted_ind)
                ind += 1
            else:
                ind = 0
                order_ind += 1

        elif inf == 8:
            if ind < len(seq.ant):
                if impL2check(seq, adjusted_ind):
                    action = impL2(seq, adjusted_ind)
                ind += 1
            else:
                ind = 0
                order_ind += 1

        elif inf == 9:
            if ind < len(seq.ant):
                if impL3check(seq, adjusted_ind):
                    action = impL3(seq, adjusted_ind)
                ind += 1
            else:
                ind = 0
                order_ind += 1

        elif inf == 10:
            if ind < len(seq.ant):
                if impL4check(seq, adjusted_ind):
                    action = impL4(seq, adjusted_ind)
                ind += 1
            else:
                ind = 0
                order_ind += 1

        elif inf == 11:
            if impRcheck(seq):
                action = impR(seq)
            order_ind += 1

        if action != None:
            newNodes = ptn.infer(action)
            resolved = True
            
            for node in newNodes:
                if not(randomDFS_LJT(node, max_depth, complete)):
                    ptn.clear()
                    resolved = False
                    break

            if resolved:
                
                complete[seq] = ptn
                return True
        
    return False

P = Sentence("P")
Q = Sentence("Q")
R = Sentence("R")
S = Sentence("S")
T = Sentence("T")
A = Sentence("A")
B = Sentence("B")
C = Sentence("C")
D = Sentence("D")
E = Sentence("E")

#prove((P&Q) >> (Q&P))
#prove(P | ~P)
#prove(((P >> R) | (Q >> R)) >> ((P & Q) >> R))
#prove(((B >> ~A) & ~C & (A >> (B | C))) >> ~A)

a = Sentence("a");a1 = Sentence("a1");a2 = Sentence("a2");a3 = Sentence("a3");a4 = Sentence("a4");
b = Sentence("b");b1 = Sentence("b1");b2 = Sentence("b2");b3 = Sentence("b3");b4 = Sentence("b4");
c = Sentence("c");c1 = Sentence("c1");c2 = Sentence("c2");c3 = Sentence("c3");c4 = Sentence("c4");
d = Sentence("d");d1 = Sentence("d1");d2 = Sentence("d2");d3 = Sentence("d3");d4 = Sentence("d4");
e = Sentence("e");e1 = Sentence("e1");e2 = Sentence("e2");e3 = Sentence("e3");e4 = Sentence("e4");
f = Sentence("f");f1 = Sentence("f1");f2 = Sentence("f2");f3 = Sentence("f3");f4 = Sentence("f4");
g = Sentence("g");g1 = Sentence("g1");g2 = Sentence("g2");g3 = Sentence("g3");g4 = Sentence("g4");
p = Sentence("p");p1 = Sentence("p1");p2 = Sentence("p2");p3 = Sentence("p3");p4 = Sentence("p4");
p5 = Sentence("p5");p6 = Sentence("p6");p7 = Sentence("p7");p8 = Sentence("p8");p9 = Sentence("p9");
p10 = Sentence("p10");p11 = Sentence("p11");p12 = Sentence("p12");p13 = Sentence("p13");p14 = Sentence("p14");
p15 = Sentence("p15");p16 = Sentence("p16");p17 = Sentence("p17");p18 = Sentence("p18");p19 = Sentence("p19");p20 = Sentence("p20");
q = Sentence("q");q1 = Sentence("q1");q2 = Sentence("q2");q3 = Sentence("q3");q4 = Sentence("q4");
r = Sentence("r");r1 = Sentence("r1");r2 = Sentence("r2");r3 = Sentence("r3");r4 = Sentence("r4");
s = Sentence("s");s1 = Sentence("s1");s2 = Sentence("s2");s3 = Sentence("s3");s4 = Sentence("s4");
t = Sentence("t");t1 = Sentence("t1");t2 = Sentence("t2");t3 = Sentence("t3");t4 = Sentence("t4");
u = Sentence("u");u1 = Sentence("u1");u2 = Sentence("u2");u3 = Sentence("u3");u4 = Sentence("u4");
v = Sentence("v");v1 = Sentence("v1");v2 = Sentence("v2");v3 = Sentence("v3");v4 = Sentence("v4");

x11=Sentence("x11");x21=Sentence("x21");x31=Sentence("x31");x12=Sentence("x12");x22=Sentence("x22");x32=Sentence("x32");
