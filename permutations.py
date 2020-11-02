from start import *
import time
from matplotlib import pyplot
import random

def andCompose(*args):
    """Composes a list of sentences with &"""
    if len(args) == 1:
        return andCompose(args[0][0], args[0][1:])

    if len(args[1]) > 0:
        return andCompose((args[0] | args[1][0]), args[1][1:])
    else:
        return args[0]


def reverseTest(n, trials):
    atoms = [Sentence("P" + str(i)) for i in range(1, n+1)]
    start = time.time()
    tot_size = 0
    for trial in range(trials):
        ptn = prove(andCompose(atoms) >> andCompose(atoms[::-1]), verbose=False)
        tot_size += ptn.getSize()
    elapsed = int(1000*(time.time() - start))
    
    print("{}\t{}\t{}".format(n, tot_size/trials, elapsed/trials))

    return n, tot_size/trials, elapsed/trials

def randPermTest(n, trials):
    atoms = [Sentence("P" + str(i)) for i in range(1, n+1)]
    start = time.time()
    tot_size = 0
    for trial in range(trials):
        ptn = prove(andCompose(atoms) >> andCompose(random.sample(atoms, n)), verbose=False)
        tot_size += ptn.getSize()
    elapsed = int(1000*(time.time() - start))
    
    print("{}\t{}\t{}".format(n, tot_size/trials, elapsed/trials))

    return n, tot_size/trials, elapsed/trials

reverse = []
rand = []
for i in range(1, 20):
    reverse.append(reverseTest(i, 25))
    rand.append(randPermTest(i, 25))

size = pyplot.figure(1)
pyplot.title("Size of proof tree")
pyplot.plot([f[0] for f in reverse], [f[1] for f in reverse], [f[0] for f in rand], [f[1] for f in rand])
size.show()

runtime = pyplot.figure(2)
pyplot.title("Runtime of proof")
pyplot.plot([f[0] for f in reverse], [f[2] for f in reverse], [f[0] for f in rand], [f[2] for f in rand])
runtime.show()
