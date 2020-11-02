from start import *
from random import randint

def randPol():
    """Returns either -1 or 1"""
    return 1-randint(0,1)*2

class Polarized:
    """A formula with polarity"""

    def __init__(self, seq, *args):
        """Polarize a sequent"""
        
        self.polarize(seq, *args)

    def polarize(self, seq, *args):
        if len(args) > 0:
            self.pol = args[0]
        else:
            self.pol = randPol()     #choose randomly

        dontFlip = False
        if len(args) > 1:
            dontFlip = args[1]
            
        if seq.atom:
            assert seq != Name.F    #can't deal with true/false literals for now
            self.atom = True
            self.id = seq.id

        else:
            self.atom = False
            assert seq.op != Name.NOT   #can't deal with NOT for now
            if seq.op == Name.OR:
                if self.pol == -1:
                    self.op = PName.UP
                    self.left = Polarized(seq, 1)
                else:
                    self.op = PName.OR
                    self.left = Polarized(seq.left, 1)
                    self.right = Polarized(seq.right, 1)

            elif seq.op == Name.AND:
                if dontFlip:    #Already randomly chosen which AND to use from parent
                    if self.pol == -1:
                        self.op = PName.NAND
                        self.left = Polarized(seq.left, -1, False)
                        self.right = Polarized(seq.right, -1, False)
                    elif self.pol == 1:
                        self.op = PName.PAND
                        self.left = Polarized(seq.left, 1, False)
                        self.right = Polarized(seq.right, 1, False)
                else:
                    use = randPol()
                    if use == -1:
                        if self.pol == 1:
                            self.op = PName.DOWN
                            self.left = Polarized(seq, -1, True)
                        elif self.pol == -1:
                            self.op = PName.NAND
                            self.left = Polarized(seq.left, -1, False)
                            self.right = Polarized(seq.right, -1, False)

                    elif use == 1:
                        if self.pol == -1:
                            self.op = PName.UP
                            self.left = Polarized(seq, 1, True)
                        elif self.pol == 1:
                            self.op = PName.PAND
                            self.left = Polarized(seq.left, 1, False)
                            self.right = Polarized(seq.right, 1, False)

            elif seq.op == Name.IMP:
                if self.pol == 1:
                    self.op = PName.DOWN
                    self.left = Polarized(seq, -1)
                elif self.pol == -1:
                    self.op = PName.IMP
                    self.left = Polarized(seq.left, 1)
                    self.right = Polarized(seq.right, -1)
                    
    def __str__(self):
        if self.atom:
            return str(self.id) + (PName.P if self.pol>0 else PName.N)

        if self.op == PName.DOWN:
            return PName.DOWN + str(self.left)

        if self.op == PName.UP:
            return PName.UP + str(self.left)

        else:
            return "("+str(self.left)+" "+str(self.op)+" "+str(self.right)+")"

                    

class PName:
    PAND = "⊗"
    NAND = "&"
    OR = "⊕"
    IMP = "⊃"
    P = "+"
    N = "-"
    DOWN = "↓"
    UP = "↑"
