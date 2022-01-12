# pip install pysat
# pip install automata-lib
# pip install graphviz
# pip install hashlib

from pysat.solvers import Glucose3
from automata.fa.dfa import DFA
import json
import hashlib
import time

start = time.time()


######################################
# DFAs for the example

dfaSeq3 = DFA(
    states={'q0', 'q1', 'q2', 'q3', 'phi'},
    input_symbols={'u', 'l', 'r', 'd'},
    transitions={
        'q0': {'u': 'q1', 'l': 'q1', 'r': 'q1', 'd': 'q1'},
        'q1': {'u': 'q2', 'l': 'q2', 'r': 'q2', 'd': 'q2'},
        'q2': {'u': 'q3', 'l': 'q3', 'r': 'q3', 'd': 'q3'},
        'q3': {'u': 'phi', 'l': 'phi', 'r': 'phi', 'd': 'phi'},
        'phi': {'u': 'phi', 'l': 'phi', 'r': 'phi', 'd': 'phi'},
    },
    initial_state='q0',
    final_states={'q3'}
)


dfaSeq4 = DFA(
    states={'q0', 'q1', 'q2', 'q3', 'q4', 'phi'},
    input_symbols={'u', 'l', 'r', 'd'},
    transitions={
        'q0': {'u': 'q1', 'l': 'q1', 'r': 'q1', 'd': 'q1'},
        'q1': {'u': 'q2', 'l': 'q2', 'r': 'q2', 'd': 'q2'},
        'q2': {'u': 'q3', 'l': 'q3', 'r': 'q3', 'd': 'q3'},
        'q3': {'u': 'q4', 'l': 'q4', 'r': 'q4', 'd': 'q4'},
        'q4': {'u': 'phi', 'l': 'phi', 'r': 'phi', 'd': 'phi'},
        'phi': {'u': 'phi', 'l': 'phi', 'r': 'phi', 'd': 'phi'},
    },
    initial_state='q0',
    final_states={'q4'}
)

dfaSeqWater = DFA(
    states={'q0', 'q1', 'phi'},
    input_symbols={'u', 'l', 'r', 'd'},
    transitions={
        'q0': {'u': 'q0', 'l': 'q1', 'r': 'q0', 'd': 'q1'},
        'q1': {'u': 'q1', 'l': 'phi', 'r': 'q1', 'd': 'phi'},
        'phi': {'u': 'phi', 'l': 'phi', 'r': 'phi', 'd': 'phi'},
    },
    initial_state='q0',
    final_states={'q1'}
)

dfaSeqPower = DFA(
    states={'q0', 'q1', 'phi'},
    input_symbols={'u', 'l', 'r', 'd'},
    transitions={
        'q0': {'l': 'q0', 'u': 'q1', 'd': 'q0', 'r': 'q1'},
        'q1': {'l': 'q1', 'u': 'phi', 'd': 'q1', 'r': 'phi'},
        'phi': {'u': 'phi', 'l': 'phi', 'r': 'phi', 'd': 'phi'},
    },
    initial_state='q0',
    final_states={'q1'}
)

dfaSeqPatrol = DFA(
    states={'q0', 'q1', 'q2', 'q3', 'q4', 'phi'},
    input_symbols={'u', 'l', 'r', 'd'},
    transitions={
        'q0': {'u': 'phi', 'l': 'phi', 'r': 'q1', 'd': 'phi'},
        'q1': {'u': 'phi', 'l': 'phi', 'r': 'q1', 'd': 'q2'},
        'q2': {'u': 'phi', 'l': 'q3', 'r': 'phi', 'd': 'q2'},
        'q3': {'u': 'q4', 'l': 'q3', 'r': 'phi', 'd': 'phi'},
        'q4': {'u': 'q4', 'l': 'phi', 'r': 'q1', 'd': 'phi'},
        'phi': {'u': 'phi', 'l': 'phi', 'r': 'phi', 'd': 'phi'},
    },
    initial_state='q0',
    final_states={'q0', 'q1', 'q2', 'q3', 'q4'}
)


# automata functions

def autInitialState(A):
    return A.initial_state


def autGetSuccessor(A, state, letter):
    if letter in A.transitions[state]:
        return A.transitions[state][letter]
    else:
        return "phi"


def autIsFinal(A, state):
    return state in A.final_states


def autStates(A):
    return A.states


def autFinalStates(A):
    return A.final_states


# not used yet
class POLModel:
    worlds = []
    succ = []

    def addWorld(self, exp, val):
        self.worlds.append({"val": val, "exp": exp})
        self.succ.append([])

    def addEdge(self, w, u, a):
        self.succ[w].append({"succ": u, "agent": a})


# dictionnary of propositional variables
class PropDictionnary:
    objs = {}  # id to obj
    dict = {}  # str to id
    nextID = 1

    # input: an object
    # register that object
    # output: the id of that object (an integer)
    def id(self, obj):
        s = json.dumps(obj)
        if(not s in self.dict):
            self.dict[s] = self.nextID
            self.objs[self.nextID] = obj
            self.nextID = self.nextID + 1

        return self.dict[s]

    # input: id
    # output: the object corresponding to that id
    def getProp(self, id):
        return self.objs.get(id)


class Solver:
    g = Glucose3()
    d = PropDictionnary()

    def addExist(self, PROP):
        # [2, 5, 6, 9]  at least one is true
        self.g.add_clause([self.d.id(p) for p in PROP])

    # add the constraint that exactly one proposition in PROP is true
    def addExistUnique(self, PROP):
        # [2, 5, 6, 9]  at least one is true
        self.g.add_clause([self.d.id(p) for p in PROP])
        for p in PROP:
            for q in PROP:
                if(p != q):
                    # [-2, -5] both cannot be true at the same time
                    self.g.add_clause([-self.d.id(p), -self.d.id(q)])

    # we say that that propositin prop

    def addProp(self, prop):
        self.g.add_clause([self.d.id(prop)])

    def addNegProp(self, prop):
        self.g.add_clause([-self.d.id(prop)])

    # it returns a valuation that satisfies the set of constraints
    def get_model(self):
        try:
            self.g.solve()
            return list(filter(lambda o: o != None, map(lambda id: self.d.getProp(id), self.g.get_model())))
        except TypeError:
            return None

    def addClause(self, clause):
       # print(len(clause.posProp))
       # print([self.d.id(p) for p in clause.posProp] + [-self.d.id(p) for p in clause.negProp])
        self.g.add_clause([self.d.id(p) for p in clause.posProp] +
                          [-self.d.id(p) for p in clause.negProp])


# a clause of litterals
class Clause:
    def __init__(self):
        self.posProp = []
        self.negProp = []

    def addPos(self, prop):
        self.posProp.append(prop)

    def addNeg(self, prop):
        self.negProp.append(prop)


M = POLModel()
M.addWorld("water", ["water"])
M.addWorld("power", ["power"])
M.addWorld("patrol", ["patrol"])
M.addEdge(0, 1, "a")
M.addEdge(1, 0, "a")
M.addEdge(1, 2, "a")
M.addEdge(2, 1, "a")
M.addEdge(2, 0, "a")
M.addEdge(0, 2, "a")
M.addEdge(0, 1, "b")
M.addEdge(1, 0, "b")


alphabet = ["l", "u", 'd', 'r']

solver = Solver()

# surv
# input: A = automaton
#        idA = id of the automaton, a string that tags the automaton
#        k length of the guessed word
# effect: add to the solver the constraint of the execution of the guessed word in automaton A
#        => proposition {"type": "s", "automaton": idA} is true iff the word is accepted by A
#


def surv(A, idA, k):
    solver.addProp({"type": "a", "automaton": idA,
                   "t": 0, "q": autInitialState(A)})

    for t in range(k+1):
        solver.addExistUnique(
            [{"type": "a", "automaton": idA, "t": t, "q": q} for q in autStates(A)])

    for t in range(k):
        for a in alphabet:
            for q in autStates(A):
                c = Clause()
                c.addNeg({"type": "a", "automaton": idA, "t": t, "q": q})
                c.addNeg({"type": "p", "t": t, "a": a})
                # it is deterministic contrary to the paper
                c.addPos({"type": "a", "automaton": idA, "t": t +
                         1, "q": autGetSuccessor(A, q, a)})
                solver.addClause(c)
                # rules

    c = Clause()
    for q in autFinalStates(A):
        c.addPos({"type": "a", "automaton": idA, "t": k, "q": q})
        c.addNeg({"type": "s", "automaton": idA})
    solver.addClause(c)

    for q in autFinalStates(A):
        c = Clause()
        c.addNeg({"type": "a", "automaton": idA, "t": k, "q": q})
        c.addPos({"type": "s", "automaton": idA})
        solver.addClause(c)


def tseitinWorld(iw, phi):
    if isinstance(phi, str):
        print("prop!")
        if(phi in M.worlds[iw]["val"]):
            solver.addProp({"type": "t", "world": iw, "formula": phi})
        else:
            print("false")
            solver.addNegProp({"type": "t", "world": iw, "formula": phi})
    elif phi[0] == "not":
        c = Clause()
        c.addPos({"type": "t", "world": iw, "formula": phi})
        c.addPos({"type": "t", "world": iw, "formula": phi[1]})
        solver.addClause(c)
        c2 = Clause()
        c2.addNeg({"type": "t", "world": iw, "formula": phi})
        c2.addNeg({"type": "t", "world": iw, "formula": phi[1]})
        solver.addClause(c2)
    elif phi[0] == "and":
        c = Clause()
        c.addNeg({"type": "t", "world": iw, "formula": phi})
        c.addPos({"type": "t", "world": iw, "formula": phi[1]})
        solver.addClause(c)
        c2 = Clause()
        c2.addNeg({"type": "t", "world": iw, "formula": phi})
        c2.addPos({"type": "t", "world": iw, "formula": phi[2]})
        solver.addClause(c2)
        c3 = Clause()
        c3.addNeg({"type": "t", "world": iw, "formula": phi[1]})
        c3.addNeg({"type": "t", "world": iw, "formula": phi[2]})
        c3.addPos({"type": "t", "world": iw, "formula": phi})
        solver.addClause(c3)
    elif phi[0] == "K":
        agent = phi[1]

        for transition in M.succ[iw]:
            if transition["agent"] == agent:
                iu = transition["succ"]
                c = Clause()
                c.addNeg({"type": "t", "world": iw, "formula": phi})
                c.addNeg({"type": "s", "automaton": M.worlds[iu]["exp"]})
                c.addPos({"type": "t", "world": iu, "formula": phi[2]})
                solver.addClause(c)

        c = Clause()

        for transition in M.succ[iw]:
            if transition["agent"] == agent:
                iu = transition["succ"]
                c.addPos({"type": "p", "world": iu, "formula": phi[2]})

                d = Clause()
                d.addPos({"type": "p", "world": iu, "formula": phi[2]})
                d.addPos({"type": "t", "world": iu, "formula": phi[2]})
                d.addNeg({"type": "s", "automaton": M.worlds[iu]["exp"]})

                solver.addClause(d)

                e = Clause()
                e.addNeg({"type": "p", "world": iu, "formula": phi[2]})
                e.addPos({"type": "s", "automaton": M.worlds[iu]["exp"]})
                solver.addClause(e)

                e = Clause()
                e.addNeg({"type": "p", "world": iu, "formula": phi[2]})
                e.addNeg({"type": "t", "world": iu, "formula": phi[2]})
                solver.addClause(e)

        c.addPos({"type": "t", "world": iw, "formula": phi})

        solver.addClause(c)


def tseitin(phi):
    for iw in range(len(M.worlds)):
        tseitinWorld(iw, phi)

    if isinstance(phi, str):
        return
    elif phi[0] == "not":
        tseitin(phi[1])
    elif phi[0] == "and":
        tseitin(phi[1])
        tseitin(phi[2])
    elif phi[0] == "K":
        tseitin(phi[2])


def mcExample3():
    k = 4
    # GuessWord: the guessed word of size k is uniquely determined
    for t in range(k):
        solver.addExistUnique([{"type": "p", "t": t, "a": a}
                              for a in alphabet])

    # encodings of the readings of the guessed word for all the automata
    surv(dfaSeq4, "seq4", k)
    surv(dfaSeqPatrol, "patrol", k)
    surv(dfaSeqPower, "power", k)
    surv(dfaSeqWater, "water", k)

    #phi = "azeaze"
    phi = ["and", ["K", "b", "water"], ["not", ["K", "a", ["not", "patrol"]]]]

    solver.addProp({"type": "t", "world": 0, "formula": phi})

    tseitin(phi)
    solver.addProp({"type": "s", "automaton": "seq4"})  # pi
    solver.addProp({"type": "s", "automaton": "water"})  # water should survive
    # patrol should survive
    solver.addProp({"type": "s", "automaton": "patrol"})
    solver.addNegProp({"type": "s", "automaton": "power"}
                      )  # power should not survive
    print(solver.get_model())


def mcExample4():
    k = 3
    # GuessWord: the guessed word of size k is uniquely determined
    for t in range(k):
        solver.addExistUnique([{"type": "p", "t": t, "a": a}
                              for a in alphabet])

    # encodings of the readings of the guessed word for all the automata
    surv(dfaSeq3, "seq3", k)
    surv(dfaSeqPatrol, "patrol", k)
    surv(dfaSeqPower, "power", k)
    surv(dfaSeqWater, "water", k)

    solver.addProp({"type": "s", "automaton": "seq3"})  # pi
    solver.addProp({"type": "s", "automaton": "water"})  # water should survive
    solver.addNegProp({"type": "s", "automaton": "patrol"}
                      )  # patrol should not survive
    solver.addNegProp({"type": "s", "automaton": "power"}
                      )  # power should not survive
    print(solver.get_model())


mcExample3()

end = time.time()
print("Time elapsed: ", end - start, "ms")
