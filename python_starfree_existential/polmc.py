# pip install pysat
# pip install automata_toolkit
# pip install graphviz
# pip install hashlib

from pysat.solvers import Glucose3
from automata_toolkit import regex_to_nfa, visual_utils, nfa_to_dfa, dfa_to_efficient_dfa
import json
import hashlib


from uuid import UUID


class UUIDEncoder(json.JSONEncoder):
    def default(self, obj):
        if isinstance(obj, UUID):
            # if the obj is uuid, we simply return the value of uuid
            return obj.hex
        return json.JSONEncoder.default(self, obj)


# input: regular expression
# output: a corresponding DFA


def autFromReg(e):
    NFA = regex_to_nfa.regex_to_nfa(e)
    DFA = nfa_to_dfa.nfa_to_dfa(NFA)
    return DFA  # dfa_to_efficient_dfa.dfa_to_efficient_dfa(DFA)


# to draw the automaton A
#

def autInitialState(A):
    return A["initial_state"]


def autGetSuccessor(A, state, letter):
    if letter in A["transition_function"][state]:
        return A["transition_function"][state][letter]
    else:
        return "phi"


def autIsFinal(A, state):
    return state in A["final_states"]


def autStates(A):
    return A["states"]


def autFinalStates(A):
    return A["final_states"]


def autShow(A):
    visual_utils.draw_dfa(A, title="")


#
# print(A)


class POLModel:
    worlds = []
    succ = []

    def addWorld(self, exp, val):
        self.worlds.append({"val": val, "exp": exp})
        self.succ.append([])

    def addEdge(self, w, u, a):
        self.succ[w].append({"succ": u, "agent": a})

# input: a string
# output: an ID


class PropDictionnary:
    objs = {}  # id to obj
    dict = {}  # str to id
    nextID = 1

    # input: an object
    # register that object
    # output: the id of that object (an integer)
    def id(self, obj):
        s = json.dumps(obj, cls=UUIDEncoder)
        if(not s in self.dict):
            self.dict[s] = self.nextID
            self.objs[self.nextID] = obj
            self.nextID = self.nextID + 1

        return self.dict[s]

    #input: id
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

    # it returns a valuation that satisfies the set of constraints
    def get_model(self):
        self.g.solve()
        return list(filter(lambda o: o != None, map(lambda id: self.d.getProp(id), self.g.get_model())))

    def addClause(self, clause):
       # print(len(clause.posProp))
       # print([self.d.id(p) for p in clause.posProp] + [-self.d.id(p) for p in clause.negProp])
        self.g.add_clause([self.d.id(p) for p in clause.posProp] +
                          [-self.d.id(p) for p in clause.negProp])


class Clause:
    def __init__(self):
        self.posProp = []
        self.negProp = []

    def addPos(self, prop):
        self.posProp.append(prop)

    def addNeg(self, prop):
        self.negProp.append(prop)


M = POLModel()
M.addWorld("(ab)*", ["p"])
M.addWorld("(a)*", ["q"])
M.addEdge(0, 1, "a")
M.addEdge(0, 0, "a")


phi = ["K", "a", "p"]

alphabet = ["a", "b"]

solver = Solver()

# surv
#input: automaton
#        idA id of the automaton
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

    solver.addExist([{"type": "a", "automaton": idA, "t": k, "q": q}
                    for q in autFinalStates(A)])


# def test2():
#     solver.addProp({"type": "t", "w": 0, "phi": phi})

#     k = 4
#     # GuessWord
#     for t in range(k):
#         solver.addExistUnique([{"type": "p", "t": t, "a": a} for a in alphabet])

#     A = autFromReg("(ab)*")
#     surv(A, "A", k)

#     print(solver.get_model())

# def test0():
#     solver.addProp("a")
#     print(solver.get_model())


def test1():
    k = 2
    # GuessWord
    for t in range(k):
        solver.addExistUnique([{"type": "p", "t": t, "a": a}
                              for a in alphabet])

    A = autFromReg("(ab)*")
    B = autFromReg("a*b*")
    #autShow(A)
    surv(A, "A", k)
    surv(B, "B", k)
    print(solver.get_model())


test1()
