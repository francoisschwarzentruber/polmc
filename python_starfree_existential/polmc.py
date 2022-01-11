from pysat.solvers import Glucose3
from automata_toolkit import regex_to_nfa, visual_utils, nfa_to_dfa, dfa_to_efficient_dfa
import json
import hashlib

def regex_to_dfa(e):
    NFA = regex_to_nfa.regex_to_nfa("(ab)*")
    DFA = nfa_to_dfa.nfa_to_dfa(NFA)
    return dfa_to_efficient_dfa.dfa_to_efficient_dfa(DFA)


A = regex_to_dfa("(ab)*")
#visual_utils.draw_dfa(A, title="")
print(A)


class POLModel:
    worlds = []
    succ = []

    def addWorld(self, exp, val):
        self.worlds.append({"val": val, "exp": exp})
        self.succ.append([])

    def addEdge(self, w, u, a):
        self.succ[w].append({"succ": u, "agent": a})


def strToInt(str):
    return int(hashlib.md5("aze".encode('utf-8')).hexdigest(), 16)%10000

class PropDictionnary:
    objs = {}

    def id(self, obj):
        id = strToInt(json.dumps(obj))
        self.objs[id] = obj
        return id

    def getProp(self, id):
        return self.objs.get(id)


class Solver:
    g = Glucose3()
    d = PropDictionnary()

    def addExistUnique(self,PROP):
        self.g.add_clause([self.d.id(p) for p in PROP])
        for p in PROP:
            for q in PROP:
                if(p != q)
        self.g.add_clause([-self.d.id(p), -self.d.id(q)])

    def addProp(self, prop):
        self.g.add_clause([self.d.id(prop)])


    def get_model(self):
        self.g.solve()
        return list(filter(lambda o: o!=None, map(lambda id : self.d.getProp(id), self.g.get_model())))




M = POLModel()
M.addWorld("(ab)*", ["p"])
M.addWorld("(a)*", ["q"])
M.addEdge(0, 1, "a")
M.addEdge(0, 0, "a")


phi = ["K", "a", "p"]

alphabet = ["a", "b"]

solver = Solver()
solver.addProp({"type":"t", "w":0, "phi":phi})

#add GuessWord
for t in range(5):
    solver.addExistUnique([{"type":"p", "t":t, "a": a} for a in alphabet])













print(solver.get_model())






