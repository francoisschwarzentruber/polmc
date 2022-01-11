const regParser = require('automata.js');
/**
 * TODO: handle prefixes
 */


function coReachable(dfa) {
   const visited = {};
   const 
}

/**
 * 
 * @param {*} regularExpression 
 * @returns a DFA whose language is the same than the one described by regularExpression
 */
function constructDFA(regularExpression) {
   const parser = new regParser.RegParser(regularExpression);
   return parser.parseToDFA();
}

/**
 * 
 * @param {*} dfa 
 * @param {*} word 
 * @returns true if word is accepted by the dfa
 */
function accept(dfa, word) {
   console.log(word)
   if (word == "")
      return true;
   let q = dfa.initialState;
   console.log(dfa)

   console.log("start in " + q);
   for (let i = 0; i < word.length; i++) {
      let symbol = word[i];
      let nextq = undefined;
      for (let r in dfa.transitions[q]) {
         console.log(r)
         if (dfa.transitions[q][r] == symbol) {
            nextq = r;
            console.log(r);
            break;
         }
      }
      if (nextq)
         q = nextq;
      else
         return false;

   }
   return (dfa.acceptStates.indexOf(q) >= 0);
}



class POLModel {
   worlds = [];
   succs = [];
   obs = "";

   addWorld(regularExpression, val) {
      const dfa = constructDFA(regularExpression);
      console.log(dfa);
      this.worlds.push({ exp: dfa, state: dfa.initialState, valuation: val });
      this.succs.push([]);
   }

   addEdge(w, u, a) { this.succs[w].push({ succ: u, agent: a }); }


   mc(w, phi) {
      if (typeof (phi) == "string")
         return this.worlds[w].valuation.indexOf(phi) > -1;
      else if (phi[0] == "!")
         return this.mc(w, phi[1]);
      else if (phi[1] == "&")
         return this.mc(w, phi[0]) && this.mc(w, phi[2]);
      else if (phi[1] == "|")
         return this.mc(w, phi[0]) || this.mc(w, phi[2]);
      else if (phi[0] == "K") {
         for (const edge of this.succs[w]) {
            if (accept(this.worlds[edge.succ].exp, this.obs))
               if (edge.agent == phi[1])
                  if (!this.mc(edge.succ, phi[2]))
                     return false;
         }
         return true;
      }
      else if (phi[0] == "obs") {
         const beforeWord = this.obs;
         this.obs = this.obs + phi[1];
         const b = this.mc(w, phi[2]);
         this.word = beforeWord;
         return b;
      }
      throw "syntax error";
   }

}


const M = new POLModel();
M.addWorld("ba*", ["p"]);
M.addWorld("b*", ["p"]);
M.addWorld("a*", []);
M.addEdge(0, 1, "i");
M.addEdge(0, 2, "i");
M.addEdge(0, 2, "j");

console.log(M.mc(0, [["obs", "b", ["K", "i", "p"]], "&", ["!", ["K", "i", "p"]]]));

