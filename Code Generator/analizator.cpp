#include<bits/stdc++.h>
#include "utils.h"
#define breturn return
using namespace std;
struct Scope {
    map<string, string> declarations;
    set<string> defintions;
    string returnType;
    int layersOfLoops = 0;
    Scope *parentScope;
    map<string, int>varAddress;
    int stackBytes = 0;
    int stackSizeBeforeParameters = 0;
    string breakAddress;
    string continueAddress;
};
Scope *globalScope = new Scope();
vector<pair<string, string> > allDeclaredFunctions;
int biggestAddress = 131072;






// nacin za lakse obilaziti sintaksno stablo

struct SyntaxNode {
    string name;
    string lexname;
    int rownumber;
    string val;
    SyntaxNode(string name) : name(name) {
        if(name[0] != '<') {
            int id = name.find(' ');
            lexname = name.substr(0, id++);
            int nex = name.find(' ', id);
            rownumber = stoi(name.substr(id, nex - id));
            val = name.substr(nex + 1);
            this->name = lexname;
        }
    } 

    vector<SyntaxNode*> production;
    friend ostream& operator << (ostream& os, const SyntaxNode& obj)
    {
        if(obj.name[0] == '<') os << obj.name;
        else os << obj.name << "(" << obj.rownumber << "," << obj.val << ")";
        return os;
    }
};

vector<string>assem;

// generiranje strukture sintaksnog stabla iz inputa

void readline(SyntaxNode *(&startNode)) {
    string s;
    vector<string> tempV;
    while(getline(cin, s)) tempV.push_back(s);
    vector<pair<SyntaxNode*, int> > treeBuilder = {{nullptr, -1}};
    for(auto t:tempV) {
        int depth = 0;
        while(t[depth++] == ' ');
        string syntaxName = t.substr(depth - 1);
        while(treeBuilder.back().second >= depth) treeBuilder.pop_back();
        SyntaxNode *currentNode = new SyntaxNode(syntaxName);
        if(treeBuilder.back().first != nullptr) treeBuilder.back().first->production.push_back(currentNode);
        else startNode = currentNode, treeBuilder[0].first = currentNode;
        treeBuilder.push_back({currentNode, depth});
    }
}


void error(SyntaxNode* currentNode) {
    cout << *currentNode << " ::= ";
    for(int i = 0; i < (int)currentNode->production.size(); i++) cout << *currentNode->production[i] << (i + 1 != (int)currentNode->production.size() ? " ":"");
    exit(0);
}


// funkcija za parsirati niz a,b,c,d -> {a, b, c, d}

void parseListaParametaraRet(string s, vector<string> &v) {
    s += ',';
    int id = 0;
    while(id < (int)s.size()) {
        int nex = s.find(',', id);
        v.push_back(s.substr(id, nex - id));
        id = nex + 1;
    }
}

// funkcija koja gleda je li char ok definiran po pravilima iz 4.3.2
bool isCharOk (string c) {
   //cout << c.size() << " " << c << endl;
   // classic single char
   if (c.size() == 3) return (c[0] == '\'' && c[2] == '\'');

   // TODO: provjeriti je li ok
   vector<string>goods = {"'\\t'", "'\\n'", "'\\0'", "'\\'\'", "'\\\"'", "'\\\\'"};
   for (int i = 0; i < (int)goods.size(); i++) {
      //cout << goods[i] << endl;
      if (goods[i] == c) return true;
   }
   return false;
}

// za niz znakova
bool isStringOk (string s) {
   for (int i = 1; i < (int)s.size()-1; i++) {
      bool res = true;
      if (s[i] == '\\') {
         if (i == (int)s.size()-2) return false;
         string h = "'";
         h += s[i];
         h += s[i+1];
         h += "'";
         res = isCharOk(h);
         i++;
      }
      else {
         string h = "'";
         res = isCharOk(h+s[i]+h);
      }
      if (!res) return false;
   }
   return true;
}

// funkcija koja gleda moze li se a castati u b
bool canCast (string a, string b) {
   set<pair<string, string> > castingPairs;
   castingPairs.insert({"const(int)", "int"});
   castingPairs.insert({"const(char)", "char"});
   castingPairs.insert({"int", "const(int)"});
   castingPairs.insert({"char", "const(char)"});
   castingPairs.insert({"char", "int"});
   castingPairs.insert({"niz(int)", "niz(const(int))"});
   castingPairs.insert({"niz(char)", "niz(const(char))"});

   return (a == b || castingPairs.count({a, b}) != 0);
}

bool isT (string a) {
   return (a == "int" || a == "char");
}

bool isX (string a) {
   return (isT(a) || a == "const(int)" || a == "const(char)");
}

bool whichScope(Scope* (&runner), string &name) {
    while (runner != nullptr) {
        if (runner->declarations.find(name) != runner->declarations.end()) break;
        runner = runner->parentScope;
    }
    return (runner == globalScope);
}


vector<string> provjeri(SyntaxNode *currentNode, Scope *currentScope, vector<string> params);

// funkcija za sve one slicne binarne izraze

vector<string> binarniIzraz (SyntaxNode* c, vector<SyntaxNode*> &p, Scope* currentScope) {
   vector<string> retValue;
   retValue = provjeri(p[0], currentScope, {});

   string lijevi_izraz_tip = retValue[0];
   if (!canCast(lijevi_izraz_tip, "int")) error(c);
   
   pushToStackFrom("R6", ",");

   retValue = provjeri(p[2], currentScope, {});

   string desni_izraz_tip = retValue[0];
   if (!canCast(desni_izraz_tip, "int")) error(c);

   
   pushToStackFrom("R6", ",");
   return {"int", "0"};
}

vector<string> logIzraz (SyntaxNode* c, vector<SyntaxNode*> &p, Scope* currentScope, string op) {
    vector<string> retValue;
    retValue = provjeri(p[0], currentScope, {});
    string labelName = "i";
    reserveLabel(labelName);
    
    string lijevi_izraz_tip = retValue[0];
    if (!canCast(lijevi_izraz_tip, "int")) error(c);
    isFalse("R6");
    if(op == "OP_I") conditionoalJumpLink(labelName);
    else if(op == "OP_ILI") conditionoalJumpLink(labelName, "NE");
    retValue = provjeri(p[2], currentScope, {});

    string desni_izraz_tip = retValue[0];
    if (!canCast(desni_izraz_tip, "int")) error(c);
    putLabel("int", -1, labelName, true);
    isFalse("R6");
    skipOperatorNext("EQ");
    fillReg("1", "R6");
    return {"int", "0"};
}



void addReturn(Scope* currentScope, Scope* runner, bool lastChance = false) {
   Scope* runner2 = currentScope;
   int cleanerBytes = runner2->stackBytes; 
   int stackSize = st.size() - cleanerBytes;
   int deleted = 0;
   if(!lastChance) {
    while (runner2 != runner) {
            while (cleanerBytes) {
                cleanerBytes--;
                stackSize--;
                deleted++;
                code.push_back("\t\tPOP R0");
            }
            runner2 = runner2->parentScope;
            cleanerBytes = runner2->stackBytes;

    }
   }
   // kada smo u scopeu funkcije (stack_cleaner == runner),
   // moramo ocistiti lokalne varijable tog scopea
   while (stackSize != runner->stackSizeBeforeParameters) {
         stackSize--;
         deleted++;
         code.push_back("\t\tPOP R0");
   }
   if(lastChance) for(int i = 0; i < deleted; i++) st.pop_back();
   code.push_back("\t\tRET");
}

// funkcija provjeri kao u labosu opisana, prvo je trenutno koje pravilo projveravamo, drugi parametar
// koji je trenutni djelokrug, a zadnji parametar su nasljedna svojstva, povratni parametar je niz izvedenih svojstava



vector<string> provjeri(SyntaxNode *currentNode, Scope *currentScope, vector<string> params = {}) {
    SyntaxNode *&c = currentNode;
    vector<SyntaxNode*> &p = c->production;
    // cout << "Provjera " << c->name << " -> ";
    // for(auto t:p) cout << *t << " ";
    // cout << '\n'; 
    // printSt();
    vector<string> retValue;
    if(c->name == "<primarni_izraz>") {
        if (p[0]->lexname == "IDN") {
            // trazenje scopea u kojem je deklarirana varijabla
            Scope* runner = currentScope;
            bool foundDeclaration = false;
            while (runner != nullptr) {
               if (runner->declarations.count(p[0]->val) != 0) {
                  foundDeclaration = true;
                  break;
               }
               runner = runner->parentScope;
            }
            // nije deklarirano IDN.ime
            if (!foundDeclaration) error(c);
            
            string tip = runner->declarations[p[0]->val];
            // "jedino IDN moze biti l-izraz i to samo ako predstavlja varijablu brojevnog tipa 
            // (char ili int) bez const-kvalifkatora"
            // TODO: ovako?
            string lizraz = (tip == "char" || tip == "int") ? "1" : "0";
            if (runner == globalScope) {
                loadToFromStatic ("R6", runner->varAddress[p[0]->val]); // u r6 s ove staticke adrese   
            }
            else {
                int off = getOffFromStackTop(p[0]->val);
                loadToFromStack ("R6", off);
            }
            return {tip, lizraz, p[0]->val};
        }
        if (p[0]->lexname == "BROJ") {
            string tip = "int";
            string lizraz = "0";

            // provjera je li vrijednost u rasponu inta
            long long int numVal = 0;
            int st = 0;
            if (p[0]->val[0] == '-') st = 1;

            for (int i = st; i < (int)p[0]->val.size(); i++) {
               numVal = 10 * numVal + (p[0]->val[i] - '0');
            }
            if (st == 1) numVal *= (-1);

            long long int minVal = -((long long int)1 << 31);
            long long int maxVal = ((long long int)1 << 31) - 1;

            if (!(minVal <= numVal && numVal <= maxVal)) error(c);

            int constAddress = 0;
            // spremi konstantu i dobij gdje je spremljena
            storeConst("int", numVal, constAddress);
            // zapisi konstantu u r6
            loadToFromStatic("R6", constAddress);
            return {tip, lizraz};
        }
        if (p[0]->lexname == "ZNAK") {
            string tip = "char";
            string lizraz = "0";

            if (!isCharOk(p[0]->val)) error(c);

            int constAddress = 0;
            storeConst("int", p[0]->val[1], constAddress); // TODO: OVO NIJE DOBROOOOOOOOOOOOOOOOOOOOOOOOOOOOOO (kako npr. ascii od \t)
            loadToFromStatic("R6", constAddress);
            return {tip, lizraz};
        }
        if (p[0]->lexname == "NIZ_ZNAKOVA") {
            string tip = "niz(const(char))";
            string lizraz = "0";
            loadToFromStack("R0", 0);
            if (!isStringOk(p[0]->val)) error(c);
            string op = "";
            if(currentScope == globalScope) op = "ADD";
            else op = "SUB";
            for(int i = 1; i < (int)(p[0]->val.size()) - 1; i++) {
                int constAddress = 0;
                storeConst("int", p[0]->val[i], constAddress);
                loadToFromStatic("R6", constAddress);
                storeFromToReg("R6", "R0");
                operatorGeneric(op, "R0", "4", "R0");
            }
            fillReg("0", "R6");
            storeFromToReg("R6", "R0");
            return {tip, lizraz};
        }
        if (p[0]->lexname == "L_ZAGRADA") {
            string tip = "", lizraz = "";

            retValue = provjeri(p[1], currentScope);

            string izraz_tip = retValue[0];
            string izraz_lizraz = retValue[1];

            tip = izraz_tip;
            lizraz = izraz_lizraz;

            return {tip, lizraz};
        }
    } else if(c->name == "<postfiks_izraz>") {    
        if (p[0]->name == "<primarni_izraz>") {
            string tip = "", lizraz = "";

            retValue = provjeri(p[0], currentScope);
            string izraz_tip = retValue[0];
            string izraz_lizraz = retValue[1];
            tip = izraz_tip;
            lizraz = izraz_lizraz;

            if (retValue.size() >= 3) return {tip, lizraz, retValue[2]};
            else return {tip, lizraz};
        } 
        if (p[1]->lexname == "L_UGL_ZAGRADA") {
            retValue = provjeri(p[0], currentScope);

            string postfiks_izraz_tip = retValue[0];
            string idn_ime = retValue[2];
            
            // provjeri je li postfiks.tip oblix niz(X)
            if (postfiks_izraz_tip.substr(0, 4) != "niz(" 
               || postfiks_izraz_tip[postfiks_izraz_tip.size()-1] != ')'
               || !isX(postfiks_izraz_tip.substr(4, postfiks_izraz_tip.size()-5))) {
                  error(c);
               }
            
            string X = postfiks_izraz_tip.substr(4, postfiks_izraz_tip.size()-5);

            retValue = provjeri(p[2], currentScope);
            pushToStackFrom("R6", "offset");
            string izraz_tip = retValue[0];

            // provjeri vrijedi li izraz.tip ~ int
            if (!canCast(izraz_tip, "int")) error(c);
            string tip = X;
            string lizraz = isT(X) ? "1" : "0";
            Scope* runner = currentScope;
            whichScope(runner, idn_ime);
            if(runner == globalScope) {
                loadToFromStatic("R0", runner->varAddress[idn_ime]);
                operatorGeneric("ADD", "R0", "4", "R0");
                operatorGeneric("SHL", "R6", "2", "R6");
                operatorGeneric("ADD", "R0", "R6", "R0");
            } else {
                int off = getOffFromStackTop(idn_ime);
                loadToFromStack ("R0", off);
                operatorGeneric("SUB", "R0", "4", "R0");
                operatorGeneric("SHL", "R6", "2", "R6");
                operatorGeneric("SUB", "R0", "R6", "R0");
            }
            loadToFromReg("R6", "R0");
            return {tip, lizraz, idn_ime};
            
        }
        if (p[1]->lexname == "L_ZAGRADA" && p.size() == 3) {
            retValue = provjeri(p[0], currentScope);

            string postfiks_izraz_tip = retValue[0];

            // provjeri je li postfiks.tip = funkcija(void -> pov)
            if (postfiks_izraz_tip.substr(0, 17) != "funkcija(void -> "
               || postfiks_izraz_tip[postfiks_izraz_tip.size()-1] != ')') {
                  error(c);
               }

            code.pop_back(); // TODO: jer to ide u <primarni_izraz> pa IDN, a ne zelimo da iz f(5) loada vrijednost f za koju misli da je varijabla
            string functionName = retValue[2]; // TODO: provjerit da je ovo ok
            code.push_back("\t\tCALL " + (functionName == "main" ? "main" : "f_" + functionName));

            string pov = postfiks_izraz_tip.substr(17, postfiks_izraz_tip.size()-18);

            string tip = pov;
            string lizraz = "0";

            if (retValue.size() >= 3) return {tip, lizraz, retValue[2]};
            else return {tip, lizraz};
        }
        if (p[1]->lexname == "L_ZAGRADA" && p.size() == 4) {
            retValue = provjeri(p[0], currentScope);

            code.pop_back(); // TODO: jer to ide u <primarni_izraz> pa IDN, a ne zelimo da iz f(5) loada vrijednost f za koju misli da je varijabla
            string postfiks_izraz_tip = retValue[0];
            string functionName = retValue[2]; // TODO: provjerit da je ovo ok
            // provjeri je li funkcija
            // TODO: stroza provjera ????
            if (postfiks_izraz_tip.substr(0, 8) != "funkcija") error(c);
            // izvuci vektor parametara iz params iz funkcija(params -> pov)
            int id = postfiks_izraz_tip.find(' ');
            string params = postfiks_izraz_tip.substr(9, id-9);

            vector<string>vparams;
            parseListaParametaraRet(params, vparams);
            
            int stackSizeBeforeArguments = st.size();
            
            retValue = provjeri(p[2], currentScope);
            vector<string>lista_arg_tipovi;
            parseListaParametaraRet(retValue[0], lista_arg_tipovi);
            // provjeri vrijedi li redom po parovima argumenata iz lista_arg_tipovi i vparams
            // da se mogu castati

            if (vparams.size() != lista_arg_tipovi.size()) error(c);

            
            code.push_back("\t\tCALL f_" + functionName);
            while ((int)(st.size()) != stackSizeBeforeArguments) popFromStackTo("R0");
            for (int i = 0; i < (int)vparams.size(); i++) if (!canCast(lista_arg_tipovi[i], vparams[i])) error(c);

            string pov = postfiks_izraz_tip.substr(id+4, postfiks_izraz_tip.size()-(id+5));
            string tip = pov, lizraz = "0";

            
            if (retValue.size() >= 3) return {tip, lizraz, retValue[2]};
            else return {tip, lizraz};
        }
        if (p[1]->lexname == "OP_INC" || p[1]->lexname == "OP_DEC") {
            retValue = provjeri(p[0], currentScope);
            string op = (p[1]->lexname == "OP_INC" ? "ADD" : "SUB");
            string postfiks_izraz_tip = retValue[0];
            string postfiks_izraz_lizraz = retValue[1];
            if (postfiks_izraz_lizraz != "1" || !canCast(postfiks_izraz_tip, "int")) error(c);
            string idn_ime = retValue[2];
            Scope *runner = currentScope;
            whichScope(runner, idn_ime);
            if (runner == globalScope) {
                loadToFromStatic ("R6", currentScope->varAddress[idn_ime]); // jer ce tu biti vrijednost s desne strane jednakosti
            }
            else {
                int off = getOffFromStackTop(idn_ime);
                loadToFromStack ("R6", off);
            }
            operatorGeneric(op, "R6", "1", "R1");
            if (runner == globalScope) {
                storeFromToStatic ("R1", currentScope->varAddress[idn_ime]); // jer ce tu biti vrijednost s desne strane jednakosti
            }
            else {
                int off = getOffFromStackTop(idn_ime);
                storeFromToStack ("R1", off);
            }
            if (retValue.size() >= 3) return {"int", "0", retValue[2]};
            else return {"int", "0"};
        }
    } else if(c->name == "<lista_argumenata>") {
        if (p.size() == 1) {
            retValue = provjeri(p[0], currentScope);

            pushToStackFrom("R6", ",");
            return {retValue[0]};
        }
        if (p.size() == 3) {
            retValue = provjeri(p[0], currentScope);

            string lista_arg_tipovi = retValue[0];

            retValue = provjeri(p[2], currentScope);

            pushToStackFrom("R6", ",");

            string izraz_pridruzivanja_tip = retValue[0];

            // dodaj izraz_pridruzivanja_tip na kraj liste lista_arg_tipovi
            return {lista_arg_tipovi + "," + izraz_pridruzivanja_tip};
        }
    } else if(c->name == "<unarni_izraz>") {
        if (p[0]->name == "<postfiks_izraz>") {
            retValue = provjeri(p[0], currentScope);
            string tip = retValue[0];
            string lizraz = retValue[1];
            if(retValue.size() >= 3) return {tip, lizraz, retValue[2]};
            return {tip, lizraz};
        } 
            // TODO: vjerjatno ne radi
        if (p[0]->lexname == "OP_INC" || p[0]->lexname == "OP_DEC") {
            retValue = provjeri(p[1], currentScope);
            string op = "";
            op = (p[0]->lexname == "OP_INC" ? "ADD" : "SUB");
            operatorGeneric(op, "R6", "1", "R6"); 
            string unarni_izraz_tip = retValue[0];
            string unarni_izraz_lizraz = retValue[1];
            string idn_ime = retValue[2];
            if (unarni_izraz_lizraz != "1" || !canCast(unarni_izraz_tip, "int")) error(c);
            Scope *runner = currentScope;
            whichScope(runner, idn_ime);
            if (runner == globalScope) {
                storeFromToStatic ("R6", currentScope->varAddress[idn_ime]); // jer ce tu biti vrijednost s desne strane jednakosti
            }
            else {
                int off = getOffFromStackTop(idn_ime);
                storeFromToStack ("R6", off);
            }
            return {"int", "0"};
        }
        if (p[0]->name == "<unarni_operator>") {
            retValue = provjeri(p[1], currentScope);

            string cast_izraz_tip = retValue[0];

            if (!canCast(cast_izraz_tip, "int")) error(c);
            if(p[0]->production[0]->lexname == "MINUS") negateR6();
            else if(p[0]->production[0]->lexname == "OP_TILDA") {
                negateR6();
                operatorGeneric("SUB", "R6", "1", "R6");
            } else if(p[0]->production[0]->lexname == "OP_NEG") {
                isFalse("R6");
                fillReg("1", "R6");
                skipOperatorNext("EQ");
                fillReg("0", "R6");
            }
            return {"int", "0"};
        }
    } else if(c->name == "<unarni_operator>") {
        return {}; // TODO: ne treba nista ?
    } else if(c->name == "<cast_izraz>") {
        if (p.size() == 1) {
            retValue = provjeri(p[0], currentScope);

            string unarni_izraz_tip = retValue[0];
            string unarni_izraz_lizraz = retValue[1];

            return {unarni_izraz_tip, unarni_izraz_lizraz};
        }
        if (p.size() == 4) {
            retValue = provjeri(p[1], currentScope);

            string ime_tipa_tip = retValue[0];

            retValue = provjeri(p[3], currentScope);

            string cast_izraz_tip = retValue[0];

            // eksplicitno castanje moze biti samo na brojevnim tipovima (T), 
            // ali se tipovi X mogu castati implicitno u to, pa se valjda i oni broje
            // (iz ispisa 4.22 u uputama?)

            if (!isX(ime_tipa_tip) || !isX(cast_izraz_tip)) error(c);

            return {ime_tipa_tip, "0"};
        }
    } else if(c->name == "<ime_tipa>") {
        if (p.size() == 1) {
            retValue = provjeri(p[0], currentScope);

            return retValue;
        }
        if (p.size() == 2) {
            retValue = provjeri(p[1], currentScope);

            string specifikator_tipa_tip = retValue[0];

            // provjeri da ne pokusavas napraviti const(void)
            if (specifikator_tipa_tip == "void") error(c);

            string tip = string("const(") + specifikator_tipa_tip + ")";

            return {tip};
        }
    } else if(c->name == "<specifikator_tipa>") {
      string tip = "";
      if (p[0]->lexname == "KR_VOID") tip = "void";
      if (p[0]->lexname == "KR_CHAR") tip = "char";
      if (p[0]->lexname == "KR_INT") tip = "int";
      
      return {tip};
    } else if(c->name == "<multiplikativni_izraz>") {
        if (p.size() == 1) {
            return provjeri(p[0], currentScope);
        }
        if (p.size() == 3) {
            binarniIzraz(c, p, currentScope);
            string op = "";
            if (p[1]->lexname == "OP_PUTA") operatorFromStackTo("OP_PUTA", "R6");
            else if(p[1]->lexname == "OP_MOD") operatorFromStackTo("OP_MOD", "R6");
            else if(p[1]->lexname == "OP_DIJELI") operatorFromStackTo("OP_DIJELI", "R6");
            return {"int", "0"};
        }
    } else if(c->name == "<aditivni_izraz>") {
        if (p.size() == 1) {
            return provjeri(p[0], currentScope);
        }
        if (p.size() == 3) {
            binarniIzraz(c, p, currentScope);
            string op = "";
            if (p[1]->lexname == "PLUS") op = "ADD";
            if (p[1]->lexname == "MINUS") op = "SUB";
            operatorFromStackTo(op, "R6");
            return {"int", "0"};
        }
    } else if(c->name == "<odnosni_izraz>") {
        if (p.size() == 1) {
            return provjeri(p[0], currentScope);
        }
        if (p.size() == 3) {
            binarniIzraz(c, p, currentScope);            
            string op = "";
            code.push_back("\t\tMOVE 0, SR");
            operatorFromStackTo("SBC", "R6");
            fillReg("1", "R6");
            if (p[1]->lexname == "OP_LT") op = "SLT";
            if (p[1]->lexname == "OP_GT") op = "SGT";
            if (p[1]->lexname == "OP_GTE") op = "SGE";
            if (p[1]->lexname == "OP_LTE") op = "SLE";           
            skipOperatorNext(op);
            fillReg("0", "R6");
            return {"int", "0"};
        }
    } else if(c->name == "<jednakosni_izraz>") {
        if (p.size() == 1) {
            return provjeri(p[0], currentScope);
        }
        if (p.size() == 3) {
            binarniIzraz(c, p, currentScope);
            code.push_back("\t\tMOVE 0, SR");
            operatorFromStackTo("SBC", "R6");
            fillReg("1", "R6");
            string op = "";
            if (p[1]->lexname == "OP_EQ") op = "EQ";
            if (p[1]->lexname == "OP_NEQ") op = "NE";
            skipOperatorNext(op);
            fillReg("0", "R6");
            return {"int", "0"};
        }
    } else if(c->name == "<bin_i_izraz>") {
        if (p.size() == 1) {
            return provjeri(p[0], currentScope);
        }
        if (p.size() == 3) {
            binarniIzraz(c, p, currentScope);
            string op = "AND";
            operatorFromStackTo(op, "R6");
            return {"int", "0"};
        }
    } else if(c->name == "<bin_xili_izraz>") {
        if (p.size() == 1) {
            return provjeri(p[0], currentScope);
        }
        if (p.size() == 3) {
            binarniIzraz(c, p, currentScope);
            string op = "XOR";
            operatorFromStackTo(op, "R6");
            return {"int", "0"};
        }
    } else if(c->name == "<bin_ili_izraz>") {
        if (p.size() == 1) {
            return provjeri(p[0], currentScope);
        }
        if (p.size() == 3) {
            binarniIzraz(c, p, currentScope);
            string op = "OR";
            operatorFromStackTo(op, "R6");
            return {"int", "0"};
        }
    } else if(c->name == "<log_i_izraz>") {
        if (p.size() == 1) {
            return provjeri(p[0], currentScope);
        }
        if (p.size() == 3) {
            return logIzraz(c, p, currentScope, "OP_I");
        }
    } else if(c->name == "<log_ili_izraz>") {
        if (p.size() == 1) {
            return provjeri(p[0], currentScope);
        }
        if (p.size() == 3) {
            return logIzraz(c, p, currentScope, "OP_ILI");
        }
    } else if(c->name == "<izraz_pridruzivanja>") {
        if (p.size() == 1) {
            return provjeri(p[0], currentScope);
        }
        if (p.size() == 3) {
            retValue = provjeri(p[0], currentScope);

            string postfiks_izraz_tip = retValue[0];
            string postfiks_izraz_lizraz = retValue[1];
            string postfiks_izraz_ime = retValue[2];

            Scope *runner = currentScope;
            whichScope(runner, postfiks_izraz_ime);

            if (postfiks_izraz_lizraz != "1") error(c);
            bool isArray = (st.back() == "offset");
            retValue = provjeri(p[2], currentScope);
            
            string izraz_pridruzivanja_tip = retValue[0];
            if(!isArray) {
                if(st.size() && st.back()=="offset") popFromStackTo("R0");
                if (runner == globalScope) {
                    storeFromToStatic ("R6", runner->varAddress[postfiks_izraz_ime]); // jer ce tu biti vrijednost s desne strane jednakosti
                }
                else {
                    int off = getOffFromStackTop(postfiks_izraz_ime);
                    storeFromToStack ("R6", off);
                }
            } else {
                if (runner == globalScope) {
                    loadToFromStatic("R0", runner->varAddress[postfiks_izraz_ime]);
                    
                    popFromStackTo("R1");
                    operatorGeneric("ADD", "R1", "1", "R1");
                    operatorGeneric("SHL", "R1", "2", "R1");
                    operatorGeneric("ADD", "R0", "R1", "R0");
                    storeFromToReg ("R6", "R0"); // jer ce tu biti vrijednost s desne strane jednakosti
                }
                else {
                    int off = getOffFromStackTop(postfiks_izraz_ime);
                    loadToFromStack("R1", off);
                    popFromStackTo("R0");
                    operatorGeneric("ADD", "R0", "1", "R0");
                    operatorGeneric("SHL", "R0", "2", "R0");
                    operatorGeneric("SUB", "R1", "R0", "R0");
                    storeFromToReg ("R6", "R0");
                }
            }
            
            if (!canCast(izraz_pridruzivanja_tip, postfiks_izraz_tip)) error(c);

            return {postfiks_izraz_tip, "0"};
        }
    } else if(c->name == "<izraz>") {
        // izvedena svojstva
        string tip = "", lizraz = "";

        if(p.size() == 1) {

            // provjeri izraz pridruzivanja
            retValue = provjeri(p[0], currentScope);
            string izraz_pridruzivanja_tip = retValue[0];
            string izraz_pridruzivanja_lizraz = retValue[1];

            tip = izraz_pridruzivanja_tip;
            lizraz = izraz_pridruzivanja_lizraz;
        } else if(p.size() == 3) {
            
            // provjeri izraz
            provjeri(p[0], currentScope);
            
            // provjeri izraz pridruzivanja
            retValue = provjeri(p[2], currentScope);
            string izraz_pridruzivanja_tip = retValue[0];
            tip = izraz_pridruzivanja_tip;
            lizraz = "0";
        }
        return {tip, lizraz};

    } else if(c->name == "<slozena_naredba>") {
        // provjeri lista deklaracija ili lista naredbi ako nema deklaracija
        provjeri(p[1], currentScope);

        // provjeri listu naredbi ako ima deklaracija
        if(p.size() == 4) provjeri(p[2], currentScope);
        
    } else if(c->name == "<lista_naredbi>") {
        
        // provjeri listu naredbi ili naredbu ako ne postoji lista
        provjeri(p[0], currentScope);
        
        // provjeri naredbu ako postoji lista
        if(p.size() == 2) provjeri(p[1], currentScope);
    } else if(c->name == "<naredba>") {

        // nasljedna svojstva
        Scope* newScope = new Scope();
        newScope->parentScope = currentScope;
        string parentBreakAddress = "", parentContinueAddress = "";
        if(params.size()) {
            parentBreakAddress = params[0];
            parentContinueAddress = params[1];
        } else {
            parentBreakAddress = currentScope->breakAddress;
            parentContinueAddress = currentScope->continueAddress;
        }
        string breakAddress = "b", continueAddress = "s", normalAddress = "o";
        reserveLabel(breakAddress);
        reserveLabel(continueAddress);
        reserveLabel(normalAddress);
        newScope->breakAddress = breakAddress;
        newScope->continueAddress = continueAddress;

        // provjeri jedinicnu produkciju
        provjeri(p[0], newScope);
        int noOfPops = newScope->stackBytes;
        while (newScope->stackBytes) {
            newScope->stackBytes--;
            popFromStackTo("R0");
        }
        jumpLink(normalAddress);
        putLabel("int", -1, breakAddress, true);
        if(parentBreakAddress != "") {
            for(int i = 0; i < noOfPops; i++) code.push_back("\t\tPOP R0");
            jumpLink(parentBreakAddress);
        }
        putLabel("int", -1, continueAddress, true);
        if(parentContinueAddress != "") {
            for(int i = 0; i < noOfPops; i++) code.push_back("\t\tPOP R0");
            jumpLink(parentContinueAddress);
        }
        putLabel("int", -1, normalAddress, true);
    } else if(c->name == "<izraz_naredba>") {
        string tip = "";
        if(p.size() == 1) {
            fillReg("1", "R6");
            tip = "int";
        }
        else {
            
            // provjeri izraz
            retValue = provjeri(p[0], currentScope);
            string izraz_tip = retValue[0];
            tip = izraz_tip;
        }
        return {tip};
    } else if(c->name == "<naredba_grananja>") {
        if (p.size() == 5) {
            retValue = provjeri(p[2], currentScope);
            string outLabel = "l";
            reserveLabel(outLabel);
            isFalse("R6");
            conditionoalJumpLink(outLabel);
            string izraz_tip = retValue[0];

            if (!canCast(izraz_tip, "int")) error(c);

            provjeri(p[4], currentScope);
            putLabel("int", -1, outLabel, true);
        }
        if (p.size() == 7) {
            retValue = provjeri(p[2], currentScope);

            string izraz_tip = retValue[0];
            string outLabel = "l";
            string elseLabel = "l";
            reserveLabel(outLabel);
            reserveLabel(elseLabel);
            isFalse("R6");
            conditionoalJumpLink(elseLabel);
            if (!canCast(izraz_tip, "int")) error(c);

            provjeri(p[4], currentScope);
            jumpLink(outLabel);
            putLabel("int", -1, elseLabel, true);
            provjeri(p[6], currentScope);
            putLabel("int", -1, outLabel, true);
        }
    } else if(c->name == "<naredba_petlje>") {
// oznaci da si scope petlje (potrebno za provjeru continue i break)
        string mainLoop = "";
        string outLabel = "l";
        currentScope->layersOfLoops = 1;
        if (p.size() == 5) {
            putLoopLabel(mainLoop);
            retValue = provjeri(p[2], currentScope);
            isFalse("R6");
            reserveLabel(outLabel);
            conditionoalJumpLink(outLabel);
            
            string izraz_tip = retValue[0];

            if (!canCast(izraz_tip, "int")) error(c);

            provjeri(p[4], currentScope, {outLabel, mainLoop});

            jumpLink(mainLoop);
            putLabel("int", -1, outLabel, true);
        }
        if (p.size() == 6) {
            provjeri(p[2], currentScope);
            
            putLoopLabel(mainLoop);   
            retValue = provjeri(p[3], currentScope);
            isFalse("R6");
            reserveLabel(outLabel);
            conditionoalJumpLink(outLabel);
      
            string izraz_tip = retValue[0];

            if (!canCast(izraz_tip, "int")) error(c);

            provjeri(p[5], currentScope, {outLabel, mainLoop});

            jumpLink(mainLoop);
            putLabel("int", -1, outLabel, true);
        }
        if (p.size() == 7) {
            provjeri(p[2], currentScope);
            putLoopLabel(mainLoop);
            retValue = provjeri(p[3], currentScope);
            string izraz_tip = retValue[0];
            isFalse("R6");
            reserveLabel(outLabel);
            conditionoalJumpLink(outLabel);
      
            string loopCommand = "";
            if (!canCast(izraz_tip, "int")) error(c);
            string contentLabel = "l";
            reserveLabel(contentLabel);
            jumpLink(contentLabel);
            putLoopLabel(loopCommand);
            provjeri(p[4], currentScope);
            jumpLink(mainLoop);
            putLabel("int", 0, contentLabel, true);
            provjeri(p[6], currentScope, {outLabel, loopCommand});
            jumpLink(loopCommand);
            putLabel("int", -1, outLabel, true);
        }

    } else if(c->name == "<naredba_skoka>") {
        if (p[0]->lexname == "KR_CONTINUE" || p[0]->lexname == "KR_BREAK") {
            Scope* runner = currentScope;
            bool foundLoop = false;
            while (runner != nullptr) {
               if (runner->layersOfLoops) {
                  foundLoop = true;
                  break;
               }
               runner = runner->parentScope;
            }
            if (!foundLoop) error(c);
            if(p[0]->lexname == "KR_CONTINUE") jumpLink(currentScope->continueAddress);
            else jumpLink(currentScope->breakAddress);
        }
        if (p[0]->lexname == "KR_RETURN") {
            Scope* runner = currentScope;
            string tip_funkcije = "";
            while (runner != nullptr) {
               if (runner->returnType != "") {
                  tip_funkcije = runner->returnType;
                  break;
               }
               runner = runner->parentScope;
            }
            if (p.size() == 2) {
               if (tip_funkcije != "void") error(c);
            }
            if (p.size() == 3) {
               retValue = provjeri(p[1], currentScope);

               string izraz_tip = retValue[0];
               if (!canCast(izraz_tip, tip_funkcije)) error(c);
            }
            // idemo cistiti stog od trenutnog scopea do scopea definicije funkcije
            
            addReturn(currentScope, runner);

        }
    } else if(c->name == "<prijevodna_jedinica>") {
        if(p[0]->name == "<vanjska_deklaracija>") {
            
            // provjeri vanjska deklaracija
            provjeri(p[0], currentScope);
        } else if(p[0]->name == "<prijevodna_jedinica>") {
            
            // provjeri prijevodna jedinica
            provjeri(p[0], currentScope);
            
            // provjeri vanjska deklaracija
            provjeri(p[1], currentScope);             
        } 
    } else if(c->name == "<vanjska_deklaracija>") {
        // provjeri definicija funkcije ili deklaracija
        provjeri(p[0], currentScope);
    } else if(c->name == "<definicija_funkcije>") {

         // TODO: currentScope != globalScope?
        // provjeri ime tipa
        retValue = provjeri(p[0], currentScope);
        string ime_tipa_tip = retValue[0];

        string idn_ime = p[1]->val;


        string f_label = idn_ime == "main" ? "main" : "f_" + idn_ime;
        code.push_back(f_label);

        // <ime_tipa>.tip != const(T)
        if(ime_tipa_tip.substr(0, 5) == "const") error(c);
        
        // ne postoji prije definirana funkcija IDN.ime
        for(auto t:currentScope->defintions) {
            int id = t.find("?");
            if(id == -1) continue;
            string tempS = t.substr(0, id);
            if(tempS == p[1]->val) error(c);
        }
        
        string funcType;
        Scope *newScope = new Scope();
        newScope->parentScope = currentScope;
        if(p[3]->name == "<lista_parametara>") {

            // provjeri lista naredba
            retValue = provjeri(p[3], newScope);
            string lista_parametara_tipovi = retValue[0];
            string lista_parametara_imena  = retValue[1];

            // zabiljezi varijable u lokalni djelokrug, lol vimena
            vector<string> vtipovi, vimena;
            parseListaParametaraRet(lista_parametara_tipovi, vtipovi);
            parseListaParametaraRet(lista_parametara_imena, vimena);
            for(int i = 0; i < (int)vtipovi.size(); i++) newScope->declarations[vimena[i]] = vtipovi[i];

            funcType = "funkcija(" + lista_parametara_tipovi + " -> " + ime_tipa_tip + ")";
        } else if(p[3]->name == "KR_VOID") {
            funcType = "funkcija(void -> " + ime_tipa_tip + ")";
        }
        newScope->returnType = ime_tipa_tip;
        
        st.push_back("!");
        newScope->stackBytes++;

        
        newScope->stackSizeBeforeParameters = st.size();

        // ako postoji deklaracija moraju se podudarati
        if(currentScope->declarations.find(p[1]->val) != currentScope->declarations.end()) {
            if(currentScope->declarations[p[1]->val] != funcType) error(c);

            // zabiljezi deklaraciju
        } else {
            currentScope->declarations[p[1]->val]  = funcType; 
            allDeclaredFunctions.push_back({p[1]->val, funcType});
        }
        // zabiljezi definiciju
        currentScope->defintions.insert(p[1]->val + "?" + funcType);
        provjeri(p[5], newScope);
        
        addReturn(currentScope, newScope, true);

        if(idn_ime != "main")code.push_back("e_" + idn_ime);

    } else if(c->name == "<lista_parametara>") {
        vector<string> isUseless = {};
        if(params.size()) isUseless.push_back(params[0]);
        if(p.size() == 1) return provjeri(p[0], currentScope, isUseless);
        if(p.size() == 3) {
            retValue = provjeri(p[0], currentScope, isUseless);
            string lista_parametara_tipovi = retValue[0];
            string lista_parametara_imena = retValue[1];

            retValue = provjeri(p[2], currentScope, isUseless);
            string deklaracija_parametra_tip = retValue[0];
            string deklaracija_parametra_ime = retValue[1];
            
            // provjeri da deklaracija_parametra.ime nije u lista_parametara.imena
            vector<string> tempV;
            parseListaParametaraRet(lista_parametara_imena, tempV);
            for(auto t:tempV) if(t == deklaracija_parametra_ime) error(c);
            return {lista_parametara_tipovi + "," + deklaracija_parametra_tip, lista_parametara_imena + "," + deklaracija_parametra_ime};
        }
        
    } else if(c->name == "<deklaracija_parametra>") {
        vector<string> isUseless = {};
        if(params.size()) isUseless.push_back(params[0]);
        // provjeri ime_tipa
        retValue = provjeri(p[0], currentScope, isUseless);
        string ime_tipa_tip = retValue[0];
        
        string idn_ime = p[1]->val;
        if(!isUseless.size()) {
            st.push_back(idn_ime);
            currentScope->stackBytes++;
        }
        // ime_tipa.tip != void
        if(ime_tipa_tip == "void") error(c);
        if(p.size() == 2) return {ime_tipa_tip, p[1]->val};
        else if(p.size() == 4) return {string("niz(") + ime_tipa_tip + ")", p[1]->val}; 
    } else if(c->name == "<lista_deklaracija>") {

        // provjeri deklaracija
        if(p.size() == 1) return provjeri(p[0], currentScope);
        else if(p.size() == 2) {
            
            // provjeri lista deklaracija
            provjeri(p[0], currentScope);
            
            // provjeri deklaracija
            provjeri(p[1], currentScope);
        }
    } else if(c->name == "<deklaracija>") {
        
        // provjeri ime tipa
        retValue = provjeri(p[0], currentScope);
        string ime_tipa_tip = retValue[0];
        
        // provjeri lista init deklaratora uz nasljedno svojstvo
        provjeri(p[1], currentScope, {ime_tipa_tip});

    } else if(c->name == "<lista_init_deklaratora>") {
        
        // nasljedno svojstvo
        string ntip = params[0];
        
        // provjeri init deklarator uz nasljedno svojstvo
        if(p.size() == 1) provjeri(p[0], currentScope, {ntip});
        else if(p.size() == 3) {

            // provjeri lista init deklaratora uz nasljedno svojstvo
            provjeri(p[0], currentScope, {ntip});

            // provjeri init deklarator uz nasljedno svojstvo
            provjeri(p[2], currentScope, {ntip});
        }
    } else if(c->name == "<init_deklarator>") {
        
        // nasljedno svojstvo
        string ntip = params[0];
        
        // provjeri izravni deklarator uz nasljedno svojstvo
        retValue = provjeri(p[0], currentScope, {ntip});
        string izravni_deklarator_tip = retValue[0];
        string izravni_brelem_string = retValue[1];
        
        string idn_ime = retValue[2];
        
        if(izravni_deklarator_tip.substr(0, 8) != "funkcija") {
            if (currentScope == globalScope) {
                currentScope->varAddress[idn_ime] = firstFreeAddress();
        
                if(izravni_brelem_string != "") putLabel("int", currentScope->varAddress[idn_ime], "n", false, stoi(izravni_brelem_string));
                else putLabel("int", currentScope->varAddress[idn_ime]);
        
                if(izravni_brelem_string != "") {
                    int constAddress = 0;
                    storeConst("int", currentScope->varAddress[idn_ime], constAddress);
                    loadToFromStatic("R6", constAddress);
                    storeFromToStatic("R6", currentScope->varAddress[idn_ime]);
                }
            }
            else {
                currentScope->varAddress[idn_ime] = 0x40000 - st.size() * 4;   // lokalna varijabla, "adresa" joj je koja je po redu na "stacku ove funkcije"
                currentScope->stackBytes++;
                if(izravni_deklarator_tip == "niz(int)" || izravni_deklarator_tip == "niz(char)") pushToStackFrom("R7", idn_ime); 
                else pushToStackFrom("R0", idn_ime); // samo da se napravi mjesto, nebitna vrijednost
                fillReg("0", "R0");
                if(izravni_brelem_string != "") for(int i = 0; i < stoi(izravni_brelem_string); i++) pushToStackFrom("R0", "[]");
                
            }
        } 
        if(p.size() == 1) {

            // provjeri izravni deklarator.tip != const(T) || niz(const(T))
            if(izravni_deklarator_tip == "const(int)" || izravni_deklarator_tip == "const(char)" || izravni_deklarator_tip == "niz(const(int))" || izravni_deklarator_tip == "niz(const(char))") error(c);

        } else if(p.size() == 3) {
            if(izravni_deklarator_tip == "niz(int)" || izravni_deklarator_tip == "niz(char)" || izravni_deklarator_tip == "niz(const(int))" || izravni_deklarator_tip == "niz(const(char))") {
                if(currentScope == globalScope) {
                    loadToFromStatic("R6", currentScope->varAddress[idn_ime]);
                    operatorGeneric("ADD", "R6", "4", "R6");
                    pushToStackFrom("R6", idn_ime);
                } else {
                    int off = getOffFromStackTop(idn_ime);
                    loadToFromStack ("R6", off);
                    operatorGeneric("SUB", "R6", "4", "R6");
                    pushToStackFrom("R6", idn_ime);
                }
            }
            
            // provjeri inicijalizator 
            retValue = provjeri(p[2], currentScope, {ntip});
            if(izravni_deklarator_tip == "niz(int)" || izravni_deklarator_tip == "niz(char)" || izravni_deklarator_tip == "niz(const(int))" || izravni_deklarator_tip == "niz(const(char))") {
                popFromStackTo("R0");
            }
            
            string inicijalizator_tip = retValue[0];
            
            if(isX(izravni_deklarator_tip)) {
                
                // ako izravni deklarator tip = T ili const(T) mora se moci implicitno pretvoriti
                // iz inicijalizator.tip u T
                string tempT = izravni_deklarator_tip;
                if(tempT.size() > 4) tempT = tempT.substr(6, tempT.size() - 7); 
                if(!canCast(inicijalizator_tip, tempT)) error(c);
                if (currentScope == globalScope) {
                    storeFromToStatic ("R6", currentScope->varAddress[idn_ime]); // jer ce tu biti vrijednost s desne strane jednakosti
                }
                else {
                    int off = getOffFromStackTop(idn_ime);
                    storeFromToStack ("R6", off);
                }

            } else if(izravni_deklarator_tip == "niz(int)" || izravni_deklarator_tip == "niz(char)" || izravni_deklarator_tip == "niz(const(int))" || izravni_deklarator_tip == "niz(const(char))") {
                
                string tempT = izravni_deklarator_tip;
                if(tempT.size() > 9) tempT = tempT.substr(10, tempT.size() - 12);
                else tempT = tempT.substr(4, tempT.size() - 5);

                // je li izravni vratio brelem
                if (izravni_brelem_string == "") error(c);
                int izravni_deklarator_brelem = stoi(izravni_brelem_string);
                // imas li br_elem inicijalizatore? ako ne umre
                if (retValue[1] == "") error(c);
                int inicijalizator_brelem = stoi(retValue[1]);
                string inicijalizator_tipovi = retValue[2];
                // provjeri inicijalizator.breleme <= izravni deklarator.brelem
                
                if(inicijalizator_brelem > izravni_deklarator_brelem) error(c);    
                

                // provjeri za svaki tip iz inicijalizator.tipovi da se moze implicitno
                // pretvoriti u izravni deklarator.tip
                vector<string> tempV;
                parseListaParametaraRet(inicijalizator_tipovi, tempV);
                
                int arrayIndex = 0;
                
                for(auto t:tempV) {
                    if(!canCast(t, tempT)) error(c);
                    arrayIndex++;
                }

            } else error(c);
        }
    } else if(c->name == "<izravni_deklarator>") {
        // nasljedna svojstva
        string ntip = params[0];

        // izvedena svojstva
        string tip = "", brelem = "";
        if(p.size() == 1) {
            tip = ntip;
            
            // provjeri ntip != void
            if(ntip == "void") error(c);

            // provjeri da IDN.ime nije deklarirano u  lokalnom djelokrugu
            if(currentScope->declarations.find(p[0]->val) != currentScope->declarations.end()) error(c);

            // zabiljezi deklaraciju s odgovarajucim tipom
            currentScope->declarations[p[0]->val] = tip;
            allDeclaredFunctions.push_back({p[0]->val, tip});

            if (ntip == "int" || ntip == "const(int)" || ntip == "char" || ntip == "const(char)") {
                currentScope->varAddress[p[0]->val] = biggestAddress + (4-biggestAddress)%4;
                biggestAddress = biggestAddress + (4-biggestAddress)%4 + 4;
            }
        } else if(p.size() == 4) {
            if(p[2]->lexname == "BROJ") {
                tip = string("niz(") + ntip + ")";
                brelem = p[2]->val;

                // provjeri ntip != void
                if(ntip == "void") error(c);

                // provjeri da IDN.ime nije deklarirano u  lokalnom djelokrugu
                if(currentScope->declarations.find(p[0]->val) != currentScope->declarations.end()) error(c);
            
                // provjeri da je BROJ.vrijednost > 0 i <= 1024
                if(stoll(brelem) <= 0 || stoll(brelem) > 1024) error(c);
            
                // zabiljezi deklaraciju s odgovarajucim tipom
                currentScope->declarations[p[0]->val] = tip;
                allDeclaredFunctions.push_back({p[0]->val, tip});
                if (ntip == "int" || ntip == "const(int)") {
                    currentScope->varAddress[p[0]->val] = biggestAddress + (4-biggestAddress)%4;
                    biggestAddress = biggestAddress + (4-biggestAddress)%4 + (stoi(brelem) + 1) * 4;
                }
                if (ntip == "char" || ntip == "const(char)") {
                    currentScope->varAddress[p[0]->val] = biggestAddress;
                    biggestAddress += (stoi(brelem) + 1);
                }
                
            } else if(p[2]->lexname == "KR_VOID") {
                tip = string("funkcija(void -> ") + ntip + ")";
                // ako je vec deklarirano IDN.ime mora biti tipa funkcija(void -> ntip)
                if(currentScope->declarations.find(p[0]->val) != currentScope->declarations.end()) {
                    if(currentScope->declarations[p[0]->val] != tip) error(c);
                // inace je zabiljezi u deklaracije
                } else {
                    currentScope->declarations[p[0]->val] = tip;
                    allDeclaredFunctions.push_back({p[0]->val, tip});
                }
            } else if(p[2]->name == "<lista_parametara>") {

                // provjeri lista parametara
                retValue = provjeri(p[2], currentScope, {"useless"});
                string lista_parametara_tipovi = retValue[0];
                vector<string> tempV;
                parseListaParametaraRet(lista_parametara_tipovi, tempV);
                tip = string("funkcija(") + lista_parametara_tipovi + " -> " + ntip + ")";
                
                // ako je vec deklarirano IDN.ime mora biti tipa funkcija(<lista_parametara>.tipovi -> ntip)
                if(currentScope->declarations.find(p[0]->val) != currentScope->declarations.end()) {
                    if(currentScope->declarations[p[0]->val] != tip) error(c);
                // inace je zabiljezi u deklaracije
                } else {
                    currentScope->declarations[p[0]->val] = tip;
                    allDeclaredFunctions.push_back({p[0]->val, tip});
                }
            }
        }
        return {tip, brelem, p[0]->val}; // #TODO: vrati i IDN.ime

    } else if(c->name == "<inicijalizator>") {
        // izvedena svojstva
        string tip = "", brelem = "", tipovi = "", value="";
        if(p.size() == 1) {
            // provjeri da se moze izraz pridruzivanja *=>
            string charArray = "";
        
            for(SyntaxNode *tempNode = p[0];; tempNode = tempNode->production[0]) {
                if(tempNode->lexname != "" && tempNode->lexname == "NIZ_ZNAKOVA") {
                    charArray = tempNode->val;
                    break;
                }
                else if(tempNode->production.size() != 1 || tempNode->lexname != "") break;
            } 
        
            // ako vrijedi gornja relacija
            retValue = provjeri(p[0], currentScope);
            if(charArray.size()) {
                int charArrayBrElem = 0;
                for(int i = 1; i < (int)charArray.size() - 1; i++) {
                    charArrayBrElem++;
                    if(charArray[i] == '\\') i++;
                }
                brelem = to_string(charArrayBrElem + 1);
                string tempS = "";
                for(int i = 0; i < charArrayBrElem+1; i++) tempS += "char,";
                tempS.pop_back();
                tipovi = tempS;
            } else {

                // provjeri izraz pridruzivanja
                tip = retValue[0];
            }
        } else if(p.size() == 3) {

            // provjeri listra izraza pridruzivanja
            retValue = provjeri(p[1], currentScope);
            brelem = retValue[1];
            tipovi = retValue[0];
        }
        return {tip, brelem, tipovi, value};
    } else if(c->name == "<lista_izraza_pridruzivanja>") {
        // nasljedno svojstvo koja je pozicija u arrayu
        loadToFromStack("R0", 0);
        string op = "";
        if(currentScope == globalScope) op = "ADD";
        else op = "SUB";
        if(p.size() == 1) {
            // trece nasljedno svojstvo je pozicija u nizu
            // provjeri izraz pridruzivanja
            retValue = provjeri(p[0], currentScope);
            if(st.back() == "offset") popFromStackTo("R0");
            popFromStackTo("R0");
            storeFromToReg("R6", "R0");
            operatorGeneric(op, "R0", "4", "R0");
            pushToStackFrom("R0", "[]");
            return {retValue[0], "1"};
        } else if(p.size() == 3) {

            // provjeri lista izraza pridruzivanja
            retValue = provjeri(p[0], currentScope);

            string lip_tipovi = retValue[0];    
            string lip_brelem = retValue[1];

            // provjeri izraz pridruzivanja
            retValue = provjeri(p[2], currentScope);
            if(st.back() == "offset") popFromStackTo("R0");
            popFromStackTo("R0");
            storeFromToReg("R6", "R0");
            operatorGeneric(op, "R0", "4", "R0");
            pushToStackFrom("R0", "[]");
            string izraz_pridruzivanja_tip = retValue[0];
            // !prev pushToStackFrom("R6", "[]");
            return {lip_tipovi + "," + izraz_pridruzivanja_tip, to_string(stoi(lip_brelem) + 1)};
        }
    } else error(c);
    return {};
}

int main() {
    SyntaxNode *startNode;
    code.push_back("\t\tMOVE 040000, R7");
    readline(startNode);
    provjeri(startNode, globalScope);
    if(globalScope->declarations["main"] != "funkcija(void -> int)") {
        cout << "main";
        exit(0);
    }
    for(auto t:allDeclaredFunctions) if(t.second.size() > 8 && t.second.substr(0, 8) == "funkcija" && globalScope->defintions.find(t.first + "?" + t.second) == globalScope->defintions.end()) {
        cout << "funkcija";
        exit(0);
    }

    bool funBody = false;
    for (auto s : code) {
        if (s[0] == 'f') funBody = true;
        
        if (funBody) funs.push_back(s);
        else  result.push_back(s);
        if (s[0] == 'e') funBody = false;
    }

    for (auto s : funs) result.push_back(s);
    ofstream file("a.frisc");
    // for (auto line : code) cout << line << endl;
    addMulCode(result);
    addDivCode(result);
    addModCode(result);
    for (auto line : result) {
        if(line == "main") file << "\t\tCALL main\n\t\tHALT\n";
        file << line << "\n";
    }
    file.close();
}