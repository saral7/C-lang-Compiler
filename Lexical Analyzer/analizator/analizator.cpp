#include <bits/stdc++.h>

using namespace std;

struct tableStruct {
   string lexName;
   string charGroup;
   int lineNum;
};

/* IMPORTANT!
   "single state" in comments refers to states in this format [0,q1] or [1,q1]
   "complex state" refers to states in this format {[0,q1],[1,q2]} 
 */

int LINE_COUNT = 1;
int PTR_START, PTR_END, PTR_LAST; /* start and last are used for the grouped characters, end is for the reading head */
string EXPRES; /* used for remembering the single state with the regex current character group is matching with */
string codeText; /* from stdin */
vector<tableStruct> sol; /* solution vector*/
string currState, startState; /* current state, and the starting state (to know where to return to e.g. after error) */

/* parses a line in DFA table to find the state it is about */
bool getMapKeyFromLine (string line, string &ret) {
   for (int i = 0; i < (int)line.size(); i++) {
      if (line[i] == ' ') return true;
      ret += line[i];
   }
   return false;
}

/* parses a line in DFA table and finds all the transitions */
bool getTransitionsFromLine (string line, map<int, string> &v) {
   bool inside = false, started = false;
   pair<int, string> p;
   for (int i = 0; i < (int)line.size(); i++) {
      if (line[i] == ' ') started = true;
      if (!started) continue;
      if (line[i] == '(') {
         inside = true;
         
         p.first = 0;
         p.second = "";
         i++;
         while (line[i] != ':') {
            p.first = (10*p.first) + (line[i]-'0');
            i++;
         }
         continue;
      }
      if (line[i] == ')') {
         inside = false;
         v[p.first] = p.second;
      }

      if (inside) p.second += line[i];
   }
   return false;
}

/* parses a line in DFA table with helper functions */
void parseDFATableLine (string line, string &mapKey, map<int, string> &v) {
   getMapKeyFromLine(line, mapKey);
   getTransitionsFromLine(line, v);
}


/* parses the DFA table and creates the map and finds the starting state */
// TODO: prvo stanje == pocetno stanje?
void parseDFATable (string name, map<string, map<int, string> > * m, string &startState) {
   string filePath = __FILE__;
   size_t lastSlash = filePath.find_last_of("\\/");
   string directoryPath = filePath.substr(0, lastSlash);
   name = directoryPath + name;
   ifstream file;
   file.open(name);
   if (file.is_open()) {
      string line;
      int i = 0;
      while (getline(file, line)) {
         map<int, string> * v = new map<int, string>();
         string mapKey;
         parseDFATableLine(line, mapKey, *v);
         if (i == 0) startState = mapKey;
         i = 1;
         (*m)[mapKey] = *v;
      }
   }

   file.close();
}

/* creates a vector of single state names [], from a complex state name */
vector<string>* splitStateName (string name) {
   vector<string>* v = new vector<string>();
   string p = "";
   int diff = 0;
   for (int i = 1; i < (int)name.size(); i++) {
      if (name[i] == '[') diff++;
      if (name[i] == ']') diff--;
      if (!diff && (name[i] == ',' || i == (int)name.size()-1)) {
         v->push_back(p);
         p = "";
         continue;
      }
      p += name[i];
   }
   return v;
}

/* receives a single state name of an acceptable state, returns appropriate infos about it by references */
void parseSingleState (string name, int &priorityNum, string &lexName, string &switchedState, bool &newLine, int &returnTo) {
   priorityNum = 0;
   returnTo = -1;
   lexName = switchedState = "";
   newLine = false;

   int indStart = 3;
   for (int j = indStart; j < (int)name.size(); j++) {
      if (name[j] == ',') {
         indStart = j+1;
         break;
      }
      priorityNum = (priorityNum*10) + (name[j]-'0');
   }
   for (int j = indStart; j < (int)name.size(); j++) {
      if (name[j] == ',') {
         indStart = j+1;
         break;
      }
      lexName += name[j];
   }
   int diff = 0;
   for (int j = indStart; j < (int)name.size(); j++) {
      if (name[j] == '{') diff++;
      if (name[j] == '}') diff--;
      if (name[j] == ',' && diff == 0) {
         indStart = j+1;
         break;
      }
      switchedState += name[j];
   }
   newLine = (name[indStart] == '1');
   indStart += 2;
   if (name[indStart] == '-') returnTo = -1;
   else {
      returnTo = 0;
      for (int j = indStart; j < (int)name.size()-1; j++) {
         returnTo = (returnTo*10) + (name[j]-'0');
      }
   }
}

/* checks if a state is acceptable, based on its single states acceptabilities */
bool isStateAcceptable (string name) {
   vector<string>* v = splitStateName(name);
   bool acceptable = false;
   for (int i = 0; i < (int)v->size(); i++) {
      string curr = (*v)[i];
      if (curr[1] == '1') acceptable = true;
   }
   return acceptable;
}

/* returns the lex unit from source code that was classified between PTR_START and PTR_LAST */
string getGroupedChars () {
   //TODO: ovaj ret kao pointer?
   string ret = "";
   for (int i = PTR_START; i <= PTR_LAST; i++) ret += codeText[i];
   return ret;
}

/* does the actions based on EXPRES state infos; executed when DFA stops and EXPRES != "" */
void doStateActions (string name) {
   //cout << "found " << name << ", doing actions" << endl;
   int priorityNum = 0, returnTo = 0;
   string lexName = "", switchedState = ""; 
   bool newLine = false;
   parseSingleState(name, priorityNum, lexName, switchedState, newLine, returnTo);

   //cout << "concluded this: " << priorityNum << " " << lexName << " " << switchedState << " " << newLine << " " << returnTo << endl;
   if (returnTo != -1) PTR_LAST = PTR_START+returnTo-1;

   if (lexName != "-" && lexName != "" && returnTo != 0) { //TODO: ovo sam mijenjala
      sol.push_back({lexName, getGroupedChars(), LINE_COUNT});
      //cout << "FOUND this: " << lexName << " " << getGroupedChars() << " " << LINE_COUNT << endl;
   }

   if (newLine) LINE_COUNT++;

   if (switchedState != "-" && switchedState != "") currState = switchedState; //TODO: ovo sam mijenjala
   else currState = startState;
}

/* receives a complex state name of an acceptable state, remembers a single state name with the greatest priority in a global variable EXPRES */
void setNewPriority (string name) {
   vector<string>* v = splitStateName(name);
   
   int foundPriority = 0;

   for (int i = 0; i < (int)v->size(); i++) {
      string curr = (*v)[i];
      int priorityNum = 0;
      for (int j = 3; j < (int)curr.size(); j++) {
         if (curr[j] == ',') break;
         priorityNum = (priorityNum*10) + (curr[j]-'0');
      }
      if (i == 0) foundPriority = priorityNum;

      if (priorityNum <= foundPriority) {
         foundPriority = priorityNum;
         EXPRES = curr;
      }
   }

}

int main () {
   map<string, map<int, string> >* m = new map<string, map<int, string> >();
   parseDFATable("\\dka.txt", m, startState);
   currState = startState;

   /* for (auto it = m->begin(); it != m->end(); it++) {
      string k = it->first;
      cout << "key: " << k << "\n";
      for (auto it2 = (it->second).begin(); it2 != (it->second).end(); it2++) {
         cout << it2->first << " " << it2->second << "\n";
      }
      cout << "\n";
   }  */

   // TODO: citati nekako s pokazivacima u datoteci, jer ovo je meh, doda random praznine
   string line;
   while (getline(cin, line)) {
   	codeText += line + "\n";
   } 
   codeText = codeText.substr(0, codeText.length()-1);
   //cout << codeText;
   //cout << codeText.length() << endl;;
   // TODO: ovaj while uvjet
   string lastState = "";
   while (PTR_START < (int)codeText.size()) {
      //cout << endl << "currState: " << currState << " " << PTR_START << " " << PTR_LAST << " " << PTR_END << " " << EXPRES << endl;
      if (currState == "") { // DFA stops - either error or new lex unit is found
         if (EXPRES == "") { // no matching regex was found - remove one character and start over
            /* error */
            // TODO: stderr
            //cout << "ERROR ON CHAR " << PTR_START << " (" << codeText[PTR_START] << ")" << endl;
            PTR_START++;
            PTR_END = PTR_START;
            PTR_LAST = PTR_START;
            currState = lastState;
            // TODO: provjerit ovo
         }
         else {
            doStateActions(EXPRES);
            PTR_END = PTR_LAST+1;
            PTR_START = PTR_LAST = PTR_END;
            EXPRES = "";
         }
      }
      else {
         lastState = currState;
         if (isStateAcceptable(currState)) {
            //cout << "acceptable" << endl;
            setNewPriority(currState);
            PTR_LAST = PTR_END-1;
         }

         if (PTR_END == (int)codeText.size()) {
            currState = "";
            continue;
         }
         int nxtChr = codeText[PTR_END];
         if (!(m->count(currState)) || !(*m)[currState].count(nxtChr)) currState = "";
         else currState = (*m)[currState][nxtChr];

         PTR_END++;
      }
            
   }

   //cout << "SOLUTION" << endl;
   //ofstream file("output.txt");
   for (int i = 0; i < (int)sol.size(); i++) {
      cout << sol[i].lexName  << " " << sol[i].lineNum << " " << sol[i].charGroup << "\n";
   }
   //file.close();
   return 0;
}