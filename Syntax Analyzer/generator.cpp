#include<iostream>
#include<vector>
#include<utility>
#include<map>
#include<set>
#include<fstream>
#include<algorithm>
#define breturn return
using namespace std;
const int MOD1 = 1e9 + 7;
const int BASE1 = 31337;
const int MOD2 = 1e9 + 3;
const int BASE2 = 31259;
int indexCounter = 0;
int dkaIndexCounter = 0;
int n, m;
vector<void*> allNodes;
vector<string> alphabet;
vector<string> syncSymbols;
map<string, int> index;
int currentCounter = 0;
int terminalCutoff = -1;
vector<vector<vector<int> > > grammar;
vector<vector<int> > tempVector;
vector<int> tempTempVector;
vector<int> emptySymbols;
vector<int> isEmptyArray;
vector<vector<int> > zapocinjeZnakom;
vector<vector<int>> zapocinje;
vector<bool> been;
map<string, pair<int, string> > lrTable;
map<string, int> reductionPriority;
string acceptString;

void fillEmptySymbols() {
    bool changed = false;
    do {
        changed = false;
        for(int i = 0; i < (int)grammar.size(); i++) if(!isEmptyArray[i]) {
            for(int j = 0; j < (int)grammar[i].size(); j++) {
                bool isEmpty = true;
                for(auto symb:grammar[i][j]) {
                    if(symb != -1 && !isEmptyArray[symb]) isEmpty = false;

                } 
                if(isEmpty) isEmptyArray[i] = changed = true;
            }
        }
    } while(changed);
    for(int i = 0; i < (int)isEmptyArray.size(); i++) if(isEmptyArray[i]) emptySymbols.push_back(i);
}
pair<int, int> doubleHash(string s) {
    int hash1 = 0;
    int hash2 = 0;
    for(auto t:s) {
        hash1 = ((hash1 * BASE1)%MOD1 + t)%MOD1;
        hash2 = ((hash2 * BASE2)%MOD2 + t)%MOD2;
    }
    return {hash1, hash2};
}

void fillZapocinjeIzravnoZnakom() {
    for(int i = 0; i < m; i++) {
        for(auto t:grammar[i]) {
            for(int j = 0; j < (int)t.size(); j++) {
                if(t[j] == -1) break;
                zapocinjeZnakom[i][t[j]] = 1;
                if(!isEmptyArray[t[j]]) break;
            }
        }
    }
}

void fillZapocinjeZnakom() {
    fillZapocinjeIzravnoZnakom();
    for(int iteration = 0; iteration < n; iteration++)
        for(int i = 0; i < n; i++) 
            for(int j = 0; j < n; j++) if(zapocinjeZnakom[i][j])
                for(int k = 0; k < n; k++) zapocinjeZnakom[i][k] |= zapocinjeZnakom[j][k];             
    for(int i = 0; i < n; i++) zapocinjeZnakom[i][i] = 1;
}


void fillZapocinje() {
    fillZapocinjeZnakom();
    for(int i = 0; i < m; i++) {
        for(int j = m; j < n; j++) {
            if(zapocinjeZnakom[i][j]) zapocinje[i].push_back(j);
        }
    }
    for(int i = m; i < n; i++) zapocinje[i].push_back(i);
}

void *EnkaNodeFactory(string name);

struct EnkaNode {
    string name;
    vector<pair<int, EnkaNode*> > neighbours;
    bool isFinishState = false;
    int id = -1;
    EnkaNode() {
        name = string("[0,") + to_string(++indexCounter) + "]";
        id = indexCounter;
        allNodes.push_back(this);
        
    }
    EnkaNode(string name) : name(name) {
        id = ++indexCounter;
        allNodes.push_back(this);
    } 
    void add(int c, EnkaNode *n) {
        neighbours.push_back({c, n});
    }
    friend ostream& operator<<(ostream& os, const EnkaNode& obj) {
        os << obj.name << ": ";
        for(auto t:obj.neighbours) os << "(" << t.first << "," << t.second->name << ") ";
        return os;
    }
    void eEnvironment(vector<EnkaNode*> &envir, vector<bool> &been) {
        if(been[this->id]) return;
        envir.push_back(this);
        been[this->id] = true;
        for(auto t:this->neighbours) if(t.first == -1) t.second->eEnvironment(envir, been);
    }
    void createTransitions() {
        int id = name.find(">");
        int startIndex = stoi(name.substr(1, id - 1));     
        ++id;
        int considerIndex = -1;
        vector<int> transitions;
        vector<int> alphas;
        string alphaString = "";
        while(id < (int)name.size()) {
            int nextId = name.find(' ', id);
            if(nextId == -1) nextId = name.size() - 1;
            if(name[id] == '{') {
                alphaString = name.substr(id + 1, name.size() - 3 - id);
                break;
            }
            if(name[id] ==  '.') {
                considerIndex = transitions.size();
                id = nextId + 1;
                continue;
            }
            int nextIndex = stoi(name.substr(id, nextId - id));
            transitions.push_back(nextIndex);
            id = nextId + 1;
        }
        id = 0;
        while(id < (int)alphaString.size()) {
            int nextId = alphaString.find(' ', id);
            if(nextId == -1) nextId = alphaString.size();
            int nextIndex = stoi(alphaString.substr(id, nextId - id));
            alphas.push_back(nextIndex);
            id = nextId + 1; 
        }
        if(considerIndex == (int)transitions.size()) {
            isFinishState = true;
            return;    
        }
        string applyName = string("[") + to_string(startIndex) + ">";
        for(int i = 0; i < (int)transitions.size(); i++) {
            applyName += to_string(transitions[i]) + " ";
            if(i == considerIndex) applyName += ". ";
        }
        applyName += string("{") + alphaString + "}]";
        EnkaNode *newNode = (EnkaNode*)EnkaNodeFactory(applyName);
        add(transitions[considerIndex], newNode);

        int transitionIndex = transitions[considerIndex];
        if(transitionIndex >= terminalCutoff || transitionIndex  == -1) return;
        //next part of code constructs epsilon transitions

        set<int> nextAlpha;
        
        for(int i = considerIndex + 1; i <= (int)transitions.size(); i++) {
            if(i == (int)transitions.size()) {
                for(auto t:alphas) nextAlpha.insert(t);
                break;
            }
            for(auto t:zapocinje[transitions[i]]) nextAlpha.insert(t);
            if(!isEmptyArray[transitions[i]]) break;
        }
        string nextAlphaString = "{";
        for(auto t:nextAlpha) nextAlphaString += to_string(t) + " ";
        nextAlphaString.pop_back();
        nextAlphaString += "}";
        for(auto t:grammar[transitionIndex]) {
            string tempName = string("[") + to_string(transitionIndex) + ">.";
            for(auto tt:t) if(tt != -1) tempName += string(" ") + to_string(tt);
            tempName += string(" ") + nextAlphaString + "]";
            EnkaNode *newNode = (EnkaNode*)EnkaNodeFactory(tempName);
            add(-1, newNode);
        }
    }
};
map<pair<int, int>, EnkaNode*> hashNodes;

void *EnkaNodeFactory(string name) {
    pair<int, int> dh = doubleHash(name);
    auto it = hashNodes.find(dh);
    if(it != hashNodes.end()) return it->second;
    EnkaNode *temp = new EnkaNode(name);
    hashNodes[dh] = temp;
    temp->createTransitions();
    return temp;
}

void *DkaNodeFactory(vector<EnkaNode*> &v);


struct DkaNode {
    string name;
    vector<pair<int, DkaNode*>> neighbours;
    int id = 0;
    DkaNode(string name) : name(name) {this->id = dkaIndexCounter++;}
    void generateNeighbours(vector<EnkaNode*> v) {
        vector<EnkaNode*> eEnvironOriginal;
        for(auto t:v) t->eEnvironment(eEnvironOriginal, been);
        for(auto t:eEnvironOriginal) been[t->id] = false;
        for(int i = 0; i < n; i++) {
            vector<EnkaNode*> newTransition;
            for(auto t:eEnvironOriginal) {
                for(auto tt:t->neighbours) {
                    if(tt.first == i) {
                        tt.second->eEnvironment(newTransition, been);
                    } 
                }
            }
            for(auto t:newTransition) been[t->id] = false;
            if((int)newTransition.size()) neighbours.push_back({i, (DkaNode*) DkaNodeFactory(newTransition)});
        }
    }
    friend ostream& operator<<(ostream& os, const DkaNode& obj) {
        os << obj.name << " ";
        for(auto t:obj.neighbours) os << "(" << t.first-0 << ":" << t.second->name << ") ";
        return os;
    }
};

map<pair<int, int>, DkaNode*> allDkaNodes;

void *DkaNodeFactory(vector<EnkaNode*> &v) {
    vector<pair<int, string> > comp;
    int nameHash1 = 0, nameHash2 = 0;
    for(auto t:v) comp.push_back({t->id, t->name});
    sort(comp.begin(), comp.end());
    for(auto t:comp) {
        nameHash1 = ((nameHash1 * BASE1)%MOD1 + t.first)%MOD1;
        nameHash2 = ((nameHash2 * BASE2)%MOD2 + t.first)%MOD2;
    }       
    auto it = allDkaNodes.find({nameHash1, nameHash2});
    if(it != allDkaNodes.end()) return it->second;
    string name = "{";
    for(int i = 0; i < (int)comp.size(); i++) {
        name += comp[i].second;
        if(i != (int)comp.size() - 1) name += ",";
    }
    name += "}";
    DkaNode *original = new DkaNode(name);
    allDkaNodes[{nameHash1, nameHash2}] = original;
    original->generateNeighbours(v);
    return original;
}



int main() {
    ofstream file("analizator/lrparsertablica.txt");
    string s = "";
    int parentIndex = -1;
    int lineCounter = 0;
    while(getline(cin, s)) {
        lineCounter++;
        if(s[0] == '%' && s[1] == 'V') {
            int id = 3;
            s += ' ';
            while(id < (int)s.size()) {
                int nextId = s.find(' ', id);
                string tempName = s.substr(id, nextId - id);
                id = nextId + 1; 
                alphabet.push_back(tempName);
                index[tempName] = currentCounter;
                currentCounter++;
            }   
            for(int i = 0; i < currentCounter; i++) grammar.push_back(tempVector);
            m = terminalCutoff = currentCounter;
            
        } else if(s[0] == '%' && s[1] == 'T') {
            int id = 3;
            s += ' ';
            while(id < (int)s.size()) {
                int nextId = s.find(' ', id);
                string tempName = s.substr(id, nextId - id);
                id = nextId + 1; 
                alphabet.push_back(tempName);
                index[tempName] = currentCounter;
                currentCounter++;
            } 
        } else if(s[0] == '%' && s[1] == 'S') {
            int id = 5;
            s += ' ';
            while(id < (int)s.size()) {
                int nextId = s.find(' ', id);
                string tempName = s.substr(id, nextId - id);
                id = nextId + 1; 
                syncSymbols.push_back(tempName);
            } 
        } else {
            if(s[0] != ' ') {
                parentIndex = index[s];
            }
            else if(s[1] == '$') {
                grammar[parentIndex].push_back(tempTempVector);
                grammar[parentIndex].back().push_back(-1);
                reductionPriority[alphabet[parentIndex] + " -> "] = lineCounter;
            } else {
                grammar[parentIndex].push_back(tempTempVector);
                int id = 1;
                reductionPriority[alphabet[parentIndex] + " -> " + s.substr(1, s.size() - 1)] = lineCounter;
                s += ' ';
                while(id < (int)s.size()) {
                    int nextId = s.find(' ', id);
                    string tempName = s.substr(id, nextId - id);
                    id = nextId + 1; 
                    grammar[parentIndex].back().push_back(index[tempName]); 
                }   
            }
        }
    }
    n = currentCounter;
    while((int)zapocinje.size() < n) zapocinje.push_back(tempTempVector);
    while((int)isEmptyArray.size() < n) isEmptyArray.push_back(0);
    tempTempVector.clear();
    while((int)tempTempVector.size() < n) tempTempVector.push_back(0);
    while((int)zapocinjeZnakom.size() < n)  zapocinjeZnakom.push_back(tempTempVector);

    fillEmptySymbols();
    
    fillZapocinje();
    

    EnkaNode *startingNode = new EnkaNode("[-1>. 0 {-1}]");
    startingNode->createTransitions();
    for(int i = 0; i <= indexCounter; i++) been.push_back(0);
    vector<EnkaNode*> temp;
    startingNode->eEnvironment(temp, been);
    for(auto t:temp) been[t->id] = false;
    DkaNodeFactory(temp);
    
    for(auto t:allDkaNodes) { 
        auto dkan = t.second;
        for(int j = 0; j < n; j++) {
            for(auto t:dkan->neighbours) if(t.first == j) {
                lrTable[string("(") + to_string(dkan->id) + ", " + alphabet[j] + ")"] = {-1, to_string(t.second->id)};
            }
        } 
        int id = 2;
        string name = dkan->name;
        while(id < (int)name.size()) {
            string transitionName = "";
            int nextId = name.find(']', id) + 1;
            string express = name.substr(id, nextId - id - 1);
            int bid = express.find('{');
            if(express[bid - 2] == '.') {
                if(express[0] == '-') {
                    transitionName += string("(") + to_string(dkan->id) + ", stackend)";
                    acceptString = transitionName;
                    transitionName = "";
                    id = nextId + 2;
                    continue;
                }
                int iid = 0;
                iid = express.find('>');
                string reductionString = alphabet[stoi(express.substr(0, iid))] + " ->";
                iid++;
                while(express[iid] != '.') {
                    int nextIid = express.find(' ', iid);
                    reductionString += string(" ") + alphabet[stoi(express.substr(iid, nextIid - iid))];
                    iid = nextIid + 1;
                }
                string alpha = express.substr(bid + 1, express.size() - bid - 2);
                alpha += " ";
                iid = 0;
                while(iid < (int)alpha.size()) {
                    int nextIid = alpha.find(' ', iid);
                    int val = stoi(alpha.substr(iid, nextIid - iid));
                    transitionName += string("(") + to_string(dkan->id) + ", ";
                    if(val == -1) transitionName += "stackend)";
                    else transitionName += alphabet[val] + ")";
                    auto it = lrTable.find(transitionName);
                    if(it == lrTable.end() || it->second.first > reductionPriority[reductionString]) {
                        lrTable[transitionName] = {reductionPriority[reductionString], reductionString};  
                    }
                    transitionName = ""; 
                    iid = nextIid + 1;
                }
            }
            id = nextId + 2;
            
        }
    }
    for(auto t:syncSymbols) file << t << " ";
    file << '\n';
    file << acceptString << " => Prihvati\n";
    for(auto t:lrTable) file << t.first << " => " << (t.second.first >= 0 ? "Reduciraj: ":(t.first[t.first.size()-2] == '>' ? "Stavi(":"Pomakni(")) <<t.second.second << (t.second.first >= 0?"":")") << '\n';
    file.close();
}