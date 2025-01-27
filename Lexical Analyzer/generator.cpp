#include<iostream>
#include<string>
#include<vector>
#include<map>
#include<algorithm>
#include<fstream>
#define breturn return
using namespace std;
const int MOD1 = 1e9 + 7;
const int BASE1 = 31337;
const int MOD2 = 1e9 + 3;
const int BASE2 = 31259;

int priorityCounter = 0;
int indexCounter = 0;
int dkaShortenNamesCounter = 0;
map<string, string> regices;
vector<string> operators;
vector<void*> allNodes;
vector<bool> been;
string actualStartingNode;


void expandRegex(string &regex) {
    string temp = "", nam = "";
    bool inName = false;
    for(int i = 0; i < (int)regex.size(); i++) {
        auto t = regex[i];
        if(t == '\\') {
            temp += t;
            temp += regex[i + 1];
            i++;
            continue;
        }
        if(t == '{') {
            nam = "";
            inName = true;
            temp += '(';
        } else if(t == '}') {
            for(auto tt:regices[nam]) temp += tt;
            inName = false;
            temp += ')';
        } else if(inName) 
            nam += t;
        else temp += t;
    }
    regex = temp;
}


struct EnkaNode {
    string name;
    vector<pair<char, EnkaNode*> > neighbours;
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
    void add(char c, EnkaNode *n) {
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
        for(auto t:this->neighbours) if(t.first == 0) t.second->eEnvironment(envir, been);
    }
};

void *createOriginalDkaNode(vector<EnkaNode*> &v);

struct DkaNode {
    string name;
    vector<pair<char, DkaNode*>> neighbours;
    DkaNode(string name) : name(name) {}
    void generateNeighbours(vector<EnkaNode*> v) {
        vector<EnkaNode*> eEnvironOriginal;
        for(auto t:v) t->eEnvironment(eEnvironOriginal, been);
        for(auto t:eEnvironOriginal) been[t->id] = false;
        for(int i = 1; i < 128; i++) {
            vector<EnkaNode*> newTransition;
            for(auto t:eEnvironOriginal) {
                for(auto tt:t->neighbours) {
                    if(tt.first == i) {
                        tt.second->eEnvironment(newTransition, been);
                    } 
                }
            }
            for(auto t:newTransition) been[t->id] = false;
            if((int)newTransition.size()) neighbours.push_back({i, (DkaNode*) createOriginalDkaNode(newTransition)});
        }
    }
    friend ostream& operator<<(ostream& os, const DkaNode& obj) {
        os << obj.name << " ";
        for(auto t:obj.neighbours) os << "(" << t.first-0 << ":" << t.second->name << ") ";
        return os;
    }
};

map<pair<int, int>, DkaNode*> allDkaNodes;


void shortenDkaNodeNames() {
    for(auto t:allDkaNodes) {
        string &s = t.second->name;
        bool startingNode = false;
        for(int i = 0; i < (int)s.size(); i++) {
            if(s[i] == '[') {
                int id = s.find(']', i);
                string tempName = s.substr(i, id - i + 1);
                if(tempName[3] == 'S' && tempName[4] == '_') startingNode = true; 
                i = id;
            }
        }
        string shortName = (startingNode?"{":string("{[0,q") + to_string(++dkaShortenNamesCounter)+"]");
        for(int i = 0; i < (int)s.size(); i++) {
            if(s[i] == '[') {
                int id = s.find(']', i);
                if(id < (int)s.size() - 2 && s[id + 1] == '}' && s[id + 2] == ',') id = s.find(']', id + 1);
                string tempName = s.substr(i, id - i + 1);
                if((tempName[3] == 'S' && tempName[4] == '_') || tempName[1] == '1') shortName += (startingNode?"":string(",")) + tempName;
                i = id;
            }
        }
        shortName += "}";
        s = shortName;
    }
}

void *createOriginalDkaNode(vector<EnkaNode*> &v) {
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



map<string, EnkaNode*> startingNodes;

void generateBrackets(string &regex, vector<int> &brackets) {
    vector<int> stack;
    while(brackets.size() < regex.size()) brackets.push_back(0);
    for(int i = 0; i < (int)regex.size(); i++) {
        if(regex[i] == '\\') {
            i++;
            continue;
        }
        if(regex[i] == '(') stack.push_back(i);
        if(regex[i] == ')') {
            brackets[stack.back()] = i + 1; 
            stack.pop_back();
        }
    }
}


//regex -> regex koji se parsira, [x,y> -> interval u kojem se parsira 
void parseRegex(string &regex, vector<int> &brackets, int x, int y, EnkaNode *startNode, EnkaNode *endNode) {
    EnkaNode *regexBegin = startNode;
    EnkaNode *regexEnd = endNode;
    EnkaNode *lastNode = regexBegin;
    bool specialChar = false;
    for(int i = x; i < y; i++) {
        if((regex[i] == '\\' || regex[i] == '*') && !specialChar) {
            if (regex[i] == '\\') specialChar = true;
            continue;
        }
        if(regex[i] == '(' && !specialChar) {
            EnkaNode *startrNode = new EnkaNode();   
            EnkaNode *endrNode = new EnkaNode();   
            lastNode->add(0, startrNode);
            if(regex[brackets[i]] == '*') {
                lastNode->add(0, endrNode);
                endrNode->add(0, startrNode);
            }
            parseRegex(regex, brackets, i + 1, brackets[i] - 1, startrNode, endrNode);
            i = brackets[i] - 1;
            lastNode = endrNode;           
        } else if((regex[i] == '|' || regex[i] == ')') && !specialChar) {
            lastNode->add(0, regexEnd);
            lastNode = regexBegin;
        }  else {
            EnkaNode *newNode = new EnkaNode();   
            if(regex[i] == '$' && !specialChar) lastNode->add(0, newNode);
            else if(specialChar) {
                if(regex[i] == 'n') lastNode->add(10, newNode);
                else if(regex[i] == 't') lastNode->add(9, newNode);
                else if(regex[i] == '_') lastNode->add(32, newNode);
                else lastNode->add(regex[i], newNode);
            }
            else lastNode->add(regex[i], newNode);
            if(regex[i + 1] == '*') {
                EnkaNode *newNode2 = new EnkaNode();
                lastNode->add(0, newNode);
                newNode->add(0, lastNode);
                newNode->add(0,newNode2);
                newNode = newNode2;
            }
            lastNode = newNode;
        }
        specialChar = false;
    }
    lastNode->add(0, regexEnd);
}

int main() {
    bool action = false;
    string s;
    EnkaNode *lastActionFinal;
    bool noviRedak = false;
    int vratiSe = 0;
    string udjiUStanje = "";
    string lJedinka = "";
    while(getline(cin, s)) {
        if(s[0] == '{' && !action) {
            int id = s.find('}');
            string name = s.substr(1, id - 1);
            string regex = s.substr(id + 2);
            expandRegex(regex);
            regices[name] = regex;
        } else if(s[0] == '%' && s[1] == 'X') {
            s += ' ';
            int id = 3, nextId = -1;
            while(id < (int)s.size()) {
                nextId = s.find(' ', id);
                string name = s.substr(id, nextId - id);
                EnkaNode *startingNode = new EnkaNode(string("[0,") + name + "]");
                startingNodes[name] = startingNode;
                if(id == 3) actualStartingNode = startingNode->name;
                id = nextId + 1;
            }
        } else if(s[0] == '%' && s[1] == 'L') {
            s += ' ';
            int id = 3, nextId = -1;
            while(id < (int)s.size()) {
                nextId = s.find(' ', id);
                string name = s.substr(id, nextId - id);
                operators.push_back(name);
                id = nextId + 1;
            }
        } else if(s[0] == '<') {
            action = true;
            int id = s.find('>');
            string name = s.substr(1, id - 1);
            EnkaNode *startingNode = startingNodes[name];
            EnkaNode *regexBeginNode = new EnkaNode();   
            startingNode->add(0, regexBeginNode);
            lastActionFinal = new EnkaNode();
            string actionRegex = s.substr(id + 1);
            vector<int> brackets;
            udjiUStanje = name;
            expandRegex(actionRegex);
            generateBrackets(actionRegex, brackets);
            parseRegex(actionRegex, brackets, 0, actionRegex.size(), regexBeginNode, lastActionFinal);
        } else if(s[0] == '-') {
            continue;
        } else if(s[0] == '{') {
            vratiSe = -1;
            noviRedak = false;
            lJedinka = "";
        } else if(s[0] == '}') {
            lastActionFinal->name = string("[1,") + to_string(++priorityCounter) + "," + lJedinka + ",{[0," + udjiUStanje + "]}," + to_string(noviRedak) + "," + to_string(vratiSe) + "]"; 
            action = false;
        } else {
            int id = s.find(' ');
            if(id != -1) {
                string name = s.substr(0, id);
                string value = s.substr(id + 1);
                if(name == "VRATI_SE") vratiSe = stoi(value);
                else if(name == "UDJI_U_STANJE") udjiUStanje = value;
            } else {
                if(s == "NOVI_REDAK") noviRedak = true;
                else lJedinka = s;
            }
        }
    }
    while((int)been.size() <= indexCounter) been.push_back(false);
    vector<EnkaNode*> temp;
    for(auto t:startingNodes) {
        EnkaNode tempNode = *(t.second);
        tempNode.eEnvironment(temp, been);
        for(auto t:temp) been[t->id] = false;
        createOriginalDkaNode(temp);
        temp.clear();
    }    
    shortenDkaNodeNames();
    ofstream file("analizator\\dka.txt");

    for(auto t:allDkaNodes) if(t.second->name.substr(1,t.second->name.size()-2) == actualStartingNode) file << *t.second << '\n';    
    for(auto t:allDkaNodes) if(t.second->name.substr(1,t.second->name.size()-2) != actualStartingNode) file << *(t.second) << '\n';

    file.close();
}