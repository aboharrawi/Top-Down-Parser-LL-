#pragma warning(disable : 4996)  
#pragma warning(disable : 4018)  
#pragma warning(disable : 4996)  

#include <iostream>
#include <iomanip>
#include <vector>
#include <string>
#include <string.h>
#include <list>
#include <map>
#include <regex>
#include <fstream>
#include <ostream>
#include <algorithm>
#include <unordered_map>
#include <set>
#include <unordered_set>
#include <stack>
#include <sstream>
#include <ostream>
#include <fstream>
using namespace std;

#define find_(a,b)std::find(a.begin(),a.end(),b)


typedef vector<string> text;
typedef vector<text> book;
typedef map<string, book> table;
typedef map<string, bool> boolmap;
typedef map<string, text> dict;
typedef map<string, map<string,int>> parse;

table grammar;
text nonterminals,lines;
set<string> terminals;
map<int, vector<string>> mping;//mapping for first+ with its line number
int linesnum;

void readGrammar(string &t, string filename)
{
	string str;
	ifstream is(filename);
	while (true){
		getline(is, str, '\n');
		if (is.eof() || str == "\n")
			break;
		t += str + '\n';
	}
}
void printFirst(dict &d)
{
	dict::iterator it;
	for (it = d.begin(); it != d.end(); it++){
		cout << "First of " << it->first << " { ";
		for (int i = 0; i < it->second.size(); i++){
			cout << d[it->first][i];
			if (i != it->second.size() - 1)
				cout << " ,";

		}
		cout << " }" << endl;
	}
}
void printFollow(dict &d)
{
	dict::iterator it;
	for (it = d.begin(); it != d.end(); it++){
		cout << "Follow of " << it->first << " { ";
		for (int i = 0; i < it->second.size(); i++){
			cout << d[it->first][i];
			if (i != it->second.size() - 1)
				cout << " ,";

		}
		cout << " }" << endl;
	}
}
void printFirstPlus(dict &d)
{
	dict::iterator it;
	for (it = d.begin(); it != d.end(); it++){
		cout << "First+ of " << it->first << " { ";
		for (int i = 0; i < it->second.size(); i++){
			cout << d[it->first][i];
			if (i != it->second.size() - 1)
				cout << " ,";

		}
		cout << " }" << endl;
	}
}
void printParsingTable(parse &parseTable)
{
	for (auto i : parseTable){
		cout << i.first << " ";
		for (auto j : i.second)
			cout << j.second << "\t";
		cout << endl;
	}
}
text split(const string& input, const string& reg)
{
	regex re(reg);
	sregex_token_iterator first{ input.begin(), input.end(), re, -1 }, last;
	return{ first, last };
}
text getAllKeys(table &grammar)
{
	text keys;
	for (auto i : grammar)
		keys.push_back(i.first);
	return keys;
}
template<class T>
T getRange(T oldtxt, int f, int t)
{
	T temp;
	for (int i = f; i < t; i++)
		temp.push_back(oldtxt[i]);

	return temp;
}
string space(int num)
{
	string s = "";
	while (num > 0){
		s += ' ';
		num--;
	}
	return s;
}
string Readable(table &grammar) {
	linesnum = 0;
	int i, j, max = 0;
	string pretty = "";
	text keys = nonterminals;
	for (size_t i = 0; i < keys.size(); i++)
	if (keys[i].length() > max)
		max = keys[i].length();

	for (i = 0; i < keys.size(); i += 1) {
		for (j = 0; j < grammar[keys[i]].size(); j++) {
			if (j == 0) {
				pretty += space(max - keys[i].length());
				pretty += keys[i];
				pretty += " -> ";
			}
			else {
				pretty += space(max);
				pretty += " | ";
			}
			for (int tt = 0; tt < grammar[keys[i]][j].size(); tt++)
			{
				pretty += grammar[keys[i]][j][tt];
				if (tt != grammar[keys[i]][j].size() - 1)
					pretty += " ";
			}
			pretty += '\n';
			linesnum++;
		}
	}
	return pretty;
}
int getIndex(text &p, string &key)
{
	for (size_t i = 0; i < p.size(); i++)
	if (p[i] == key)
		return i;
	return -1;
}
bool calcRecEOFS(string &key, text &path, boolmap &eofs) {
	int i, j;
	if (getIndex(path, key) >= 0) {
		return true;
	}
	path.push_back(key);
	if (eofs.count(key) != 0) {
		return eofs[key];
	}
	for (i = 0; i < grammar[key].size(); i++) {
		for (j = 0; j < grammar[key][i].size(); ++j) {
			if (!calcRecEOFS(grammar[key][i][j], path, eofs)) {
				break;
			}
		}
		if (j == grammar[key][i].size()) {
			eofs[key] = true;
			return true;
		}
	}
	eofs[key] = false;
	return false;
}
text calcFirstRec(string key, text &path, dict &firsts, boolmap &eofs, bool &done) {
	int i, j, k;
	text first;
	if (grammar.count(key) == 0)
		return firsts[key];
	if (getIndex(path, key) != -1)
		return firsts[key];
	path.push_back(key);
	if (firsts.count(key) == 0) {
		firsts[key] = text();
		done = false;
	}
	for (i = 0; i < grammar[key].size(); i++) {
		for (j = 0; j < grammar[key][i].size(); j++) {
			first = calcFirstRec(grammar[key][i][j], path, firsts, eofs, done);
			for (k = 0; k < first.size(); k++) {
				if (getIndex(firsts[key], first[k]) == -1) {
					firsts[key].push_back(first[k]);
					done = false;
				}
			}
			if (!eofs[grammar[key][i][j]]) {
				break;
			}
		}
	}
	return firsts[key];
}
void calcFollow(string key, text &path, dict &firsts, dict& follows, boolmap &eofs, bool &done) {
	int i, j, k, l;
	string mid;
	text first;
	for (i = 0; i < grammar[key].size(); i++) {
		for (j = 0; j < grammar[key][i].size(); j++) {
			mid = grammar[key][i][j];
			if (grammar.count(mid)) {
				for (k = j + 1; k < grammar[key][i].size(); k++) {
					first = firsts[grammar[key][i][k]];
					for (l = 0; l < first.size(); l++) {
						if (first[l] != "epsilon" && getIndex(follows[mid], first[l]) == -1) {
							follows[mid].push_back(first[l]);
							done = false;
						}
					}
					if (!eofs[grammar[key][i][k]]) {
						break;
					}
				}
				if (k == grammar[key][i].size()) {
					for (l = 0; l < follows[key].size(); l++) {
						if (getIndex(follows[mid], follows[key][l]) < 0) {
							follows[mid].push_back(follows[key][l]);
							done = false;
						}
					}
				}
			}
		}
	}
}
void lineVector()
{
	string ll = Readable(grammar);
	istringstream iss(ll);
	string str;
	for (int i = 0; i < linesnum; i++){
		getline(iss, str);
		lines.push_back(str);
		str = "";
	}
}

int findpos(string str)
{
	for (int i = 0; i < lines.size(); i++)
		if (lines[i].find(str) != string::npos)
			return i;
	return -1;
}

void printPT(parse pt)
{
	ofstream os("skeletonTable.txt");
	parse temp;
	terminals.insert("eof");
	if (find_(terminals, "epsilon") != terminals.end())
		terminals.erase(find_(terminals, "epsilon"));

	for (auto i:nonterminals)
		for (auto j : terminals)
			temp[i][j] = -1;

	for (auto i : pt){
		for (auto j : i.second){
			temp[i.first][j.first] = j.second;
		}
	}
	os << "\t"+space(6);
	for (auto i : terminals)
		os << fixed << i << setw(8);
	os << endl;
	for (auto i : nonterminals){
		os << i<< "::"<<fixed<<setw(5);
		for (auto j : terminals){
			if (temp[i][j] == -1)
				os <<"-"<< setw(8);
			else
				os << fixed<<temp[i][j] << setw(8);
		}
		os << endl;
	}
}

void mappinglinefp(parse pt)
{
	for (auto i : pt)
		for (auto j : i.second)
			mping[j.second].push_back(j.first);
}
void ppap()//print 
{
	cout << "\n\n" << endl;
	for (int i = 0; i < linesnum; i++)
	{
		cout << i << ": ";
		for (auto j : mping[i])
			cout << j << " ";
		cout << endl;
	}
}
text getproductionlines(int linenum)
{
	int c = 0;
	for (auto i:nonterminals){
		for (int x = 0; x < grammar[i].size(); x++,c++){
			if (c == linenum){
				return grammar[i][x];
			}
		}
	}
}