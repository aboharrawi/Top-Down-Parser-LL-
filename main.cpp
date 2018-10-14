#include "utilities.h"
void parseGrammar(string txt)
{
	int index = 0;//the index from where to start
	text tokens;//token vector
	string head;// to store the non terminal symbol for constructing later
	///grammar is constructed as this 
	///grammar {key : string , value : <vector<vector<string>> }
	///value { nontermonal symbol -> array of terminal symbols }

	tokens = split(txt, "\\s+");//split grammar into tokens

	while (index < tokens.size()){
		if (index + 1 < tokens.size() && tokens[index + 1] == "->") // if it started by nonterminal 
		{
			head = tokens[index];//head is the non terminal
			index += 2;//move next to ->
			book b(1);
			grammar[head] = b;
			nonterminals.push_back(head);
		}
		else if (tokens[index] == "|") // if it has another production
		{
			text str;
			grammar[head].push_back(str);//add the tokens into this grammar[head] 
			index += 1;
		}
		else {
			terminals.insert(tokens[index]);
			grammar[head][grammar[head].size() - 1].push_back(tokens[index]);
			index += 1;
		}
	}

	for (int i = 0; i < nonterminals.size(); i++){
		if (find_(terminals, nonterminals[i]) != terminals.end())//found
			terminals.erase(nonterminals[i]);
	}
}
table eliminateLeftRecursion(){

	int j, k, i, l;
	book extended;//new book for extracting and replacing the old production
	text keys;//all nonterminals
	bool hasDirectRec;
	string newnonterm;

	keys = nonterminals;//get all nonterminals
	for (i = 0; i < keys.size(); i++){
		//here we can do the indirect left recursion and 
		//keep doing this untill reaching the direct left recursion
		for (j = 0; j < i; j++){
			extended.clear();
			for (k = 0; k < grammar[keys[i]].size(); k++){
				if (grammar[keys[i]][k].size() > 0 && grammar[keys[i]][k][0] == keys[j]) //if it has left recursion
				{
					for (l = 0; l < grammar[keys[j]].size(); l++){
						text toadd, tmp;

						for (int txr = 0; txr < grammar[keys[j]][l].size(); txr++)
							toadd.push_back(grammar[keys[j]][l][txr]);
						tmp = getRange(grammar[keys[i]][k], 1, grammar[keys[i]][k].size());

						for (int cnt = 0; cnt < tmp.size(); cnt++)
							toadd.push_back(tmp[cnt]);
						extended.push_back(toadd);
					}
				}
				else if (grammar[keys[i]][k].size() > 0)
					extended.push_back(grammar[keys[i]][k]);
			}
			grammar[keys[i]] = extended;
		}
		hasDirectRec = false;
		for (k = 0; k < grammar[keys[i]].size(); k++) {
			if (grammar[keys[i]][k].size() > 0 && grammar[keys[i]][k][0] == keys[i]) {
				//it has direct left recursion
				hasDirectRec = true;
				break;
			}
		}
		int c = i;
		if (hasDirectRec) {

			newnonterm = keys[i] + "\'";//create the new nonterminal
			while (grammar.count(newnonterm)) {
				newnonterm += "\'";//keep adding ' if it is found in the grammar
				i++;
			}
			nonterminals.insert(find(nonterminals.begin(), nonterminals.end(), keys[i]) + 1, newnonterm);
			grammar[newnonterm] = book();
			for (j = 0, k = 0; k < grammar[keys[i]].size(); k++) {
				if (grammar[keys[i]][k].size() > 0) {
					if (grammar[keys[i]][k][0] == keys[i]){
						text toadd;
						toadd = getRange(grammar[keys[i]][k], 1, grammar[keys[i]][k].size());//get all after the nonterminal
						toadd.push_back(newnonterm);//push all 
						grammar[newnonterm].push_back(toadd);
					}
					else
					{
						if (grammar[keys[i]][k].size() == 1 && grammar[keys[i]][k][0] == "epsilon")//if epsilon found
						{
							grammar[keys[i]][k].clear();
							grammar[keys[i]][k].push_back(newnonterm);
						}
						else{
							grammar[keys[i]][k].push_back(newnonterm);
						}
						grammar[keys[i]][j] = grammar[keys[i]][k];//replace the old production with the new one
						j++;
					}
				}
			}
			book toadd;
			toadd = getRange(grammar[keys[i]], 0, j);
			grammar[keys[i]] = toadd;
			text ltt;
			ltt.push_back("epsilon");
			grammar[newnonterm].push_back(ltt);//add the production and epsilon at the end
		}
	}
	return grammar;
}
boolmap getEOF()
{
	boolmap eofs;
	int i, k, j;
	text keys = nonterminals;
	for (i = 0; i < keys.size(); i++) {
		for (j = 0; j < grammar[keys[i]].size(); j++) {
			for (k = 0; k < grammar[keys[i]][j].size(); k++) {
				if (grammar.count(grammar[keys[i]][j][k]) == 0) {
					eofs[grammar[keys[i]][j][k]] = false;
				}
			}
		}
	}
	if (eofs.count("epsilon"))
		eofs["epsilon"] = true;
	text empty;
	for (i = 0; i < keys.size(); i++){
		empty.clear();
		calcRecEOFS(keys[i], empty, eofs);
	}
	return eofs;
}
dict calcFirsts(boolmap &e) {

	int i, j, k;
	boolmap	eofs = e;
	dict firsts;
	text keys = nonterminals;
	bool done = false;
	for (i = 0; i < keys.size(); i++) {
		for (j = 0; j < grammar[keys[i]].size(); j++) {
			for (k = 0; k < grammar[keys[i]][j].size(); k++) {
				if (!grammar.count(grammar[keys[i]][j][k])){
					firsts[grammar[keys[i]][j][k]].clear();
					firsts[grammar[keys[i]][j][k]].push_back(grammar[keys[i]][j][k]);
				}
			}
		}
	}
	text p;
	while (!done) {
		done = true;
		for (i = 0; i < keys.size(); i++) {
			p.clear(), calcFirstRec(keys[i], p, firsts, eofs, done);
		}
	}
	for (i = 0; i < keys.size(); i++)
		sort(firsts[keys[i]].begin(), firsts[keys[i]].end());

	return firsts;
}
dict calcFollows(boolmap &eofs, dict &firsts) {
	int i;
	dict follows;
	bool done = false;
	text keys = nonterminals;
	for (i = 0; i < keys.size(); i++) {
		if (i == 0)
			follows[keys[i]].push_back("eof");
		else
			follows[keys[i]] = text();
	}
	text path;
	while (!done) {
		done = true;
		for (i = 0; i < keys.size(); i++) {
			path.clear();
			calcFollow(keys[i], path, firsts, follows, eofs, done);
		}
	}
	for (i = 0; i < keys.size(); i++)
		sort(follows[keys[i]].begin(), follows[keys[i]].end());
	return follows;
}
parse parsingTable(boolmap &eofs, dict &firsts, dict &follows) {
	int i, j, k, l;
	text first, follow;
	text keys = nonterminals;
	parse ptable;
	for (i = 0; i < keys.size(); i++) {
		for (j = 0; j < grammar[keys[i]].size(); j += 1) {
			for (k = 0; k < grammar[keys[i]][j].size(); k += 1) {
				first = firsts[grammar[keys[i]][j][k]];
				for (l = 0; l < first.size(); l += 1){
					if (first[l] != "epsilon"){
						ptable[keys[i]][first[l]] = i;
					}
				}
				if (!eofs[grammar[keys[i]][j][k]])
					break;
			}
			if (k == grammar[keys[i]][j].size()) {
				follow = follows[keys[i]];
				for (l = 0; l < follow.size(); l += 1)
					ptable[keys[i]][follow[l]] = i;
			}
		}
	}
	return ptable;
}
dict calculateFirstPlus(dict &firsts, dict &follows)
{
	dict firstPlus;
	for (auto i : firsts){
		if (find_(i.second, "epsilon") == i.second.end())
			firstPlus[i.first] = firsts[i.first];
		else{
			set<string> temp;
			for (int z = 0; z < firsts[i.first].size(); z++)
				temp.insert(firsts[i.first][z]);//firsts + epsilon

			for (int z = 0; z < follows[i.first].size(); z++)
				temp.insert(follows[i.first][z]);//follow + epsilon
			temp.erase(find_(temp, "epsilon"));

			for (auto z : temp)
				firstPlus[i.first].push_back(z);
		}
	}
	return firstPlus;
}
parse calcFP(dict &firsts, dict& follows)
{
	parse fp;
	int c = 0;
	for (auto i : nonterminals){
		for (int z = 0; z < grammar[i].size(); z++){
			if (find_(firsts[grammar[i][z][0]], "epsilon") == firsts[grammar[i][z][0]].end()){
				for (int j = 0; j < firsts[grammar[i][z][0]].size(); j++)
					fp[i][firsts[grammar[i][z][0]][j]] = c;
			}
			else
			{
				for (int j = 0; j < follows[i].size(); j++)
					fp[i][follows[i][j]] = c;
				for (int j = 0; j < firsts[grammar[i][z][0]].size(); j++)
					fp[i][firsts[grammar[i][z][0]][j]] = c;
			}
			c++;
		}
	}
	return fp;
}
void readFromUser(parse skeleton)
{
	string statement;
	string focus;
	stack<string> stk;
	string word;
	getline(cin, statement, '\n');
	text tokens;
	tokens = split(statement, "\\s+");
	tokens.push_back("eof");
	int index = 0;
	word = tokens[index];
	stk.push("eof");
	stk.push(nonterminals[0]);

	focus = stk.top();
	while ((true)){
		if (focus == "eof" && word == "eof"){
			cout << "success" << endl;
			return;
		}
		else if ((find_(terminals, focus) != terminals.end()) || focus == "eof"){
			if (focus == word){
				stk.pop();
				word = tokens[++index];
			}
			else{
				cout << "error" << endl;
				return;
			}
		}
		else{
			if ((skeleton[focus].count(word) != 0) && (skeleton[focus][word] != -1)){
				stk.pop();
				text txt = getproductionlines(skeleton[focus][word]);
				for (int i = txt.size() - 1; i >= 0; i--)
				if (txt[i] != "epsilon")
					stk.push(txt[i]);
			}
			else{
				cout << "Error" << endl;
				return;
			}
		}
		focus = stk.top();
	}
}

int main()
{
	ofstream os("elemenatedLR.txt");
	string str = "";
	readGrammar(str, "grammar.txt");
	cout << str << endl;
		
	parseGrammar(str);
	eliminateLeftRecursion();


	string lines = Readable(grammar);
	os << lines << endl;

	lineVector();

	boolmap eofs = getEOF();
	dict firsts = calcFirsts(eofs);
	dict follows = calcFollows(eofs, firsts);
	printFirst(firsts);
	cout << endl;
	printFollow(follows);
	cout << endl;

	
	parse sk = calcFP(firsts, follows);
	printPT(sk);
	parse temp;

	for (auto i : nonterminals)
	for (auto j : terminals)
		temp[i][j] = -1;

	for (auto i : sk)
	for (auto j : i.second){
		temp[i.first][j.first] = j.second;
	}
	readFromUser(temp);
}