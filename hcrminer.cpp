/******* Author: Akshay Kulkarni ************/

#include<bitset>
#include<ctime>
#include<sys/time.h>
#include<cassert>
#include<iostream>
#include<unordered_map>
#include<sstream>
#include<string>
#include<queue>
#include<map>
#include<vector>
#include<set>
#include<algorithm>
#include<cstdio>
using namespace std;

typedef pair<int,int> ii;
typedef unordered_map<int, vector<int> > ump;

int association_rules;
map< pair< set<int>, set<int> > , int > rules;
vector< vector<int> > answer;
int tid,iid,total_items,N,support_count,options,minsup;
double minconf;
vector< vector<int> > lhs,rhs;
vector< int > sups,only_sups;
vector< double> confs;
map< set<int>,int > sp_count;

void clear()
{
	for(int i=0;i<answer.size();i++)
		answer[i].clear();
	rules.clear();
	sp_count.clear();
	association_rules=0;
	only_sups.clear();
}

//Below two are compare functions for sorting elements based on their frequency
bool my_cmp_asc( ii i1, ii i2 ){ return i2.second > i1.second;}

bool my_cmp_desc( ii i1, ii i2 ){ return i2.second < i1.second;}

void printFrequentItems()
{
	for(int i=0;i<answer.size();i++)
	{
		for(int j=0;j<answer[i].size();j++)
			cout << answer[i][j] << " ";
		cout << endl;
	}
}

/*
Parameters:- Input File Name, Adjacency List
This functions takes input a input file name consisting of transaction ids and item ids and zero-size adjacency list.
Function reads the input file and fills adjacency list where each row consists of item belonging to a particular transaction.
*/
void readInput(char *fname,ump &G)
{
	set<int> S;
	FILE *fp = fopen(fname,"r");
	while(fscanf(fp,"%d %d",&tid,&iid)!=EOF)
	{
		if(G.find(tid) == G.end())
		{
			vector<int> items;
			items.push_back(iid);
			G[tid].push_back(iid);
		}
		else G[tid].push_back(iid);
		S.insert(iid);
	}
	N = G.size();
	total_items = S.size();
	fclose(fp);
}

/*
Auxillary function for printing projected DB. Mostly used for debugging
*/

void printDB(ump &G)
{
	for(ump::iterator it = G.begin() ; it!=G.end(); it++ )
	{
		cout << "Transaction id " << it->first << " ";
		for(int i = 0 ; i < (it->second).size();i++)
			cout << (it->second)[i] << " ";
		cout << endl;
	}
	cout << " ======================= " << endl;
}

/*
Parameters:- item,Adjacency List
item -> input for which projected DB is to be generated.
In this function, all transactions for scanned for presence of item. If item is not present, transaction is removed.
If item is present, the transaction is kept but all item lexicographically smaller than or equal to item are removed.
Return:- Function return Projected Database for item.
*/

ump getProjectedDB( int start , ump &G)
{
		ump result;
        vector< int > ::iterator delIt;
		ump::iterator it = G.begin();
		while(it != G.end())
		{
			delIt = lower_bound((it->second).begin(),(it->second).end(),start);
			if( delIt != (it->second).end() && *delIt == start)
            {
						(it->second).erase(delIt);
                        if( (it->second).size() > 0 ) result[it->first] = it->second;
            }
			it++;
		}
        return result;
}

/*
Parameters:- Adjacency List
Function removes all infrequent items i.e item whose frequency is less than minsup.
Return:- This function return vector of pair whose first element is item-id and second element is its frequency
*/

vector< ii > prune(ump &G)
{
	unordered_map< int,int > M;
	vector< int > ::iterator delIt;
	ump::iterator it = G.begin();
	vector<int>::iterator _it;
	while( it != G.end())
	{
		_it = (it->second).begin();
		while(_it != (it->second).end())
		{
			M[*_it]=M[*_it]+1;
			_it++;
		}
		it++;
	}
	
	it = G.begin();
	while( it != G.end())
	{
		_it = (it->second).begin();
		while(_it != (it->second).end())
		{
			if(M[*_it] < minsup ) _it = (it->second).erase(_it);
			else _it++;
		}
		if( 0 == it->second.size()) it = G.erase(it);
		else it++;
	}
	
	vector< ii > result;	
	unordered_map<int,int>::iterator mit = M.begin();
	while(mit!=M.end())
	{
		if(mit->second > minsup) result.push_back(ii(mit->first,mit->second));
		mit++;
	}
	
	if( 1 == options )
        sort(result.begin(),result.end());
    if(2 == options )
        sort(result.begin(),result.end(),my_cmp_asc);
    else
        sort(result.begin(),result.end(),my_cmp_desc);
    
	return result;
}

/*
Parameters:- Adjacency List,Support count vector, vector maintaing current frequent item
This function goes all item in support count vector and recursively generates for projected DB for each of them. During this process, frequent itemset along
with its support count is also maintained. This is useful in association rule mining.
*/

void generateFrequentElements(ump &G,vector< ii > &_sc,vector<int> cur)
{
		if(0 == _sc.size()) return;
		for(int i=0;i<_sc.size();i++)
		{
				cur.push_back(_sc[i].first);
				if( minsup >  20 )
				{
					set<int> current_set(cur.begin(),cur.end());
					sp_count[current_set] = _sc[i].second;
				}
				else only_sups.push_back(_sc[i].second);
				answer.push_back(cur);
				ump projectedDB = getProjectedDB(_sc[i].first,G);
				vector< ii > _tsc = prune(projectedDB);
				generateFrequentElements(projectedDB,_tsc,cur);
				cur.pop_back();
		}
}	

/*
Parameters:- two sets representing elements in left and right hand side of assoication rule and baseupport for entire transaction
This function use breadth first search and confidence based pruning to compute all valid association rule whose confidence is greater than minconf.
*/

void generateRuleUtil(set<int> &assoc_lhs,set<int> &assoc_rhs,int &baseSupport)
{
	queue< pair< set<int> , set<int> > > q;
	int supportLHS = 0;
	supportLHS = sp_count[assoc_lhs];
	if( supportLHS > 0 && (double)baseSupport/supportLHS > minconf)
	{
		rules[make_pair(assoc_lhs,assoc_rhs)] = supportLHS;
		q.push(make_pair(assoc_lhs,assoc_rhs));
	}
	while(!q.empty())
	{
		pair< set<int>,set<int> > P = q.front();
		q.pop();
		pair< set<int>,set<int> > T = P;
		association_rules++;
		vector<int> lhs_rule(P.first.begin(),P.first.end());
		vector<int> rhs_rule(P.second.begin(),P.second.end());
		lhs.push_back(lhs_rule);rhs.push_back(rhs_rule);sups.push_back(baseSupport);confs.push_back((double)baseSupport/supportLHS);
		if( P.first.size() > 1 )
        {
            for(int i=lhs_rule.size()-1;i>=0;i--)
            {
                P.first.erase(P.first.find(lhs_rule[i]));
                P.second.insert(lhs_rule[i]);
				supportLHS = sp_count[P.first];
                if(P.first.size() > 0 && P.second.size() > 0 && rules.find(make_pair(P.first,P.second)) == rules.end() && supportLHS > 0 && (double)baseSupport/supportLHS > minconf)
                {
                    rules[make_pair(P.first,P.second)] = sp_count[P.first];
                	q.push(make_pair(P.first,P.second));
				}
				P = T;
            }
        }
	}
}

/*
This is function which invokes generateRulesUtil with all possible valid, left and right hand side of association rule
*/
void generateRules()
{
	int n=0;
	pair< vector< ii >, vector< ii > > support;	
	int baseSupport = 0,currentSupport = 0;
	for(int i=0;i<answer.size();i++)
	{
		if( 1 == answer[i].size()) continue;
		set<int> uni(answer[i].begin(),answer[i].end());
		baseSupport = sp_count[uni];
		rules.clear();
		for(int j=answer[i].size()-1;j>=0;j--)
		{
			set<int> lhs,rhs;
			rhs.insert(answer[i][j]);
			for(int k=0;k<answer[i].size();k++)
			{
				if(k ==j) continue;
				else lhs.insert(answer[i][k]);
			}
		
			if(rules.find(make_pair(lhs,rhs)) == rules.end())
				generateRuleUtil(lhs,rhs,baseSupport);
		}
	}
}

/*
Parameters:- This function takes a file name as input.
This function writes all the valid high confidence rules to the file in the format LHS|RHS|SUPPORT|CONFIDENCE
If support count is less than 20, then it only list all valid frequent Itemset.
*/
void printRules(char *fname)
{
	FILE *fp = fopen(fname,"w");
	if( minsup > 20 )
	{
		for(int i=0;i<lhs.size();i++)
		{
			for(int j=0;j<lhs[i].size();j++)
			{
				if(j == lhs[i].size()-1) fprintf(fp,"%d",lhs[i][j]);
				else fprintf(fp,"%d ",lhs[i][j]);
			}
			fprintf(fp,"|");
			for(int j=0;j<rhs[i].size();j++)
			{
				if(j == rhs[i].size()-1) fprintf(fp,"%d",rhs[i][j]);
				else fprintf(fp,"%d ",rhs[i][j]);
			}
			fprintf(fp,"|");
			fprintf(fp,"%d|%.3f\n",sups[i],confs[i]);
		}
	}
	else
	{
		for(int i=0;i<answer.size();i++)
		{
			for(int j=0;j<answer[i].size();j++)
			{
				if(j == answer[i].size()-1) fprintf(fp,"%d",answer[i][j]);
				else fprintf(fp,"%d ",answer[i][j]);
			}
			fprintf(fp,"|{}|%d|-1\n",only_sups[i]);
		}
	}
	fclose(fp);
}

int main(int argc, char *argv[])
{
		double t1,t2,t3,t4;
		timeval tv1,tv2,tv3,tv4;
		ump db,mdb; 
		char fname[]  = "data/run_times.csv";
		if( 6 != argc )
				printf("Wrong number of arguments. Corrected order should be 'minsup minconf inputfile outputfile options'\n");
		else
		{
				clear();
				stringstream sup(argv[1]);sup >> minsup;
				stringstream conf(argv[2]);conf >> minconf;
				stringstream option(argv[5]);option >> options;
				readInput(argv[3],db);
				vector< ii > _sc = prune(db);
				vector<int> cur;
				gettimeofday (&tv1, NULL);
				t1 = double (tv1.tv_sec) + 0.000001 * tv1.tv_usec;
				generateFrequentElements(db,_sc,cur);
				gettimeofday (&tv2, NULL);
				t2 = double (tv2.tv_sec) + 0.000001 * tv2.tv_usec;
				gettimeofday (&tv3, NULL);
				t3 = double (tv3.tv_sec) + 0.000001 * tv3.tv_usec;
				if(minsup > 20) generateRules();
				gettimeofday (&tv4, NULL);
				t4 = double (tv4.tv_sec) + 0.000001 * tv4.tv_usec;
				printRules(argv[4]);
				//FILE *fp =fopen(fname,"a");
				//fprintf(fp,"%d,%.2f,%d,%zu,%zu,%.5f,%.5f\n",minsup,minconf,options,answer.size(),lhs.size(),t2-t1,t4-t3);
				//fclose(fp);	
		}
		return 0;
}
