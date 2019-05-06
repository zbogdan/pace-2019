// randomness through *401
// brelaz on top
// FIRST_K for starting a sequence of k's

// todo: ket kulon listaba tenni a tail-t es a teljes csucssorozatot
// Culberson megoldasa tobbszor
// becsles a fa meretre a legfelso szinten
// haromszogmentes..

// file-bol olvasson-e, vagy a STD in-out a bemenet-kimenet?
//const bool STDOUT=false;
const bool STDOUT=true;

bool KNUTH=false;

#include <iostream>
#include <bitset>
#include <fstream>
#include <iomanip>
#include <vector>
#include <algorithm>
#include <boost/dynamic_bitset.hpp>

using namespace std;
double k_1time=-1, ktime=0;
long long k_1nsum=-1, knsum=0;
// !! // const int Nmax=800;
//const int Nmax=1024;
//const int Nmax=2048;
//const int Nmax=4096;
bool INITIALIZED=false;

vector<int> patric_function; // USED in patric_function.cpp!!
vector<int> pnodes; // USED in patric_function.cpp!!
const bool PATRIC=false; // true for patric_function.cpp

//for recoloring DSatur after using patric_function
vector<int> nodes_colored;
const int ReColorPat=4;
vector<bool> toReColor;

int level;
int max_level; // value of k in finding k-clique
bool FIRST_K=false;

// not const for patric_function
int ReColor=1;
const int ReOrderLevel=4000;
//const int cut_off=1;
int N;               // actual graph size

vector<int> tree;      // branching tree
long long n=0;       // tree size
long l0=0,l1=0,l2=0,l3=0,l4=0,l5=0,l6=0,l7=0,l8=0;
     // tree level size on level 0,1 and 2
long long solution=0;
string whoami;

string comment="";

vector<boost::dynamic_bitset<> > inc(0, boost::dynamic_bitset<>(0));
vector<boost::dynamic_bitset<> > inc_tmp(0, boost::dynamic_bitset<>(0));
vector<boost::dynamic_bitset<> > stack_in(0, boost::dynamic_bitset<>(0));
vector<boost::dynamic_bitset<> > stack_out(0, boost::dynamic_bitset<>(0));

/*
bitset<Nmax> inc[Nmax];
bitset<Nmax> inc_tmp[Nmax];
bitset<Nmax> stack_in[Nmax];  // neigburs of the clique (and the clique)
bitset<Nmax> stack_out[Nmax]; // points in the clique
*/


vector<int> st_i;            // point examined
vector<vector<int> > branch;    // nodes for branching
vector<int> branch_zero;    // nodes by initial coloring (level=-1)
vector<int> branch_max;      // num of branching
vector<int> branch_full;     // all nodes in branch
vector<int> nodes;         // nodes of a branch to color
vector<pair<int,int> > to_sort;   // anything to be sorted
vector<pair<int,int> > to_sort2;   // anything to be sorted


time_t t0, t1;

bool **colors; // color classes
vector<vector<int> > bcolors; // color classes
vector<boost::dynamic_bitset<> > col_class(0, boost::dynamic_bitset<>(0));
vector<boost::dynamic_bitset<> > col_buck(0, boost::dynamic_bitset<>(0));
//bitset<Nmax> col_class[Nmax]; // color classes
bool **free_color; // free color classes of nodes
int *sat; // saturation of a node
int *free_num; // number of free color classes for nodes
bool *OK; // is the node ready
int num_color=0;
int num_to_color;    // number of nodes to color
vector<int> col_sum;   // sum of nodes in color classes
int brelaz_recolor=0;
int *color_degree;

// Culberson recoloring
const int MULTIPL=1000; // number of recoloring
vector<int> colors_best;
vector<int> colors_sum;
vector<int> sequence;
vector<boost::dynamic_bitset<> > bucket(0, boost::dynamic_bitset<>(0));
vector<int> perm_color;

vector<vector<int> > to_sort3;


void read_clq(string);
void brelaz();
bool bcolor();
bool bcolor_bit();

// reorder "tail" by difficulty: easiest first!
// reorder by node degree
void reorder(){
  int i,j;

  for(i=0;i<branch_max[level];++i)
    to_sort2[i]=make_pair((stack_in[level]&inc[branch[level][i]]).count(), branch[level][i]);

  sort(to_sort2.begin(),to_sort2.begin()+branch_max[level]);

  for(i=0;i<branch_max[level];++i)
    branch[level][i]=to_sort2[i].second;

}

// reorder by look ahead coloring branch
void reorder2(){
  int i,j;
  ++level;
  for(i=0;i<branch_max[level-1];++i){
    stack_in[level] = stack_in[level-1]&inc[branch[level-1][i]];
    bcolor_bit();
    to_sort2[i]=make_pair(branch_max[level], branch[level-1][i]);
  }
  sort(to_sort2.begin(),to_sort2.begin()+branch_max[level-1]);

  --level;
  for(i=0;i<branch_max[level];++i)
    branch[level][i]=to_sort2[i].second;
}

//coloring by iterated Culberson's method
void culberson(){

  //Culberson
  int i,c,node,color_sum_max;
  int maximum_colors=N;

  for(node=0;node<N;++node)
    sequence[node]=branch_zero[node];
  int mm=1;
  for(int mult=1;mult<MULTIPL;++mult,++mm){

    for(i=0;i<num_color;++i){
      colors_best[i]=-1;
      colors_sum[i]=0;
      //to_sort[i].clear();
    }
    //for(c=0;c<color_sum_max;++c)
    //to_sort[i].clear();

    for(i=0;i<num_color;++i)
      bucket[i].reset();

    bucket[0]=inc[sequence[0]];
    colors_best[sequence[0]]=0;
    num_color=1;
    colors_sum[0]=1;
    color_sum_max=1;

    for(node=1;node<N;++node){
      for(c=0;bucket[c][sequence[node]];++c);
      if(c==num_color)++num_color;

      bucket[c]|=inc[sequence[node]];
      colors_best[sequence[node]]=c;
      if(++colors_sum[c]>=color_sum_max) color_sum_max=colors_sum[c];
    }
    if(maximum_colors>num_color){
      maximum_colors=num_color;
      mult=1;
      for(c=0;c<num_color;++c){
	col_buck[c].reset();
	for(node=0;node<N;++node)
	  if(colors_best[node]==c) col_buck[c][node]=1;
      }
    }
    if(!STDOUT && (mm==1 || mm%50==0) ){
      cout<<whoami<<"-"<<mm<<"x: number of Culberson's colors: "<<num_color;
      cout<<"max: "<<maximum_colors<<endl;
    }    
    sequence.clear();
    
    if(mult%3!=0 && (MULTIPL-mult)%1000>5){
      for(c=num_color-1;c>=0;--c)
	for(node=0;node<N;++node)
	  if(colors_best[node]==c)
	    sequence.push_back(node);
      //}else if(mult>=MULTIPL-5 || mult%3==0 && mult%90!=0 || mult%100<5){
    }else if((MULTIPL-mult)%1000<=5 || mult%3==0 && mult%90!=0 || mult%100<5){// && mult%90!=0){
      for(i=0;i<=color_sum_max;++i)
	to_sort3[i].clear();
      
      for(c=0;c<num_color;++c)
	to_sort3[colors_sum[c]].push_back(c);

      for(i=color_sum_max;i>=0;--i)
	if(to_sort3[i].size()>0)
	  for(c=0;c<to_sort3[i].size();++c)
	    for(node=0;node<N;++node)
	      if(colors_best[node]==to_sort3[i][c]){
		sequence.push_back(node);
		//cout<<node<<", ";
	      }
   }else{
      perm_color.clear();
      for(c=0;c<num_color;++c)
	perm_color.push_back(c);

      int x,y,tmp;
      for(x=0;x<num_color;++x){
	y=((mult+x)*401)%num_color;
	tmp=perm_color[y];
	perm_color[y]=perm_color[x];
	perm_color[x]=tmp;
      }
      for(c=0;c<num_color;++c)
	for(node=0;node<N;++node)
	  if(colors_best[node]==perm_color[c])
	    sequence.push_back(node);

    }

  }

  for(node=0;node<N;++node)
    branch_zero[node]=sequence[node];
  max_level=num_color;
  if(!STDOUT)
    cout<<whoami<<"-("<<mm<<"x): FINAL number of Culberson's colors: "<<num_color<<endl;
  //exit(33);
}

bool test_color(){ //brelaz on the top
  int i,j,c;
  vector<pair<int,int> > col_sum_num;
  int sum, best_br, best_c;

  //num_to_color = N; //stack_in[level].count();
  num_to_color = stack_in[level].count();

  if(level==0){
    if( bcolor_bit()) return true;
    if(!FIRST_K) return false;
    best_br=branch_max[level];
    best_c=num_color; //num_to_color+1;
  }else{
    best_br=num_to_color+1, best_c=num_to_color+1;
  }

  
  //initialize
  for(i=0;i<N;++i)
    inc_tmp[i] = inc[i] & stack_in[level];

  int v=0;
  for(i=0;i<N;++i){
    if(stack_in[level][i]){
      sat[i]=inc_tmp[i].count();
      to_sort[v++]=make_pair(sat[i],i);
    } else sat[i]=0;
  }
  sort(to_sort.begin(), to_sort.begin()+v);
  nodes.clear();
  for(i=num_to_color-1;i>=0;--i)
    nodes.push_back(to_sort[i].second);

  for(int tries=ReColor;tries>0;--tries){

    brelaz();

    if(FIRST_K && (max_level==-1 || max_level>num_color)){
      max_level=num_color;
    }
    if( (level+num_color)<max_level) return true;

    //color sums: (atvinni a brelzaba!!)
    for(c=0;c<num_color;++c){
      col_sum[c]=0;
      for(i=0;i<num_to_color;++i)
	if(colors[c][i])
	  ++col_sum[c];
    }

    for(c=0;c<num_color;++c){
      to_sort[c]=make_pair(col_sum[c],c);
    }
    sort(to_sort.begin(),to_sort.begin()+num_color);

    
    sum=0;
    for(i=0;i<=num_color+level-max_level;++i)
      sum += to_sort[i].first;

    if(PATRIC && level==0 && best_c>num_color){
      v=0;
      for(c=0; c<num_color; ++c)
	for(j=0;j<num_to_color;++j)
	  if(colors[to_sort[c].second][j]){
	    nodes_colored[v++]=nodes[j];
	  }
    }

    //if(best_br>sum || (best_br==sum && best_c>num_color)){
    if(best_c>num_color){
    //if( (level==0&&best_br>sum) || (level>0&&best_c>num_color)){
    //if(best_c>num_color || (best_c==num_color && best_br>sum)){
      //only for patric function
      if(PATRIC) toReColor[level+1]=false;
      best_c=num_color;
      best_br=sum;
      //if(level!=0) ++brelaz_recolor;
      //debug on first level:
      if(!STDOUT && level==0) cout<<whoami<<":try: "<<tries<<". color: "<<num_color<<", branch: "<<sum<<endl;
      //build branch
      branch_max[level]=0;
      for(i=0;i<=num_color+level-max_level;++i){
	for(j=0;j<num_to_color;++j)
	  if(colors[to_sort[i].second][j]){
	    branch_zero[branch_max[level]]=nodes[j];
	    branch[level][branch_max[level]++]=nodes[j];
	  }
      }

      //remaining nodes
      branch_full[level] = branch_max[level];
      for(i=num_color+level-max_level+1; i<num_color; ++i)
	for(j=0;j<num_to_color;++j)
	  if(colors[to_sort[i].second][j]){
	    branch_zero[branch_full[level]]=nodes[j];
	    branch[level][branch_full[level]++]=nodes[j];
	  }
    }//if(best>

    //permutation -- pseudo
    /*
    if(tries>1){
      int x,y,tmp;
      for(x=0;x<num_to_color;++x){
	// 401: magical prime number
	y=(x*401)%num_to_color;
	tmp=nodes[y];
	nodes[y]=nodes[x];
	nodes[x]=tmp;
      }
    }
    */
  }//for(;tries>=0;--tries)


  culberson();
  FIRST_K=false;
  bcolor_bit();
  

  if(ReOrderLevel>level)
    reorder();

  return false;
}

void deinit(){ //memory management for coloring
  int i;
  //colors=new bool*[N/3];
  for(i=0;i<N;i++)
    delete[] free_color[i];
  delete[] free_color;
  //free_color[i]=new bool[N/3];
  //for(i=0;i<N/3;i++) 
  for(i=0;i<N;i++) 
    delete[] colors[i];
  delete[] colors;
  delete[] sat;
  delete[] free_num;
  delete[] OK;
  //coloring
  delete[] color_degree;
}

void init(vector<vector<bool> > szomszedsagi){ //memory management for coloring
  int i,j;
  if(INITIALIZED)deinit();
  INITIALIZED=true;
  N=szomszedsagi.size();


  //colors=new bool*[N/3];
  colors=new bool*[N];
  free_color=new bool*[N];
  for(i=0;i<N;i++)
    free_color[i]=new bool[N];
  //free_color[i]=new bool[N/3];
  //for(i=0;i<N/3;i++) 
  for(i=0;i<N;i++) 
    colors[i]=new bool[N];
  sat = new int[N];
  free_num = new int[N];
  OK = new bool[N];
  //coloring
  color_degree=new int[N];
  nodes_colored.resize(N);

  //dynamic bitset:
  inc.resize(N);
  inc_tmp.resize(N);
  stack_in.resize(N+1);
  stack_out.resize(N+1);
  col_class.resize(N);
  col_buck.resize(N);

  // new:
  toReColor.resize(N);
  tree.resize(N+1);
  st_i.resize(N+1);
  branch.resize(N+1);
  branch_zero.resize(N);
  branch_max.resize(N+1);
  branch_full.resize(N+1);
  nodes.resize(N);
  to_sort.resize(N+1);
  to_sort2.resize(N+1);
  bcolors.resize(N+1);
  col_sum.resize(N+1);
  colors_best.resize(N);
  bucket.resize(N);
  to_sort3.resize(N);
  sequence.resize(N);
  colors_sum.resize(N);

  for(i=0;i<=N;++i){
    branch[i].resize(N);
    bcolors[i].resize(N);
    if(i<N){
      bucket[i].resize(N);
      sequence[i]=i;
    }
  }
  //dynamic bitset:

  for(i=0;i<N;i++){
    //dynamic bitset:
    inc[i].resize(N);
    inc_tmp[i].resize(N);
    stack_in[i].resize(N);
    stack_out[i].resize(N);
    col_class[i].resize(N);
    col_buck[i].resize(N);
    //dynamic bitset:
  }
  for(i=0;i<N;++i)
    for(j=0;j<N;++j){
      inc[i][j]=szomszedsagi[i][j];
      if(j<i && inc[i][j]!=inc[j][i]){
	cout<<"incERROR"<<endl;
	exit(17);
      }
    }


}


int maxclq(vector<vector<bool> > szomszedsagi){

  int i,j;

  for(i=0;i<N;i++){
    //inc[i].reset();
    stack_in[0][i]=1;
    stack_out[i].reset();
    tree[i]=0;
  }


  int max, cmax, tmp, clqsize=0;

  while(stack_in[0].any()){
    max=-1;cmax=-1;
    for(i=0;i<N;++i){
      tmp=(inc[i]&stack_in[0]).count();
      if(stack_in[0][i] && tmp>max){
	cmax=i;
	max=tmp;
      }
    }
    if(max>0){
      ++clqsize;
      stack_out[0][cmax]=1;
      stack_in[0] = stack_in[0]&inc[cmax];
    }else break;
  }

  return clqsize;
}

bool k_clique(vector<vector<bool> > szomszedsagi, int k, string who,
	      bool is_k_first){
  max_level=k;
  //
  FIRST_K=is_k_first;
  //if(k==-1) FIRST_K=true;
  N=szomszedsagi.size();
  if(!STDOUT) cout<<"N:"<<N<<", k:"<<k<<endl;

 
  int i,j;



  for(i=0,j=0;i<who.size();++i)
    if(who[i]=='/') j=i;
  if(j!=0)who.erase(0,j+1);
  for(i=0;i<who.size();++i)
    if(who[i]=='.') break;
  who.erase(i,who.size());
  whoami=who;

  //if(!INITIALIZED)
  //init();

  for(i=0;i<N;i++){
    //inc[i].reset();
    stack_in[0][i]=1;
    stack_out[i].reset();
    tree[i]=0;
  }

  /*
  for(i=0;i<N;++i)
    for(j=0;j<N;++j){
      inc[i][j]=szomszedsagi[i][j];
      if(j<i && inc[i][j]!=inc[j][i]){
	cout<<"incERROR"<<endl;
	exit(17);
      }
      }*/


  //measure the time
  t0=clock();

  //back tracking
  level=0;
  l0=0;
  n=0;
  solution=0;
  st_i[0]=-1;
  if(FIRST_K){
    test_color();
    if(!STDOUT)cout<<"First k is: "<<max_level<<endl;
    return true; // NEW!!
  }else if(test_color()){//deinit();
    return false;} // brelaz on the top!
  if(PATRIC)
    ReColor=ReColorPat;
  while(level>=0){
    if(level==0)
      l1=0,l2=0,l3=0,l4=0,l5=0,l6=0,l7=0,l8=0,++l0;
    if(level==1)
      l2=0,l3=0,l4=0,l5=0,l6=0,l7=0,l8=0,++l1;
    if(level==2)
      l3=0,l4=0,l5=0,l6=0,l7=0,l8=0,++l2;
    if(level==3)
      l4=0,l5=0,l6=0,l7=0,l8=0,++l3;
    if(level==4)
      l5=0,l6=0,l7=0,l8=0,++l4;
    if(level==5)
      l6=0,l7=0,l8=0,++l5;
    if(level==6)
      l7=0,l8=0,++l6;
    if(level==7)
      l8=0,++l7;
    if(level==8)
      ++l8;

    //get next point
    ++st_i[level];
    if(st_i[level]<branch_max[level]){
      //elore
      stack_in[level][branch[level][st_i[level]]]=0; // nem kell tobbet!
      stack_in[level+1] = stack_in[level]&inc[branch[level][st_i[level]]];
      stack_out[level+1]=stack_out[level];


      //TEST
      /*
      for(i=0;i<N;++i)
	if(stack_out[level][i] && !inc[branch[level][st_i[level]]][i]){
	      cout<<"kHIBA"<<endl;
	      cout<<"bm: "<<branch_max[level-1];
	      cout<<", bf: "<<branch_full[level-1];
	      cout<<", sti: "<<st_i[level-1]<<endl;
	      exit(7);
	    }
      */
      stack_out[level+1][branch[level][st_i[level]]]=1;
      st_i[level+1]=-1;

      ++level;
      ++tree[level];

      /*
      //dominancia
      if(level<ReOrderLevel){
	bool deleted=true;

	while(deleted){
	  deleted=false;
	  //
	  for(int di=0;di<N;++di)
	    for(int dj=0;dj<N;++dj)
	      if(di!=dj && stack_in[level][di] && stack_in[level][dj]
		 && !inc[di][dj] &&
		 (stack_in[level]&inc[di]).any() &&
		 (stack_in[level]&inc[dj]).any()){
		//cout<<((inc[i]^inc[j])&inc[j]).count()<<endl;
		if(!(((stack_in[level]&inc[di])^(stack_in[level]&inc[dj]))
		     &(stack_in[level]&inc[dj])).any()){ // i dominates j
		  //++node_dom;
		  //cout<<i<<" dominates "<<j<<" -- node-sum:"<<node_dom<<endl;
		  //mast!!! stack_in[] !!
		  stack_in[level][dj]=0;
		  //for(int dii=0;dii<N;++dii){
		  //inc[j][ii]=0;
		  //inc[ii][j]=0;
		  //}
		  deleted=true;
		}
	      }
	}
      }

      //dominancia
      */

      //counting the leaves of the search tree:
      ++n;
      if(!STDOUT && !((n)&((1<<21)-1))){
	cout<<whoami<<": "<<(n>>20)<<"M -- "<<l0<<"(";
	cout<<branch_max[0]<<"):"<<l1<<"("<<branch_max[1]<<"):";
	cout<<l2<<"("<<branch_max[2]<<"):"<<l3<<"("<<branch_max[3]<<"):";
	cout<<l4<<"("<<branch_max[4]<<"):"<<l5<<"("<<branch_max[5]<<"):";
	cout<<l6<<"("<<branch_max[6]<<"):"<<l7<<"("<<branch_max[7]<<"):";
	cout<<l8<<"("<<branch_max[8]<<")["<<level<<"]"<<endl;
	}
      if(level>=max_level){
	//debug + all cliques:
	//cout<<level<<"-"<<stack_out[level].count()<<"-";
	//cout<<stack_out[level]<<endl;
	//if(max_level==15) exit (1);
	// if all solutions:
	++solution;
	// break -- if only one clique!
	break;
	--level;
      }else{
      //tapasztalat: 3-4 kozott no meg a futasido!
      //3: 4x-es, 4: 2x-es fa meret mellett
      //if(level<cut_off && test_color()) //should we cut the branch?
      //if(test_color()) //should we cut the branch?
      //if(bcolor()) //should we cut the branch?
      //back
      //--level;
      //else if(level>=cut_off && bcolor())
	//if(!toReColor[level] && bcolor_bit())
	if(bcolor_bit())
	  if(!KNUTH)
	    --level;
	  else return false;
	//for Patric's function:
	//else if(toReColor[level] && test_color())
	//--level;
	else if(level<ReOrderLevel) reorder();
      }
    }else{ //end of branch; back
      if(PATRIC) toReColor[level+1]=false; // for patric's function
      if(!KNUTH)
	--level;
      else return false;
    }
  }
  //running time and branches:
  t1=clock();
  k_1time=ktime;
  k_1nsum=knsum;
  knsum=n;

  ktime=difftime(t1,t0)/CLOCKS_PER_SEC;
  if(!STDOUT){
    cout<<endl<<"Backtrack time elapsed: "<<ktime<<endl;
    cout<<endl<<"--------------------------"<<endl;
    cout<<"n: "<<n<<"\t n/10^3: "<<n/1000<<"k\t n/10^6: "<<n/1000000<<"M"<<endl;
    cout<<"Brelaz recolor: "<< brelaz_recolor<<endl;

    //display the tree:
    for(i=0;i<max_level+1;++i)
      cout << setw(5) << i<< setw(12) << tree[i] << endl;
    cout<<"solutions: "<<solution<<endl;
  }
  //deinit();

  if(solution>0) return true;
  else return false;
}

void brelaz(){
  int c,min_free, min_sat, min_id;
  int i,j;

  num_color=0;
  for(i=0;i<N;++i){
    free_num[i]=0;
    OK[i]=0;
    //col_sum[i]=0;
    color_degree[i]=0;
  }
  //for(c=0;c<N/3;++c)
  for(c=0;c<N;++c)
    for(i=0;i<N;++i){
      colors[c][i]=0;
      free_color[i][c]=0;
    }

  //we color N nodes each after other:
  for(int v=0;v<num_to_color;++v){ //N;++v){
    min_free=N;
    min_sat=N;
    min_id=-1;
    //find node of minimum freedom:
    int nok=0;
    for(i=0;i<num_to_color;++i){
      //if(OK[nodes[i]])++nok;
      if(!OK[i] && min_free>free_num[i]){
	min_free=free_num[i];
	//min_sat=sat[i];
	min_id=i;
      }
    }
    if(min_id==-1){cerr<<"hiba! "<<nok<<"-"<<N<<"+"<<num_to_color<<endl; exit (42);}
    OK[min_id]=1; //ready to color

    //color it:
    if(min_free==0){
      //We need a new color class.
      colors[num_color][min_id]=1;
      //++col_sum[num_color];
      //the new color class posible class for the rest:
      //but not for the connected nodes:
      for(i=0;i<num_to_color;++i){
	if(!OK[i] && !inc_tmp[nodes[i]][nodes[min_id]]){
	  free_color[i][num_color]=1;
	  ++free_num[i];
	}else if(inc_tmp[nodes[i]][nodes[min_id]]){
	  free_color[i][num_color]=0;
	  ++color_degree[i];
	}
      }
      ++num_color;
      //if(num_color>=N/3){
      if(num_color>N){
	cout<<"too many colors (brelaz)"<<endl;
	exit(1);
      }
    }else{
      //We put node into an old color class.
      //find the class:
      for(c=0;!free_color[min_id][c];++c);
      colors[c][min_id]=1;
      //++col_sum[c];
      //the connected nodes' freedom decreases:
      for(i=0;i<num_to_color;++i){
	if(!OK[i] && free_color[i][c] && inc_tmp[nodes[i]][nodes[min_id]]){
	  free_color[i][c]=0;
	  --free_num[i];
	  ++color_degree[i];
	}else if(OK[i] && free_color[i][c] &&
		 inc_tmp[nodes[i]][nodes[min_id]]){
	  free_color[i][c]=0;
	  ++color_degree[i];
	}
      }
    }
  }
}


bool bcolor_bit(){
  int i,j,c,v;
  num_color=0;num_to_color=0;
  bool colorable;

  //for(c=0;c<N/3;++c)
  //for(c=0;c<N;++c)
  //col_class[c]=0;

  
  if(level==0 && FIRST_K){
    nodes.clear();
    for(num_to_color=0;num_to_color<N;++num_to_color)
      nodes.push_back(num_to_color);
  }else if(level==0 && !FIRST_K){
    nodes.clear();
    for(num_to_color=0;num_to_color<N;++num_to_color)
      nodes.push_back(branch_zero[num_to_color]);
  }else if(PATRIC && toReColor[level]){
    for(i=0;i<N;++i)
	if(stack_in[level][nodes_colored[i]]){
	  nodes[num_to_color++]=nodes_colored[i];
	}
  }else{
    for(i=0;i<branch_full[level-1];++i)
      if(stack_in[level][branch[level-1][i]]){
	nodes[num_to_color++]=branch[level-1][i];
      }
  }

  int num_patric_func_branch=0;

  //coloring from the largest previous color!!
  for(v=num_to_color-1; v>=0; --v){
    if(PATRIC && level+patric_function[pnodes[nodes[v]]]>=max_level)
       ++num_patric_func_branch;
  //for(v=0;v<num_to_color;++v){
    for(c=0;c<num_color;++c){
      colorable=true;
      if(col_class[c][nodes[v]])
      //for(i=0;i<col_sum[c] && colorable;++i)
      //if(inc[nodes[v]][bcolors[c][i]])
	  colorable=false;
      if(colorable) break;
    }
    if(c==num_color){
      ++num_color;
      col_sum[c]=0;
      col_class[c].reset();
      //test
      //if(num_color>=N/3){
      if(num_color>N){
	cout<<"too many colors (bcolor)"<<endl;
	exit(1);
      }
    }
    bcolors[c][col_sum[c]++]=nodes[v];
    col_class[c] |= inc[nodes[v]];
    if(level==0 && FIRST_K)col_buck[c][nodes[v]]=1;
  }

  branch_max[level]=0;
  if(FIRST_K)
    max_level=num_color;
  else
    if( (level+num_color)<max_level ) return true;

  if (PATRIC && num_patric_func_branch==0) return true;

  //find minimum color classes
  for(c=0;c<num_color;++c)
    to_sort[c]=make_pair(col_sum[c],c);
  sort(to_sort.begin(),to_sort.begin()+num_color);

  for(c=0; c<=num_color+level-max_level; ++c)
    for(i=0;i<to_sort[c].first;++i){
      if(FIRST_K)branch_zero[branch_max[level]]=bcolors[to_sort[c].second][i];
      branch[level][branch_max[level]++]=bcolors[to_sort[c].second][i]; 
    }
  
  if(!STDOUT && level==0) cout<<whoami<<": color: "<<num_color<<", branch: "<<branch_max[level]<<endl;
   
  if(PATRIC && ReColorPat>level && branch_max[level]>num_patric_func_branch){

    branch_max[level]=0;
    branch_full[level]=num_patric_func_branch;
    for(c=0; c<num_color; ++c)
      for(i=0;i<to_sort[c].first;++i)
	if(level+patric_function[pnodes[bcolors[to_sort[c].second][i]]]
	   >= max_level){
	  if(FIRST_K)branch_zero[branch_max[level]]=bcolors[to_sort[c].second][i];
	  branch[level][branch_max[level]++]=bcolors[to_sort[c].second][i];
	}else{
	  if(FIRST_K)branch_zero[branch_full[level]]=bcolors[to_sort[c].second][i];	  
	  branch[level][branch_full[level]++]=bcolors[to_sort[c].second][i];
	}
    
    if(branch_max[level]!=num_patric_func_branch ||
       branch_full[level] != num_to_color){
      cerr<<"HIBA!"<<endl; exit(0);}

    if(level==0) cout<<whoami<<": patric's func branch: "<<branch_max[level]<<endl;
    toReColor[level+1]=true;

  }else{
    branch_full[level]=branch_max[level];
    for(c=num_color+level-max_level+1; c<num_color; ++c)
      for(i=0;i<to_sort[c].first;++i){
	if(FIRST_K)branch_zero[branch_full[level]]=bcolors[to_sort[c].second][i];	  
	branch[level][branch_full[level]++]=bcolors[to_sort[c].second][i];
      }
    
    if(PATRIC) toReColor[level+1]=false;
  }

 return false;
}
