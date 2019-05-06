#include <iostream>
#include <bitset>
#include <fstream>
#include <iomanip>
#include <vector>
#include <algorithm>
#include <boost/dynamic_bitset.hpp>

using namespace std;

const int BMULTIPL=1000; // number of recoloring
const int q=7; // q-fold

int bfold(vector<vector<bool> > szomszedsagi){
   vector<pair<int,int> > col_sum_num;
   int NN=szomszedsagi.size();
   int N;               // actual graph size
   N=q*szomszedsagi.size();
 
   int i,j, x, y, ii, jj, kk, c;
   int min_free, min_sat, min_id;
   int node,color_sum_max;
   int maximum_colors=N;

   //for recoloring DSatur after using patric_function
vector<int> nodes_colored;
vector<bool> toReColor;

int level;
int max_level; // value of k in finding k-clique


vector<boost::dynamic_bitset<> > inc(0, boost::dynamic_bitset<>(0));
vector<boost::dynamic_bitset<> > inc_tmp(0, boost::dynamic_bitset<>(0));

vector<vector<int> > branch;    // nodes for branching
vector<int> branch_zero;    // nodes by initial coloring (level=-1)
vector<int> branch_max;      // num of branching
vector<int> branch_full;     // all nodes in branch
vector<int> nodes;         // nodes of a branch to color
vector<pair<int,int> > to_sort;   // anything to be sorted
vector<pair<int,int> > to_sort2;   // anything to be sorted
vector<vector<int> > to_sort3;



bool **colors; // color classes
vector<vector<int> > bcolors; // color classes
vector<boost::dynamic_bitset<> > col_class(0, boost::dynamic_bitset<>(0));
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
vector<int> colors_best;
vector<int> colors_sum;
vector<int> sequence;
vector<boost::dynamic_bitset<> > bucket(0, boost::dynamic_bitset<>(0));
vector<int> perm_color;




  //dynamic bitset:
  inc.resize(N);
  inc_tmp.resize(N);
  col_class.resize(N);

  // new:
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
    col_class[i].resize(N);
    //dynamic bitset:
    inc[i].reset();
  }

  for(i=0;i<N;++i)
    for(j=0;j<N;++j)
      inc[i][j]=0;

  if(q>1){
    for(x=0;x<NN;++x)
      for(y=x+1;y<NN;++y){
	if(!szomszedsagi[x][y])continue;
	
	//multiplicity on edges:
	for(ii=q*x;ii<q*(x+1);++ii)
	  for(jj=q*y;jj<q*(y+1);++jj){
	    inc[ii][jj]=1;
	    inc[jj][ii]=1;
	  }
      }
    //column connection:
    for(ii=0;ii<NN;++ii)
      for(jj=0;jj<q;++jj)
	for(kk=jj+1;kk<q;++kk){
	  inc[ii*q+jj][ii*q+kk]=1;
	  inc[ii*q+kk][ii*q+jj]=1;
	}
  }else{ // ORIGINAL
    for(i=0;i<N;++i)
      for(j=0;j<N;++j){
	inc[i][j]=szomszedsagi[i][j];
	if(j<i && inc[i][j]!=inc[j][i]){
	  cout<<"incERROR"<<endl;
	  exit(17);
	}
      }
  }
  
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

  
  num_to_color = N; //stack_in[level].count();

  
  //initialize
  for(i=0;i<N;++i)
    inc_tmp[i] = inc[i];

  int v=0;
  for(i=0;i<N;++i){
    sat[i]=inc_tmp[i].count();
    to_sort[v++]=make_pair(sat[i],i);
  }
  sort(to_sort.begin(), to_sort.begin()+v);
  nodes.clear();
  for(i=num_to_color-1;i>=0;--i)
    nodes.push_back(to_sort[i].second);

  //brelaz();
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


  max_level=num_color;

    //if( (level+num_color)<max_level) return true;

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

    //culberson();
      for(node=0;node<N;++node)
    sequence[node]=branch_zero[node];

  int mm=1;
  for(int mult=1;mult<BMULTIPL;++mult,++mm){

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
      if(c==num_color) ++num_color;
	
      bucket[c]|=inc[sequence[node]];
      colors_best[sequence[node]]=c;
      if(++colors_sum[c]>=color_sum_max) color_sum_max=colors_sum[c];
    }
    if(maximum_colors>num_color){ maximum_colors=num_color;mult=1;}    
    //if(mm==1 || mm%200==0)
    //cout<<whoami<<"-"<<mult<<"x: number of Culberson's colors: "<<num_color<<endl;
    
    if(num_color<max_level)max_level=num_color;
    sequence.clear();
    
    if(mult%3!=0 && (BMULTIPL-mult)%1000>5){
      for(c=num_color-1;c>=0;--c)
	for(node=0;node<N;++node)
	  if(colors_best[node]==c)
	    sequence.push_back(node);
      //}else if(mult>=BMULTIPL-5 || mult%3==0 && mult%90!=0 || mult%100<5){
    }else if((BMULTIPL-mult)%1000<=5 || mult%3==0 && mult%90!=0 || mult%100<5){// && mult%90!=0){
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

  //test_color();
  cout<<"First k is: "<<(double)max_level/q<<" = "<<max_level/q<<endl;
  return max_level/q;
}

