#include <iostream>
#include <fstream>
#include <algorithm>
#include <vector>
using namespace std;

#include "kclique-stdout.cpp"
#include "bfold-culbcol.cpp"

int megszamol2xsok=0;

bool k_clique(vector<vector<bool> >, int, string, bool);
int maxclq(vector<vector<bool> >);
boost::dynamic_bitset<> solution_line;
boost::dynamic_bitset<> tmp_line;
int solution_size=0;
int sol_count=0;
int del_count=0;
int fold_count=0;

int k;
int max_num_color;

bool node_prune();
bool node_prune3();
bool edge_prune3();
bool edge_prune4();
long long node_pruned=0;
long long edges_pruned=0;


bool basic();
bool fold1();
void write_vc(string);

vector<vector<bool> > szomszedsagi;    // inciedence matrix      //
int meret;

vector<pair<int, int> > feladat;

//for folding out
vector<vector<int> > folding;
// 1st: dominating
// 2nd: number of dominated
// 3rd+: dominated

// translete table
vector <int> translate;
// non-negative: translation node->node
// -1, -2: in clique (-1 -> -2) (solution)
// -4: in folding -- kell ez?
// -7: in vc (deleted)
// -42: temporary

vector <int> translate_back;

vector <int> Btranslate;
vector <int> Btranslate_back;
int Bsolution_size;
int Bmeret;
vector<vector<int> > complG;
vector<vector<int> > Bfolding;
// values: same as folding!!

//nem szomszedok:
vector<boost::dynamic_bitset<> > non_n(0, boost::dynamic_bitset<>(0));
int size_non_n;
vector<int> perm;

void red_delnode(int w){
  int i,j,v;
  if(Btranslate[w]==-2 || Btranslate[w]==-7){
    cerr<<"ures node torlese! w: "<<w<<" Btransl: "<<Btranslate[w]<<endl;
    exit(444);
  }
  Btranslate[w]=-7;
  for(i=0;i<complG[w].size();++i)
	for(j=0;j<complG[complG[w][i]].size();++j)
	  if(complG[complG[w][i]][j]==w){
	    complG[complG[w][i]].erase(complG[complG[w][i]].begin()+j);
	    --j;}
  complG[w].clear();

  /*
  //ellenorzes:
  for(v=0;v<Bmeret;++v){
    if(Btranslate[v]<0)continue;
    for(i=0;i<complG[v].size();++i)
      if(Btranslate[complG[v][i]]<0){
	cerr<<"torolt szomszed: "<<v<<" szomszed: "<<complG[v][i];
	cerr<<" Btr: "<<Btranslate[complG[v][i]]<<endl;
	cerr<<"eppen torol: "<<w<<endl;
	exit(88);
      }
      }*/
}

void red_insert(int w, vector<int> f){
  int i,j;
  bool found;
  for(i=0;i<f.size();++i){
    found=false;
    for(j=0;j<complG[w].size();++j)
      if(f[i]==complG[w][j]){ found=true;break;}
    if(!found){
      complG[w].push_back(f[i]);
      complG[f[i]].push_back(w);
    }
  }
}

void red_insert(int w, int a){
  int i,j;
  bool found;
  found=false;
  for(j=0;j<complG[w].size();++j)
    if(a==complG[w][j]){ found=true;break;}
    if(!found){
      complG[w].push_back(a);
      complG[a].push_back(w);
    }
}

bool reduce2(){
  int i,j,v,w,k,l;
  int a,b,c,d, tmpv;
  int da,db,dc,dd;//fokszamok
  bool ab, ac, bc;
  bool ad, bd, cd;
  int nume, s;
  bool deleted=false;
  bool found;
  for(v=0;v<Bmeret;++v){
    if(Btranslate[v]==-2 || Btranslate[v]==-7) continue;

    if(complG[v].size()==0){ //full node
      Btranslate[v]=-2; deleted=true;
    } else if(complG[v].size()==1){ //degree 1
      //delete dominated:
      red_delnode(complG[v][0]);deleted=true;
      //delete dominating:
      Btranslate[v]=-2; 
    } else if(complG[v].size()==2){ //degree 2
      a=complG[v][0];
      b=complG[v][1];
      if(Btranslate[a]==-2 || Btranslate[a]==-7 ||
	 Btranslate[b]==-2 || Btranslate[b]==-7){cerr<<"???2"<<endl;exit(3);}
      nume=0;
      for(i=0;i<complG[a].size();++i)
	if(complG[a][i]==b){nume=1;break;}
      if(nume==1){ // dominating, remains full
	red_delnode(a);
	red_delnode(b);
	Btranslate[v]=-2;deleted=true;
      }else{ // ossze vannak kotve -> 2fold
	vector<int> tmp;
	tmp.insert(tmp.end(), { v,2,a,b });
	Bfolding.push_back(tmp);
	red_insert(a,complG[b]);
	red_delnode(b);
	red_delnode(v);deleted=true;
      }
    } else if(complG[v].size()==3){ //degree 3
      a=complG[v][0];
      b=complG[v][1];
      c=complG[v][2];
      if(Btranslate[a]==-2 || Btranslate[b]==-2 ||
	 Btranslate[c]==-2 ){cerr<<"???3 -2"<<endl;exit(3);}
      if(Btranslate[a]==-7 || Btranslate[b]==-7 ||
	 Btranslate[c]==-7){cerr<<"???3 -7"<<endl;exit(3);}
      nume=0; ab=ac=bc=false;
      for(i=0;i<complG[a].size();++i)
	if(complG[a][i]==b){++nume;ab=true;break;}
      for(i=0;i<complG[a].size();++i)
	if(complG[a][i]==c){++nume;ac=true;break;}
      for(i=0;i<complG[b].size();++i)
	if(complG[b][i]==c){++nume;bc=true;break;}
      if(nume==3){ //dominating, remains full
	red_delnode(a);
	red_delnode(b);
	red_delnode(c);
	//cout<<"MERET: "<<complG[v].size()<<" v: "<<v<<endl;
	Btranslate[v]=-2;deleted=true;
      } else if(nume==2){ //a isolated:del, b-c edge: 2fold
	int tmpv;
	if(!ab){ //rotate to right position
	  tmpv=c;
	  c=a;
	  a=tmpv;
	}else if(!ac){
	  tmpv=b;
	  b=a;
	  a=tmpv;
	}else if(!bc){
	  ;
	}else{cerr<<"hibas elszamolas2"<<endl;exit(102);}
	vector<int> tmp;
	tmp.insert(tmp.end(), { v,2,b,c });
	Bfolding.push_back(tmp);
	red_insert(b,complG[c]);
	red_delnode(a);
	red_delnode(c);
	red_delnode(v);deleted=true;
      }else if(nume==1){ // a-b, a-c edges: 2x2fold
	int tmpv;
	if(ab){ //rotate to right position
	  tmpv=c; c=a; a=tmpv;
	}else if(ac){
	  tmpv=b; b=a; a=tmpv;
	}else if(bc){
	  ;
	}else{cerr<<"hibas elszamolas2"<<endl;exit(102);}
	//if(!bc || ab || ac) cerr<<"nem jo..."<<bc<<ab<<ac<<endl;
	vector<int> tmp;
	tmp.insert(tmp.end(), { v,2,b,a });
	Bfolding.push_back(tmp);
	red_insert(b,complG[a]);
	tmp.clear();
	tmp.insert(tmp.end(), { v,2,a,c });
	Bfolding.push_back(tmp);
	red_insert(a,complG[c]);
	red_delnode(c);
	red_insert(a,b);
	//complG[a].push_back(b);
	//complG[b].push_back(a);
	red_delnode(v);deleted=true;
      }else if(nume==0){// 3fold
	vector<int> tmp;
	vector<int> va=complG[a];
	vector<int> vb=complG[b];
	vector<int> vc=complG[c];
	tmp.insert(tmp.end(), { v,3,b,a,c }); //not a,b,c!
	Bfolding.push_back(tmp);
	red_insert(b,va);
	red_insert(a,vc);
	red_insert(c,vb);
	red_insert(a,c);
	//complG[a].push_back(c);
	//complG[c].push_back(a);
	red_insert(c,b);
	//complG[b].push_back(c);
	//complG[c].push_back(b);
	//cout<<"v: "<<v<<endl;
	red_delnode(v);deleted=true;	
      }	
    } else if(complG[v].size()==4){ //degree 4
      vector<int> tmp;
      a=complG[v][0];
      b=complG[v][1];
      c=complG[v][2];
      d=complG[v][3];
      if(Btranslate[a]==-2 || Btranslate[b]==-2 ||
	 Btranslate[c]==-2 || Btranslate[d]==-2)
	{cerr<<"???3 -2"<<endl;exit(3);}
      if(Btranslate[a]==-7 || Btranslate[b]==-7 ||
	 Btranslate[c]==-7 || Btranslate[d]==-7)
	{cerr<<"???3 -7"<<endl;exit(3);}
      nume=0; ab=ac=ad=bc=bd=cd=false;
      da=db=dc=dd=0;
      for(i=0;i<complG[a].size();++i)
	if(complG[a][i]==b){++nume;ab=true;++da;++db;break;}
      for(i=0;i<complG[a].size();++i)
	if(complG[a][i]==c){++nume;ac=true;++da;++dc;break;}
      for(i=0;i<complG[a].size();++i)
	if(complG[a][i]==d){++nume;ad=true;++da;++dd;break;}
      for(i=0;i<complG[b].size();++i)
	if(complG[b][i]==c){++nume;bc=true;++db;++dc;break;}
      for(i=0;i<complG[b].size();++i)
	if(complG[b][i]==d){++nume;bd=true;++db;++dd;break;}
      for(i=0;i<complG[c].size();++i)
	if(complG[c][i]==d){++nume;cd=true;++dc;++dd;break;}
      int degdist[4];
      ++degdist[da];
      ++degdist[db];
      ++degdist[dc];
      ++degdist[dd];
      
      if(nume==6){ //dominating, remains full
	red_delnode(a);
	red_delnode(b);
	red_delnode(c);
	red_delnode(d);
	Btranslate[v]=-2;deleted=true;
      }else if(nume==3 && degdist[2]==3 && degdist[0]==1){
	// a-b a-c a-d
	if(db==0){
	  tmpv=b; b=a; a=tmpv;
	}else if(dc==0){
	  tmpv=c; c=a; a=tmpv;
	}else if(dd==0){
	  tmpv=d; d=a; a=tmpv;
	}
	tmp.insert(tmp.end(), { v,2,b,a });
	Bfolding.push_back(tmp);
	red_insert(b,complG[a]);
	tmp.clear();
	tmp.insert(tmp.end(), { v,2,c,a });
	Bfolding.push_back(tmp);
	red_insert(c,complG[a]);
	tmp.clear();
	tmp.insert(tmp.end(), { v,2,d,a });
	Bfolding.push_back(tmp);
	red_insert(d,complG[a]);
	red_delnode(a);
	red_insert(b,c);
	red_insert(b,d);
	red_insert(c,d);
	red_delnode(v);deleted=true;
      }
    }

    if(deleted)continue;

    // regi 0 fokuak:
    /*
    if(complG[v].size()>2){
      bool allconn;
      for(i=0;i<complG[v].size();++i){
	allconn=true;
	for(j=0;allconn&&j<complG[v].size();++j){
	  if(complG[v][i]==complG[v][j])continue;
	  for(w=0;allconn&&w<complG[complG[v][i]].size();++w)
	    allconn=(complG[complG[v][i]][w]==complG[v][j]);
	}
	if(allconn){
	  red_delnode(complG[v][i]);
	  deleted=true;
	}
      }
    }
    if(deleted)continue;
    */

    // ATEMELVE!!!
    for(s=0;s<complG[v].size();++s)
      perm[s]=complG[v][s];
    if(s==0) continue; // azert ennek nem kene elofordulnia!
    for(i=0;i<s;++i)
      non_n[i].reset();
    
    for(i=0;i<s;++i)
      for(j=0;j<s;++j)
	if(i==j)non_n[i][j]=0;
	else non_n[i][j]=1;

    for(i=0;i<s;++i)
      for(j=0;j<complG[perm[i]].size();++j)
	for(k=0;k<s;++k)
	  if(perm[k]==complG[perm[i]][j])non_n[i][k]=0;

    //kitoroljuk a 0 fokuakat
    for(j=0;j<s;++j)
      if(non_n[j].none()){
	red_delnode(perm[j]);
	deleted=true;
      }
    // ELLENORIZNI!!!
    if(complG[v].size()==0){
      Btranslate[v]=-2;
      deleted=true;
      continue;
    }
    
    //1 fokuak (parok) 2fold-ja:
    bool allfold=true;
    bool atleastone=false;
    for(i=0;allfold && i<s;++i)
      allfold = allfold && (non_n[i].count()<=1); // regi: ==1 <=1?
    if(allfold){
      for(i=0;i<s;++i)
	if(non_n[i].count()==1){
	  for(j=0;j<s && !non_n[i][j] ;++j);
	  if(j>=s) {cerr<<"bajvan1"<<endl; exit (77);}
	  for(k=j+1;k<s && !non_n[i][k] ;++k);
	  if(k<s) {cerr<<"bajvan2"<<endl; exit (77);}
	  vector<int> tmp;
	  tmp.insert(tmp.end(), { v,2,perm[i],perm[j] });
	  Bfolding.push_back(tmp);
	  red_insert(perm[i],complG[perm[j]]);
	  red_delnode(perm[j]);
	  non_n[i][j]=0;
	  non_n[j][i]=0;
	  atleastone=true;
	}
      // v torolheto, mert van 2fold
      if(atleastone){
	red_delnode(v);deleted=true;
      }
    }
    //ATEMELVE VEGE!
    if(deleted)continue;

    // 2folding of a star
    int multi=-1;
    vector<int> tmp;
    bool foldable=true;
    bool foundone=false;
    for(i=0;foldable && i<s;++i){
      if(non_n[i].count()>1){
	if(multi!=-1){
	  foldable=false;
	  foundone=true;
	}else{
	  multi=i;
	}
      }else if(non_n[i].none()){
	foldable=false;
      }
    }
    if(foldable && foundone){
      vector<int> vv=complG[perm[multi]];
      for(i=0;i<s;++i){
	if(i==multi) continue;
	tmp.clear();
	tmp.insert(tmp.end(), { v,2,perm[i],perm[multi] });
	Bfolding.push_back(tmp);
	red_insert(perm[i],vv);
      }
      //delete multidegree nodes
      red_delnode(perm[multi]);
      // connect one degree nodes
      for(i=0;i<s;++i){
	if(i==multi) continue;
	for(j=i+1;j<s;++j){
	  if(j==multi) continue;
	  red_insert(perm[i],perm[j]);
	}
      }
      // fold v:
      red_delnode(v);deleted=true;
    }
    if(deleted) continue;
    // 2folding of stars
    /*
    vector<vector<int> > deg_inc;
    vector<vector<int> > vv;
    vector<int> tmp;
    bool foldable=true;
    bool foundone=false;
    deg_inc.resize(s);
    vv.resize(s);
    for(i=0;i<s;++i)
      deg_inc[i].resize(2);
    
    for(i=0;i<s;++i){
      if(non_n[i].count()==1)
	deg_inc[i][0]=1;
      if(non_n[i].count()>1)
	deg_inc[i][0]=2;
       if(non_n[i].none())
	deg_inc[i][0]=0;
    }
    for(i=0;foldable && i<s;++i)
      if(deg_inc[i][0]==1){
	for(j=0;j<s && !non_n[i][j];++j);
	if(j>=s) {cerr<<"bajvan3"<<endl; exit (88);}
	deg_inc[i][1]=j;
	if(deg_inc[j][0]!=2)foldable==false; //++
      }else if(deg_inc[i][0]==2){
	deg_inc[i][1]=-1;
	foundone=true;
	for(j=0;j<complG[perm[i]].size();++j)
	  vv[i].push_back(complG[perm[i]][j]);
	for(j=0;foldable && j<s;++j)
	  if(non_n[i][j] && deg_inc[j][0]==2)
	    foldable=false;
	//two multidegree nodes cannot be connected
      }
    if(foldable && foundone){
      for(i=0;i<s;++i){
	if(deg_inc[i][0]==0){
	  red_delnode(perm[i]);
	}else if(deg_inc[i][0]==1){
	  b=i;
	  a=deg_inc[i][1];
	  tmp.clear();
	  tmp.insert(tmp.end(), { v,2,perm[b],perm[a] });
	  Bfolding.push_back(tmp);
	  red_insert(perm[b],vv[a]);
	  //++ if(deg_inc[a][0]==1)
	  //++ deg_inc[a][0]=-1;
	}
      }
      //delete multidegree nodes
      for(i=0;i<s;++i)
	if(deg_inc[i][0]==2 || deg_inc[i][0]==-1)
	  red_delnode(perm[i]);
      // connect one degree nodes
      for(i=0;i<s;++i)
	for(j=i+1;j<s;++j)
	  if(deg_inc[i][0]==1 && deg_inc[j][0]==1)
	    red_insert(perm[i],perm[j]);
      // fold v:
      red_delnode(v);deleted=true;
    }
    */

    // multiple edges and triangles
    vector<vector<int> > deg_inc3;
    vector<int> deg_inc2;
    foldable=true;
    foundone=false;
    deg_inc3.resize(s);
    deg_inc2.resize(s);
    for(i=0;i<s;++i){
      deg_inc2[i]=-1;
      deg_inc3[i].resize(3);
      deg_inc3[i][0]=-1;
      deg_inc3[i][1]=-1;
      deg_inc3[i][2]=-1;
    }
    for(i=0;foldable && i<s;++i){
      if(non_n[i].none()){
	deg_inc2[i]=-2;
      }else if(non_n[i].count()==1){
	for(j=0;j<s && !non_n[i][j];++j);
	if(j>=s) {cerr<<"bajvan3"<<endl; exit (88);}
	deg_inc2[i]=j;
	foundone=true;
      }else if(non_n[i].count()==2){
	for(k=0,j=0; j<s;++j)
	  if(j==i || non_n[i][j]) deg_inc3[i][k++]=j;
	if(k>3) {cerr<<"bajvan4"<<endl; exit (89);}
	foundone=true;
      }else foldable=false;
    }
    for(i=0;foldable && i<s;++i){
      if(deg_inc2[i]!=-1 && deg_inc3[i][0]!=-1){
	cerr<<"bajvan33"<<endl;
	exit (99);
      }
      if(deg_inc2[i]>=0){
	if(deg_inc2[deg_inc2[i]]!=i){
	    foldable=false;
	    break;
	}else{//delete second
	  deg_inc2[deg_inc2[i]]=-9;
	}
      }else if(deg_inc3[i][0]>=0){
	int a=deg_inc3[i][0], b=deg_inc3[i][1], c=deg_inc3[i][2];
	if(a!=i ||
	   deg_inc3[a][0]!=a || deg_inc3[a][1]!=b || deg_inc3[a][2]!=c ||
	   deg_inc3[b][0]!=a || deg_inc3[b][1]!=b || deg_inc3[b][2]!=c ||
	   deg_inc3[c][0]!=a || deg_inc3[c][1]!=b || deg_inc3[c][2]!=c
	   ){
	  foldable=false;
	  break;	  
	} else{ //delete second, third
	  deg_inc3[b][0]=-9;
	  deg_inc3[b][1]=-9;
	  deg_inc3[b][2]=-9;
	  deg_inc3[c][0]=-9;
	  deg_inc3[c][1]=-9;
	  deg_inc3[c][2]=-9;
	}
      }
    }
    if(foldable && foundone){
      if(!STDOUT)cerr<<"folding 2s and 3s, v:"<<v<<endl;
      for(i=0;i<s;++i){
	if(deg_inc2[i]==-2){
	  red_delnode(perm[i]);
	}else if(deg_inc2[i]>=0){
	  b=perm[i];
	  a=perm[deg_inc2[i]];
	  tmp.clear();
	  tmp.insert(tmp.end(), { v,2,b,a });
	  Bfolding.push_back(tmp);
	  red_insert(b,complG[a]);
	  red_delnode(a);
	}else if(deg_inc3[i][0]>=0){
	  a=perm[i];
	  b=perm[deg_inc3[i][1]];
	  c=perm[deg_inc3[i][2]];
	  vector<int> va=complG[a];
	  vector<int> vb=complG[b];
	  vector<int> vc=complG[c];
	  tmp.clear();
	  tmp.insert(tmp.end(), { v,3,b,a,c }); //not a,b,c!
	  Bfolding.push_back(tmp);
	  red_insert(b,va);
	  red_insert(a,vc);
	  red_insert(c,vb);
	  red_insert(a,c);
	  red_insert(c,b);
	}
      }
      // fold v:
      red_delnode(v);deleted=true;
    }
    
  }
  return deleted;
}

bool reduce1(){
  int i,j,v,w,k,l;
  int a,b,c, tmpv;
  bool ab, ac, bc;
  int nume;
  bool deleted=false;
  bool found;
  for(v=0;v<Bmeret;++v){
    if(Btranslate[v]==-2 || Btranslate[v]==-7) continue;

    if(complG[v].size()==0){ //full node
      Btranslate[v]=-2; deleted=true;
    } else if(complG[v].size()==1){ //degree 1
      //delete dominated:
      w=complG[v][0];
      red_delnode(w);deleted=true;
      //delete dominating:
      Btranslate[v]=-2; 
    }
    if(deleted)continue;
    if(complG[v].size()>2){
      bool allconn;
      for(i=0;i<complG[v].size();++i){
	allconn=true;
	for(j=0;allconn&&j<complG[v].size();++j){
	  if(complG[v][i]==complG[v][j])continue;
	  for(w=0;allconn&&w<complG[complG[v][i]].size();++w)
	    allconn=(complG[complG[v][i]][w]==complG[v][j]);
	}
	if(allconn){
	  red_delnode(complG[v][i]);
	  deleted=true;
	}
      }
    }
  }
  return deleted;
}


void read_clq(string file_name){
  int i,j,n,e,x,y;
  string type,line;
  ifstream fin(file_name.c_str());
  if(!fin.is_open()){
    cout<<"ERROR opening file"<<endl;
    exit(1);
  }
  //eliminate comment lines
  while(fin.peek()=='c'){
    getline(fin,line);
    //comment=comment+"#"+line+'\n';
  }
  fin>>type; // p
  fin>>type; // edge
  fin>>meret; // vertexes
  fin>>e; // edges

  szomszedsagi.resize(meret);
  non_n.resize(meret);
  for(i=0;i<meret;++i){
    szomszedsagi[i].resize(meret);
    non_n[i].resize(meret);
  }

  for(i=0;i<e;i++){
    fin>>type; // e
    if(type=="e"){
      fin>>x;fin>>y;
      //cout<<"x: "<<x<<"; y: "<<y<<endl;
      szomszedsagi[x-1][y-1]=1;
      szomszedsagi[y-1][x-1]=1;
    }
  }
  fin.close();
  
  //complementer graph!
  /*
  for(i=0;i<meret;++i)
    for(j=0;j<meret;++j)
      if(i!=j)
	if(szomszedsagi[i][j]==1)szomszedsagi[i][j]=0;
	else szomszedsagi[i][j]=1;
  */
}

void read_hgr(string file_name){
  int i,j,k,l,v,x,y,e,s;
  string type,line;
  ifstream fin(file_name.c_str());
  if(!STDOUT){
    if(!fin.is_open()){
      cout<<"ERROR opening file"<<endl;
      exit(1);
    }
  }
  if(STDOUT){
    cin>>type; // p
    cin>>type; // td

    cin>>meret; // vertexes
    Bmeret=meret;
    cin>>e; // edges
    getline(cin,line);
    //cout<<"*"<<endl<<line<<endl<<"*"<<endl;
    //eliminate comment lines
    while(cin.peek()=='c'){
      getline(cin,line);
      comment=comment+"c"+line+'\n';
    }
    //cout<<comment;
  }else{
    fin>>type; // p
    fin>>type; // td

    fin>>meret; // vertexes
    Bmeret=meret;
    fin>>e; // edges
  
    cout<<"N: "<<meret<<", edges: "<<e<<endl;
    getline(fin,line);
    while(fin.peek()=='c'){
      getline(fin,line);
      comment=comment+"c"+line+'\n';
    }
  }
  
  //allocate apropriate space according to J:
  complG.resize(Bmeret);
  Btranslate.resize(Bmeret);
  perm.resize(Bmeret);
  non_n.resize(Bmeret);
  for(i=0;i<Bmeret;i++)
    non_n[i].resize(Bmeret);

  bool found;
  for(i=0;i<e;++i){
    if(STDOUT){
      cin>>x;cin>>y;
    }else{
      fin>>x;fin>>y;
      //cout<<"x: "<<x<<" y: "<<y<<" e: "<<i;
      if(x<1 || x>meret) cout<<"x HIBA! "<<x<<i<<endl;
      if(y<1 || y>meret) cout<<"y HIBA! "<<y<<i<<endl;
    }
    feladat.push_back(make_pair(x,y));
    --x;--y;
    //loop edges are in solution!:
    if(x==y){
      Btranslate[x]=-2;
      continue;}
    
    //if(szomszedsagi[x-1][y-1]==1)continue;
    //do not need double edges:
    found=false;
    for(j=0; j<complG[x].size() ;++j)
      if(complG[x][j]==y){found=true;break;} // true: double edge!
    
    if(!found){
      complG[x].push_back(y);
      complG[y].push_back(x);
    }
    /*
    szomszedsagi[x-1][y-1]=1;
    szomszedsagi[y-1][x-1]=1;
    if(x==y && translate[x-1]!=-7) {translate[x-1]=-7; ++del_count;}
    */
  }

  if(!STDOUT)fin.close();

  //delete loop edges
  for(v=0;v<Bmeret;++v)
    if(Btranslate[v]==-2){
      for(i=0;i<complG[v].size();++i)
	for(j=0;j<complG[complG[v][i]].size();++j)
	  if(complG[complG[v][i]][j]==v){
	    complG[complG[v][i]].erase(complG[complG[v][i]].begin()+j);
	    --j;}
      complG[v].clear();
    }
  while(reduce1());
  while(reduce2());
  meret=0;
  for(v=0;v<Bmeret;++v)
    if(Btranslate[v]!=-2 && Btranslate[v]!=-7) Btranslate[v]=-42;
  for(v=0;v<Bmeret;++v)
    if(Btranslate[v]!=-2 && Btranslate[v]!=-7){
      Btranslate_back.push_back(v);
      Btranslate[v]=meret++;
    }
  for(v=0;v<Bmeret;++v)if(Btranslate[v]==-42) {
      cerr<<"BAJ VAN!"<<endl;exit(3);}
  if(!STDOUT)cout<<"N: "<<meret<<endl;
  
  szomszedsagi.resize(meret);
  solution_line.resize(meret);
  solution_line.reset();
  tmp_line.resize(meret);
  non_n.resize(meret);
  perm.resize(meret);
  for(i=0;i<meret;i++){
    szomszedsagi[i].resize(meret);
    non_n[i].resize(meret);
    for(j=0;j<meret;++j)
      szomszedsagi[i][j]=0;
  }
  translate.resize(meret);
  for(i=0;i<meret;++i)
    translate[i]=i;
  for(i=0;i<meret;i++)
    for(j=0;j<meret;++j)
      if(i==j)szomszedsagi[i][j]=0;
      else szomszedsagi[i][j]=1;
  for(v=0;v<Bmeret;++v){
    if(Btranslate[v]==-2 || Btranslate[v]==-7) continue;
    for(i=0;i<complG[v].size();++i){
      if(Btranslate[complG[v][i]]==-2 || Btranslate[complG[v][i]]==-7){
	cerr<<"???"<<endl;exit(200);}
      szomszedsagi[Btranslate[complG[v][i]]][Btranslate[v]]=0;
    }
  }

  /*
      if(i!=j && translate[i]!=-7 && translate[j]!=-7){
	if(szomszedsagi[i][j]==1)szomszedsagi[i][j]=0;
	else szomszedsagi[i][j]=1;
      }else{
	szomszedsagi[i][j]=0;
      }
    }
    }*/
  if(meret==0){
    write_vc(file_name);
    exit(0);
  }
}

void write_vc(string file_name){
  int i,j,v;
  int szamol=0;
  int defold, tmpv;
  bool defold_dom;

  for(i=0;i<solution_line.size();++i)
    if(solution_line[i])
      if(true){ // folding to-do
	translate[translate_back[i]]=-2;
	++szamol;}
  
  if(!STDOUT){ cout<<"szamol: "<<szamol<<", solution_size: "<<solution_size;
    cout<<"-"<<solution_line.count()<<endl;
    cout<<"feladat meret "<<feladat.size()<<endl;}

  //de-folding
  for(i=folding.size()-1;i>=0;--i){
    tmpv=folding[i][0];
    defold_dom=true;
    for(;i>=0 && tmpv==folding[i][0]; --i)
      if(defold_dom && translate[folding[i][2]]==-2){
	translate[folding[i][3]]=-2;
	defold_dom=false;
      }
    if(defold_dom)
      translate[tmpv]=-2;
    ++i;
  }
  
  szamol=0;
  for(v=0;v<Bmeret;++v)
    if(Btranslate[v] >= 0 && translate[Btranslate[v]]==-2){
      Btranslate[v]=-2;
      ++szamol;
    }else if(Btranslate[v]==-2)
      ++szamol;

  //de-folding - B
  for(i=Bfolding.size()-1;i>=0;--i){
    tmpv=Bfolding[i][0];
    int tmpi=i;
    defold_dom=true;
    for(;i>=0 && tmpv==Bfolding[i][0]; --i){
      if(!defold_dom) continue;
      //if(i!=tmpi)cerr<<"tmpv: "<<tmpv<<" "<<i<<endl;
      //cout<<"v: "<<tmpv<<" i: "<<i<<endl;
      if(Bfolding[i][1]==2){ //2fold
	if(Btranslate[Bfolding[i][2]]==-2){
	  Btranslate[Bfolding[i][3]]=-2;
	  defold_dom=false;
	}
      }else if(Bfolding[i][1]==3){//3fold
	if(Btranslate[Bfolding[i][2]]==-2 &&
	   Btranslate[Bfolding[i][3]]==-2){ //xb && ya -> cz
	  Btranslate[Bfolding[i][4]]=-2;
	  defold_dom=false;
	}else if(Btranslate[Bfolding[i][2]]==-2 &&
		 Btranslate[Bfolding[i][3]]!=-2){ //xb && !ya -> ya
	  Btranslate[Bfolding[i][3]]=-2;
	  defold_dom=false;
	}else if(Btranslate[Bfolding[i][2]]!=-2 &&
		 Btranslate[Bfolding[i][3]]==-2){ //!xb && ya -> zc
	  Btranslate[Bfolding[i][4]]=-2;
	  defold_dom=false;
	}else if(Btranslate[Bfolding[i][4]]==-2){ //zc -> xb
	  Btranslate[Bfolding[i][2]]=-2;
	  defold_dom=false;
	}
      }else{cerr<<"wrong folding code"<<endl;exit(23);}
      //break;
    }
    if(defold_dom)
      Btranslate[tmpv]=-2;
    ++szamol;
    ++i;
  }

  bool found_node;
  for(i=0;i<feladat.size();++i){
    found_node=false;
    for(j=0;!found_node && j<Bmeret;++j)
      found_node=Btranslate[j]!=-2&&
	(j+1==feladat[i].first||j+1==feladat[i].second);
    if(!found_node){
      if(!STDOUT) {
	cerr<<"Wrong cover! missing edge:"<<endl;
	cerr<<feladat[i].first<<" "<<feladat[i].second<<endl;
      }
      exit(100);
    }
  }
      
  if(STDOUT){
    //cout<<"s vc "<<meret<<" "<<meret-solution_size-sol_count<<endl;
    cout<<"s vc "<<Bmeret<<" "<<Bmeret-szamol<<endl;
    for(i=0;i<Bmeret;++i)
      if(Btranslate[i]!=-2)
	cout<<i+1<<endl;
  }else{
    file_name=file_name+".vc";
    //  ifstream fin("matrix-mon-5.txt");
    ofstream fout(file_name.c_str());
    //ifstream fin("matrix.txt");
    if(!fout.is_open()){
      cout<<"ERROR opening file"<<endl;
      exit(1);
    }
  
    //fout<<"s vc "<<meret<<" "<<meret-solution_size-sol_count<<endl;
    fout<<"s vc "<<Bmeret<<" "<<Bmeret-szamol<<endl;
  
    for(i=0;i<Bmeret;++i){
      if(Btranslate[i]!=-2)
	fout<<i+1<<endl;
    }
    fout.close();
  }
  //cerr<<"megszamoltam: "<<megszamol2xsok<<endl;
}

int main(int argc, char **argv)
{
  string file_name;
  if(!STDOUT){
    if(argc<2){
      cout<<"usage: "<<endl<<argv[0]<<" IN_FILE.clq"<<endl;
      return 1;
    }
    file_name=argv[1];
  } else file_name="stdout";
  
  long long nsum=0;
  time_t tsum0, tsum1, tsum2;
  int i,j;
  bool deleted=true;
  
  tsum0=clock();
  //read_clq(file_name);
  read_hgr(file_name);
  
  //init(szomszedsagi);
  inc.resize(meret);
  for(i=0;i<meret;++i)
    inc[i].resize(meret);
  for(i=0;i<meret;++i)
    for(j=0;j<meret;++j){
      inc[i][j]=szomszedsagi[i][j];
      if(j<i && inc[i][j]!=inc[j][i]){
	cout<<"incERROR"<<endl;
	exit(17);
      }
    }

  for(i=0;i<meret;++i)
    if(translate[i]!=-2 && translate[i]!=-7  && inc[i].none()){
      translate[i]=-7;
      ++del_count;
    }
  //dirty if all not connected
  if(del_count==meret){
    translate[meret-1]=-2;
    --del_count;
    ++sol_count;
    }
  
  if(!STDOUT) {
    cout<<"in vc: "<<del_count<<endl;
    cout<<"in clique: "<<sol_count<<endl;
  }

  // KITOROLVE!!
  /*
  int deleted_count;
  if(!fold1())deleted_count=2;
  else deleted_count=0;
  while(deleted_count<2 && sol_count<meret){ // uresen ne tovabb!!!
    if(basic()){deleted_count=0;continue;}else{++deleted_count;}
    if(fold1()){deleted_count=0;continue;}else{++deleted_count;}
  }
  */
  
  if(sol_count==meret){
    if(!STDOUT)cout<<"sol_count==meret"<<endl;
    write_vc(file_name);
    return 0;
  }

  int s=0;
  for(i=0;i<meret;++i)
    if(inc[i].any())perm[s++]=i;

  if(!STDOUT) cout<<"s: "<<s<<endl;
  if(s==0){
    for(j=0,i=0;i<meret;++i)
      if(translate[i]==-2)++j;
    if(!STDOUT)cout<<"-2: "<<j<<endl<<"s==0"<<endl;
    write_vc(file_name);
    //cout<<meret<<endl;
    return 0;
  }

  szomszedsagi.resize(s);
  translate_back.resize(s);
  for(i=0;i<s;++i)
    szomszedsagi[i].resize(s);
  solution_line.resize(s);
  
  for(i=0;i<meret;++i)
    if(translate[i]!=-2)translate[i]=-42;
  for(i=0;i<s;++i){
    if(translate[perm[i]]==-2){cerr<<"Hibas osszehuzas!"<<endl;exit(42);}
    translate[perm[i]]=i;
    translate_back[i]=perm[i];
    for(j=0;j<s;++j)
      szomszedsagi[i][j]=inc[perm[i]][perm[j]];
  }
  
  /*
  cout<<solution_line.size()<<endl;
  for(j=0;j<meret;++j)
    cout<<translate[j]<<",";
  cout<<endl<<endl<<"translate:"<<endl;
  */
  init(szomszedsagi);

  //a fentiek helyett:
  /*
  translate_back.resize(meret);
  for(i=0;i<meret;++i)
    translate_back[i]=i;
  */
  
  k_clique(szomszedsagi, -1, file_name, true);
  max_num_color=num_color;
  int colsumtmp=0;
  for(int i=0;i<max_num_color;++i){
    //cout<<col_buck[i]<<endl;
    colsumtmp+=col_buck[i].count();
  }
  if(!STDOUT) cout<<"nodes colored: "<<colsumtmp<<endl;

  //k=max_level;
  k=maxclq(szomszedsagi);
  solution_line=stack_out[0];
  solution_size=k;
  if(!STDOUT)cout<<"First max clique: "<<k<<endl;
  ++k;
  tsum2=clock();


  bool found=true;
//for(; !found && k>0; --k){
  for(; found; ++k){
    for(i=0;i<N;++i)
      if(inc[i].none()){
	  translate[translate_back[i]]=-7;
	  ++del_count;
      }
    deleted=true;
    while(deleted){
      if(deleted=node_prune()) continue;
      //if(deleted=edge_prune3()) continue;
    }
    //HA URES LEALLNI?
    found=k_clique(szomszedsagi, k, file_name, false);
    if(found) {solution_line=stack_out[level]; solution_size=k;}
    //cerr<<"SOL SIZE: "<<solution_size<<endl;
    //cerr<<solution_line<<endl;
    nsum += n;
  }
  tsum1=clock();

  if(!STDOUT){
    cout<<endl<<endl<<"*******************************************"<<endl<<endl;
    cout<<"+"<<file_name<<": solution: "<<k-2<<endl;
    cout<<"+"<<file_name<<": (k+1)time: "<<ktime<<endl;
    cout<<"+"<<file_name<<": (k+1)nsum: "<<knsum;
    //cout<<"+"<<file_name<<": (k+1)time: "<<k_1time<<endl;
    //cout<<"+"<<file_name<<": (k+1)nsum: "<<k_1nsum;
    cout<<"\t /10^3: "<<(knsum+500)/1000;
    cout<<"k\t /10^6: "<<(knsum+500000)/1000000<<"M"<<endl;
    cout<<endl<<"+"<<file_name<<": FULL time elapsed: "<<difftime(tsum1,tsum0)/CLOCKS_PER_SEC<<endl;
    cout<<endl<<"--------------------------"<<endl;
    cout<<"+"<<file_name<<": nsum: "<<nsum;
    cout<<"\t /10^3: "<<(nsum+500)/1000;
    cout<<"k\t /10^6: "<<(nsum+500000)/1000000<<"M"<<endl;
    cout<<endl<<"+"<<file_name<<": coloring time: "<<difftime(tsum2,tsum0)/CLOCKS_PER_SEC<<endl;
  }
  write_vc(file_name);
  return 0;
}


bool full_nodes(){
  int v,i,j;
  int empty_nodes=0;
  bool deleted=false;
  
  for(v=0;v<meret;++v)
    if(inc[v].none())++empty_nodes;
  if(empty_nodes!=del_count+sol_count){
    cerr<<"szamolasi hiba empty nodes2"<<endl;
    cerr<<"empty :"<<empty_nodes<<" del: "<<del_count;
    cerr <<" sol: "<<sol_count<<endl;
    exit(42);}
  for(v=0;empty_nodes+1<meret && v<meret;++v){
    if(inc[v].count()==meret-empty_nodes-1){
      ++sol_count;
      ++empty_nodes;
      translate[v]=-2;
      //cerr<<"sol1: "<<v<<endl;
      deleted=true;
      //utolso csucsot berak!!
      if(empty_nodes+1==meret){
	for(i=0;!inc[v][i];++i);
	translate[i]=-2;
	//cerr<<"sol2: "<<i<<endl;
	++empty_nodes;++sol_count;
      }
      for(i=0;i<meret;++i){
	inc[v][i]=0;
	inc[i][v]=0;
	szomszedsagi[v][i]=0;
	szomszedsagi[i][v]=0;
      }
    }
  }
  return deleted;
}

void delete_node(int v){
      ++del_count;
      translate[v]=-7;
      if(inc[v].any())
	for(int i=0;i<meret;++i){
	  inc[v][i]=0;
	  inc[i][v]=0;
	  szomszedsagi[v][i]=0;
	  szomszedsagi[i][v]=0;
	}
}

void delete_full(int v){
      ++sol_count;
      translate[v]=-2;
      for(int i=0;i<meret;++i){
	inc[v][i]=0;
	inc[i][v]=0;
	szomszedsagi[v][i]=0;
	szomszedsagi[i][v]=0;
      }
}

void delete_fold(int v){
  translate[v]=-7; // ??? -3 volt!!!
      for(int i=0;i<meret;++i){
	inc[v][i]=0;
	inc[i][v]=0;
	szomszedsagi[v][i]=0;
	szomszedsagi[i][v]=0;
      }
}

bool basic(){
  int i,j,v,s;

  bool deleted=false;
  int empty_nodes=0;

  for(v=0;v<meret;++v)
    if(inc[v].none())++empty_nodes;
  if(empty_nodes!=del_count+sol_count){
    cerr<<"szamolasi hiba empty nodes1"<<endl;
    cerr<<"empty :"<<empty_nodes<<" del: "<<del_count<<" sol: "<<sol_count<<endl;
    exit(42);}
  for(v=0;v<meret;++v){
    if(translate[v]==-7 ||translate[v]==-2) continue;
    // full nodes ide?
    if(empty_nodes+2<meret &&
       inc[v].count()==meret-empty_nodes-2){ //egy hianyzik!
      deleted=true;
      for(j=0;
	  j==v ||
	    translate[j]==-7 ||translate[j]==-2 ||
	    inc[v][j];
	  ++j);
      delete_node(j);++empty_nodes;
      delete_full(v);++empty_nodes;
    }else if(empty_nodes+3<meret &&
	     inc[v].count()==meret-empty_nodes-3){ //ketto hianyzik!
      int a,b;
      for(a=0;
	  a==v||
	    translate[a]==-7||translate[a]==-2||
	    inc[v][a] ;
	  ++a);
      for(b=a+1;
	  b==v||
	    translate[b]==-7||translate[b]==-2||
	    inc[v][b] ;
	  ++b);
      if(!inc[a][b]){ // nincsenek osszekotve
	delete_node(a);++empty_nodes;      deleted=true;
	delete_node(b);++empty_nodes;
	delete_full(v);++empty_nodes;
      }else{ // ossze vannak kotve -> 2fold
	vector<int> tmp;
	tmp.insert(tmp.end(), { v,2,a,b });
	folding.push_back(tmp);
	tmp_line=inc[a]&inc[b];
	//translate[a]=-4;
	++fold_count;
	for(i=0;i<meret;++i){
	  inc[a][i]=tmp_line[i];
	  inc[i][a]=tmp_line[i];
	  szomszedsagi[a][i]=tmp_line[i];
	  szomszedsagi[i][a]=tmp_line[i];
	}
	delete_fold(v);++sol_count;++empty_nodes;
	delete_fold(b);++del_count;++empty_nodes;
      }
    }
    //utolso csucsot berak!!
    if(empty_nodes+1==meret){
      for(i=0;translate[i]>=0;++i);
      translate[i]=-2;
      //cerr<<"sol2: "<<i<<endl;
      ++empty_nodes;++sol_count;
    }

  }

  deleted = deleted || full_nodes();

  if(!STDOUT) {
    cout<<"del count (in vc): "<<del_count<<endl;
    cout<<"sol count (in clique): "<<sol_count<<endl;
    cout<<"fold count: "<<fold_count<<endl;
  }
  return deleted;
}

bool fold1(){
  int i,j,v,s,k;

  bool deleted=false;
  int empty_nodes=0;

  /*
  for(v=0;v<meret;++v)
    if(inc[v].none()){
      ++empty_nodes;
      if(empty_nodes<meret && (translate[v]>=0 || translate[v]==-4)){
        ++del_count;
        translate[v]=-7;
      }else if(empty_nodes==meret&&(translate[v]>=0 || translate[v]==-4)){
        ++sol_count;
        translate[v]=-2;
      }
      }*/
  
  for(v=0 ; v<meret && empty_nodes<meret ; ++v){
    if(inc[v].none()){
      if(translate[v]<0){
	continue;
      }else if(empty_nodes<meret){
	++empty_nodes;
	++del_count;
	translate[v]=-7;
      }else if(empty_nodes==meret){
	++empty_nodes;
	++sol_count;
	translate[v]=-2;
      }
    }else if(inc[v].count()==meret-empty_nodes-1){
      ++sol_count;
      ++empty_nodes;
      translate[v]=-2;
      deleted=true;
      //utolso csucsot berak!!
      if(empty_nodes+1==meret){
	for(i=0;!inc[v][i];++i);
	translate[i]=-2;
	++empty_nodes;++sol_count;
      }
      for(i=0;i<meret;++i){
	inc[v][i]=0;
	inc[i][v]=0;
	szomszedsagi[v][i]=0;
	szomszedsagi[i][v]=0;
      }
    }else{
      size_non_n=meret-inc[v].count()-1-del_count-sol_count;
      s=0;
      for(i=0;i<meret;++i){
	//non_n[i].reset();
	//if(!inc[v][i] && translate[i]>=0) perm[s++]=i;
	if(i!=v && !inc[v][i] && inc[i].any()) perm[s++]=i;
	if(i==v && inc[v][i])cerr<<i<<" "<<v<<endl;
      }
      if(size_non_n!=s){
	cerr<<"szamolasi hiba size_non_n"<<endl;
	cerr<<"s: "<<s<<" size_non_n: "<<size_non_n<<endl;
	exit(42);}
      if(s==0) continue;
      for(i=0;i<s;++i)
	non_n[i].reset();
      
      for(i=0;i<s;++i)
	for(j=0;j<s;++j)
	  non_n[i][j]=inc[perm[i]][perm[j]];
      
      for(j=0;j<s;++j)
	if(non_n[j].none()){
	  ++del_count;
	  translate[perm[j]]=-7;
	  deleted=true;
	  if(inc[perm[j]].any())
	    for(i=0;i<meret;++i){
	      inc[perm[j]][i]=0;
	      inc[i][perm[j]]=0;
	      szomszedsagi[perm[j]][i]=0;
	      szomszedsagi[i][perm[j]]=0;
	    }
	}
      bool allfold=true;
      for(i=0;allfold && i<s;++i)
	allfold = allfold && (non_n[i].count()==1);
      if(allfold){
	for(i=0;i<s;++i){
	  if(non_n[i].count()==1){
	    for(j=0;j<s && !non_n[i][j] ;++j);
	    vector<int> tmp;
	    tmp.insert(tmp.end(), { v,2,perm[i],perm[j] });
	    folding.push_back(tmp);
	    tmp_line=inc[perm[i]]&inc[perm[j]];
	    //translate[perm[i]]=-4;
	    for(k=0;k<meret;++k){
	      inc[perm[i]][k]=tmp_line[k];
	      inc[k][perm[i]]=tmp_line[k];
	      szomszedsagi[perm[i]][k]=tmp_line[k];
	      szomszedsagi[k][perm[i]]=tmp_line[k];
	    }
	    delete_fold(perm[j]);++del_count;	  
	    non_n[i][j]=0;
	    non_n[j][i]=0;	  
	  }
	}
	delete_fold(v);++sol_count;	
	++fold_count;
      }
    }
  }
  for(v=0;v<meret;++v)
    if(inc[v].none()){
      ++empty_nodes;
      if(empty_nodes<meret && (translate[v]>=0 || translate[v]==-4)){
        ++del_count;
        translate[v]=-7;
      }else if(empty_nodes==meret&&(translate[v]>=0 || translate[v]==-4)){
        ++sol_count;
        translate[v]=-2;
      }
    }
  if(!STDOUT) {
    cout<<"1del count (in vc): "<<del_count<<endl;
    cout<<"1sol count (in clique): "<<sol_count<<endl;
    cout<<"1fold count: "<<fold_count<<endl;
  }
  return deleted;
}

bool node_prune(){

  int v,i,j,c;
  bool deleted=false;

  for(v=0;v<N;++v){
    if(inc[v].none()) continue;
    j=1; //onmagaval egyutt
    for(c=0;c<max_num_color;++c)
      if((inc[v]&col_buck[c]).any()) ++j;
    
    if(j<k){ // torlendo!
      ++node_pruned;
      //translate[v]=-7;
      deleted=true;
      if(!STDOUT) cout<<v<<", ";
      for(i=0;i<N;++i){
	inc[v][i]=0;
	inc[i][v]=0;
	szomszedsagi[v][i]=0;
	szomszedsagi[i][v]=0;
      }
    }
  }
  
  if(!STDOUT) {
    cout<<"del count (in vc): "<<del_count<<endl;
    cout<<"sol count (in clique): "<<sol_count<<endl;
    cout<<"node pruned: "<<node_pruned<<endl;
  }
  return deleted;
}

//ez meg rossz:
/*
bool node_prune3(){

  int v,i,j,c,z,c1,c2,j1,j2;
  //long long node_pruned=0;
  bool deleted=false;
  bool is_deleted;
  bool is_node;
  boost::dynamic_bitset<> line;
  line.resize(meret);
  
  for(v=0;v<N;++v){
    if(inc[v].none()) continue;
    line=inc[v];
    
    is_deleted=false;
    for(c1=0;c1<max_num_color&&!is_deleted;++c1){
      if(colors_best[v]==c1) continue;
      for(c2=c1+1;c2<max_num_color&&!is_deleted;++c2){
	if((colors_best[v]==c2) continue;
	
	is_node=false;
	for(j1=0;j1<colors[c1].size() &&!is_node;++j1)
	  if(line[colors[c1][j1]])
	    for(j2=0;j2<colors[c2].size() &&!is_node;++j2)
	      if(line[colors[c2][j2]] &&
		 adj[colors[c1][j1]][colors[c2][j2]])
		is_node=true;
	if(!is_node){ // torlendo!
	  ++node_pruned;
	  deleted=true;
	  is_deleted=true;
	  cout<<v<<", ";
	  for(i=0;i<N;++i){
	    adj[v][i]=0;
	    adj[i][v]=0;
	  }
	}
      }
    }
  }
  cout<<"node3 pruned: "<<node_pruned<<endl;
  
  return deleted;
  }*/
  
bool edge_prune3(){

  int v,u,i,j,j1,j2,c,c1,c2,z;
  //long long edges_pruned=0;

  bool deleted=false;
  bool is_edge;
  bool is_deleted;
  boost::dynamic_bitset<> line;
  line.resize(meret);
  
  for(v=0;v<N;++v)
    for(u=v+1;u<N;++u){
      if(!inc[v][u]) continue;
      line=inc[v]&inc[u];
      j=2; //onmagukkal egyutt
      
      for(c=0;c<max_num_color;++c)
	if((line&col_buck[c]).any()) ++j;
      if(j<k){ // torlendo!
	++edges_pruned;
	deleted=true;
	inc[v][u]=0;
	inc[u][v]=0;
	szomszedsagi[v][u]=0;
	szomszedsagi[u][v]=0;
      }
    }
  
  if(!STDOUT)cout<<"edges3 pruned: "<<edges_pruned<<endl;
  
  return deleted;
}
