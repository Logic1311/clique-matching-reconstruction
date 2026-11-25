#include <algorithm>
#include <cassert>
#include <cstdint>
#include <iostream>
#include <set>
#include <vector>
using namespace std;
using M = uint64_t;
int pc(M x){return __builtin_popcountll(x);} 
int bit(M x){return __builtin_ctzll(x);} 
M full(int n){return (M(1)<<n)-1;}
using Graph=vector<M>;
Graph build(int a,int d,int k){
 Graph g(a+d); for(int i=0;i<a+d;i++)g[i]=(i<a?full(a):full(a+d)^full(a))^(M(1)<<i);
 for(int i=0;i<k;i++){g[i]|=M(1)<<(a+i);g[a+i]|=M(1)<<i;}return g;
}
// Exact recognition by examining every possible large-clique candidate containing
// a fixed maximum-degree vertex. For k>0 such a vertex must be in a size-a clique.
// (a=d or a=d+1.) No assumption about the structure of the input graph is made.
bool recognize(const Graph& g,M verts,int a,int d,int k){
 int m=0, anchor=-1, maxdeg=-1;
 for(M t=verts;t;t&=t-1){int i=bit(t),q=pc(g[i]&verts);m+=q;if(q>maxdeg){maxdeg=q;anchor=i;}}
 if(m!=a*(a-1)+d*(d-1)+2*k || maxdeg!=a-1+(k>0))return false;
 M ns=g[anchor]&verts;
 auto check=[&](M X){M Y=verts^X;
   if(pc(X)!=a || pc(Y)!=d)return false;
   for(M t=X;t;t&=t-1){int i=bit(t); if(pc(g[i]&X)!=a-1 || pc(g[i]&Y)>1)return false;}
   for(M t=Y;t;t&=t-1){int i=bit(t); if(pc(g[i]&Y)!=d-1 || pc(g[i]&X)>1)return false;}
   return true;};
 if(maxdeg==a-1)return check(ns|(M(1)<<anchor));
 for(M t=ns;t;t&=t-1)if(check((ns^(M(1)<<bit(t)))|(M(1)<<anchor)))return true;
 return false;
}
int main(int argc,char**argv){int limit=argc>1?stoi(argv[1]):9; if(limit<3||limit>15){cerr<<"Limit must be 3..15 (large cases are expensive).\n";return 2;} uint64_t total=0;
 cout<<"c,b,ally,adversary,labelled_extensions,distinct_blocker_profiles,verified_subdecks,classified_extensions\n";
 for(int c=3;c<=limit;c++)for(int b=2;b<c;b++){
  int s=c-b,n=2*c; M all=full(n),old=full(n-1);set<pair<int,int>> profiles;
  uint64_t count=0, classified=0; int checked=0;
  for(int t=b-1;t<=b;t++){
   Graph g=build(c,c-1,t);g.push_back(0);
   for(M mask=0;mask<=old;mask++){
    ++count;g.back()=mask;for(int i=0;i<n-1;i++){g[i]&=old;if(mask&(M(1)<<i))g[i]|=M(1)<<(n-1);}
    if(recognize(g,all,c,c,b))continue;
    int A=0,B=0; for(int i=0;i<n;i++){M v=all^(M(1)<<i); A+=recognize(g,v,c,c-1,b-1); B+=recognize(g,v,c,c-1,b);}
    if(c>=4 && A+B>=4){
      bool classified_ok=false;
      for(int k=0;k<=c;k++){
        if(recognize(g,all,c,c,k)) { classified_ok=true; break; }
        if(k<c && recognize(g,all,c+1,c-1,k)) { classified_ok=true; break; }
      }
      assert(classified_ok); ++classified;
    }
    profiles.emplace(min(A,2*b),min(B,2*s));
   }
  }
  int ally=n+1,adv=0;
  for(auto [a,d]:profiles)adv=max(adv,a+d+1);
  for(int a=0;a<=2*b;a++)for(int d=0;d<=2*s;d++){
   bool blocked=false;for(auto [x,y]:profiles)if(x>=a&&y>=d){blocked=true;break;}
   if(c>=4){
     bool predicted_blocked = (a<=2*(s+1) && d==0) || (a==0 && d<=2*(b+1)) || (a<=b && d<=s+1);
     assert(blocked==predicted_blocked); ++checked;
   }
   if(!blocked)ally=min(ally,a+d);
  }
  int predicted=s==1?min(b+2,max(4,b)+1):min(b+2,s+3);
  assert(ally==predicted); assert(adv==c+2); total+=count;
  cout<<c<<","<<b<<","<<ally<<","<<adv<<","<<count<<","<<profiles.size()<<","<<checked<<","<<classified<<"\n";
 }
 cerr<<"Total labelled extensions (including duplicate representations): "<<total<<"\n";
}
