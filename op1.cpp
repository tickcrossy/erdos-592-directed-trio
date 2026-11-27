#include <array>
#include <algorithm>
#include <vector>
#include <cstdio>
#include <string>
#include <cstdlib>
using namespace std;
struct Search {
 int n,d,epoch=0; vector<int> stamp; string s; array<int,32> ev,od;
 Search(int N):n(N),d(n+1),stamp(d*d*d*8) { for(int i=0;i<=n;i++)ev[i]=i+(i%2),od[i]=i+1-(i%2); }
 char path[400]; int steps=0;
 bool visit(int a,int b,int c,int m){
  if(a==n&&b==n&&c==n&&m==7)return 1;
  int id=(((a*d+b)*d+c)*8)+m;
  if(stamp[id]==epoch)return 0;
  stamp[id]=epoch;
  if(b<n&&c<n&&((b%2)||(m&2))&&((c%2)||(m&4))){
   int j=od[b],k=od[c],q=m;
   if(j!=b)q&=5;
   if(k!=c)q&=3;
   if(s[j]<=s[k])q|=2;
   if(s[k]<=s[j])q|=4;
   if(visit(a,j,k,q)){path[steps++]='z';return 1;}
  }
  if((a%2==0||(m&1))&&(b%2==0||(m&2))){
   int i=ev[a],j=ev[b],q=m;
   if(i!=a)q&=6;
   if(j!=b)q&=5;
   if(s[i]<=s[j])q|=1;
   if(s[j]<=s[i])q|=2;
   if(visit(i,j,c,q)){path[steps++]='x';return 1;}
  }
  if(a<n&&(a%2||(m&1))&&(c%2==0||(m&4))){
   int i=od[a],k=ev[c],q=m;
   if(i!=a)q&=6;
   if(k!=c)q&=3;
   if(s[i]<=s[k])q|=1;
   if(s[k]<=s[i]&&(k==n||s[k]!='2'||i>k))q|=4;
   if(visit(i,b,k,q)){path[steps++]='y';return 1;}
  }
  return 0;
 }
 void verify(int init) {
  array<string,3> labels{}, maxima{};array<int,3> lastWeight{-1,-1,-1};
  vector<bool> designated(n+1,false);
  string word="xy";
  for(int i=2;i<=init;i++)word+=i%2?'y':'x';
  word+='z';
  for(int i=steps-1;i>=0;i--)word+=path[i];
  const string pairs[3]={"xy","xz","yz"};
  for(char l:word){
   int pos[3];char wt='2';
   for(int k=0;k<3;k++){
    bool involved=pairs[k].find(l)!=string::npos;
    if(involved&&(labels[k].empty()||labels[k].back()!=l)){labels[k]+=l;maxima[k]+='0';}
    pos[k]=int(labels[k].size())-1;
    if(involved){if(pos[k]<0||pos[k]>n)abort();wt=min(wt,s[pos[k]]);}
   }
   for(int k=0;k<3;k++)if(pairs[k].find(l)!=string::npos)maxima[k].back()=max(maxima[k].back(),wt);
   int k=l-'x';if(lastWeight[k]<0&&wt!='2')abort();lastWeight[k]=wt;
   if(l=='y'&&wt=='2'&&pos[0]>pos[2]&&pos[0]%2==1&&pos[2]%2==0)designated[pos[2]]=true;
  }
  for(int k=0;k<3;k++)if(maxima[k]!=s||lastWeight[k]!='2')abort();
  for(int j=2;j<n;j+=2)if(s[j]=='2'&&!designated[j])abort();
 }
 bool test(const string& a){steps=0;
  s=a;epoch++;
  int E=n-4;while(E>=4&&s[E]!='2')E-=2;
  for(int i=max(E-1,1);i<=n;i++)if(visit(i,1,1,7)){verify(i);return 1;}
  for(int i=1;i<E-1;i++)if(visit(i,1,1,7)){verify(i);return 1;}
  return 0;
 }
};
struct Enumeration{
 int n; Search search;string s;long long reps=0,other=0;
 Enumeration(int N):n(N),search(n),s(n+1,'2'){}
 void gen(int i,bool peak){
  if(i==n-1){if(!peak)return;string rev(s.rbegin(),s.rend());if(rev<s)return; reps++;
   if(!search.test(s)){other++;if(!search.test(rev)){printf("negative %s\n",s.c_str());fflush(stdout);exit(1);}}return;
  }
  for(char ch='0';ch<='2';ch++){
   if(ch=='2'&&(s[i-1]=='2'||i==n-2))continue;
   s[i]=ch;gen(i+1,peak||(ch=='2'&&i%2==0));}
 }
};

int main(int argc, char** argv) {
    for (int index = 1; index < argc; ++index) {
        int n = atoi(argv[index]);
        if (n < 8 || n > 22 || n % 2 != 0) {
            fprintf(stderr, "Expected an even final index from 8 through 22.\n");
            return 2;
        }
        Enumeration enumeration(n);
        enumeration.gen(2, false);
        printf("length %d; classes %lld; reversed %lld\n",
               n + 1, enumeration.reps, enumeration.other);
    }
}
