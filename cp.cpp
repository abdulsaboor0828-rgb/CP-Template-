/*

Author ---> TheAlgoForge
Institute ---> NIT-Jalandhar
Date of Submission ---> XX/XX/XXXX
Time of Submission ---> XX:XX

*/

#pragma GCC optimize("Ofast")
#pragma GCC optimize("unroll-loops")
#pragma GCC target("avx2")
#pragma GCC optimize("O2")

#include<bits/stdc++.h>
#include <unordered_set>
#include <ext/pb_ds/assoc_container.hpp>
#include <ext/pb_ds/tree_policy.hpp>
using namespace std;
#define ll long long  
#define vi vector<int>
#define vll vector<ll>
#define vvi vector<vi>
#define vvll vector<vll>
#define vstr vector<string>
#define vch vector<char>
#define vb vector<bool>
#define vvb vector<vector<bool>>
#define pll pair<ll, ll>
#define vpl vector<pll>
#define vi2 vector<array<int,2>>
#define vll2 vector<array<ll,2>>
#define ump unordered_map
#define all(a) (a).begin(), (a).end()
#define rall(a) (a).rbegin(), (a).rend()
#define rep(i, a, b) for (int i = (a); i < (b); ++i)
#define rrep(i, a, b) for (int i = (a); i >= (b); --i)
#define forr(i, a, b) for (ll i = a; i <= b; i++)
#define pb push_back
#define ppb pop_back
#define ins insert
#define ers erase
#define srt(v) sort(all(v))
#define rsrt(v) sort(rall(v))
#define rev(v) reverse(all(v))
#define sum(v) accumulate(all(v), 0LL)
#define mx(v) *max_element(all(v))
#define mn(v) *min_element(all(v))
#define Cnt(v, x) count(all(v), (x))
#define up upper_bound
#define lb lower_bound

const int SINF = 1000000000;
const ll INF = 1e18;
const int MOD = 1e9 + 7;
const int MAXN = 4e5 + 5;
const int N = 1e5 + 1;
const int LOG = 20;
 
ll MOD2 = 998244353;

ll bin_exp(ll a, ll b, ll mod){a %= mod; ll ans = 1;while(b > 0){if(b & 1){ans = (ans * a) % mod;}a = (a * a) % mod;b >>= 1;}return ans;}
ll bin_exp(ll a, ll b){ll ans = 1;while(b > 0){if(b & 1){ans *= a;}a *= a;b >>= 1;}return ans;}
ll gcd(ll a, ll b){while(b){a %= b; swap(a, b);} return a;}
ll lcm(ll a, ll b){return a/gcd(a, b)*b;}
ll inv(ll x) { return bin_exp(x % MOD, MOD - 2, MOD); }
ll gcd_ext(ll a, ll b, ll& x, ll& y) {if (b == 0) {x = 1;y = 0;return a;}ll x1, y1;ll d = gcd_ext(b, a % b, x1, y1);x = y1; y = x1 - y1 * (a / b);return d;}
ll mod_inv(ll a, ll m) {
    ll x, y;
    ll g = gcd_ext(a, m, x, y);
    if (g != 1) {
        return -1;
    }
    else {
        x = (x % m + m) % m;
        return x;
    }
}
ll fact[1000001];
void factorial() {
    fact[0]=1;ll i;
    forr(i,1,1000000)
        fact[i]=(i*fact[i-1])%MOD2;
}
ll nck(ll n, ll k) {
    if (n >= k)
        return (((fact[n] * (mod_inv(fact[k], MOD))) % MOD) * mod_inv(fact[n - k], MOD)) % MOD;
    else
        return 0;
}

vector<ll> primes;
vector<bool> prime;
vector<int> lp;

// Linear Sieve->O(N)
void linear_seive(int n){lp.resize(n+1);for (int i=2; i <= n; ++i) {if (lp[i] == 0) {lp[i] = i;primes.push_back(i);}for (int j = 0; i * primes[j] <= n; ++j) {lp[i * primes[j]] = primes[j];if (primes[j] == lp[i]) {break;}}}}
// Sieve Of Eratosthenes->O(NLOG(LOG(N)))
void sieve(int n){prime.resize(n + 1);for (int p = 0; p <= n; p++) {prime[p] = 1;}for (int p = 2; p * p <= n; p++) {if (prime[p] == true) {for (int i = p * p; i <= n; i += p)prime[i] = false;}}for (int p = 2; p <= n; p++)if (prime[p])primes.pb(p);}

vector<int> segTree;
vector<int> flatTree;
// void resetEuler(){ idx = 0; flatTree.clear(); eularTourMap1.clear(); eularTourMap2.clear(); }
// build the segment tree
void build(vector<int>& arr, int start, int end, int index){
    // Time Complexity - O(n)
    if(start == end){ segTree[index] = arr[start]; return;}
    // index of nodes start from 1--> 2--> 3 and so on
    int left = 2*index, right = 2*index+1, mid = (start+end)/2;
    build(arr, start, mid, left);
    build(arr, mid+1, end, right);
    segTree[index] = segTree[left] + segTree[right];
}
void update(vector<int>& arr, int start, int end, int index, int pos, int value){
    // Time Complexity - O(log(n))
    if(start == end){ arr[pos] = value; segTree[index] = value; return; }
    int mid = (start+end)/2;
    if(mid >= pos) update(arr, start, mid, 2*index, pos, value);
    else update(arr, mid+1, end, 2*index+1, pos, value);
    segTree[index] = segTree[2*index] + segTree[2*index+1];
}
int query(int start, int end, int index, int l, int r){
    // Time Complexity - O(logn)
    // Complete Overlap
    if(l <= start && end <= r) return segTree[index];
      // Disjoint
    if(l > end || r < start) return 0;
    int mid = (start+end)/2;
    return query(start, mid, 2*index, l, r) + query(mid+1, end, 2*index+1, l, r);
}
map<int,int>eularTourMap1;
map<int,pair<int,int>>eularTourMap2;
int idx=0;
void eularTourDfs1(int node, int par, vector<int> adj[]){
    if(eularTourMap1.find(node) == eularTourMap1.end())
        eularTourMap1[node] = idx;
    flatTree.pb(node);
    idx++;
    for(auto it: adj[node]){
        if(it != par){
            eularTourDfs1(it, node, adj);
            flatTree.pb(node);
            idx++;
        }
    }
}
void eularTourDfs2(int node, int par, vector<int> adj[]){
    flatTree.pb(node);
    eularTourMap2[node].first = idx++;
    for(auto it: adj[node])
        if(it != par) eularTourDfs2(it, node, adj);
    flatTree.pb(node);
    eularTourMap2[node].second = idx++;
}

// ------------------ GRAPH ALGORITHMS ------------------

void Dijkstra(int s, int n, vll &dist, vi &parent, vpl *adj){
    dist.assign(n+1,INF); parent.assign(n+1,-1);
    priority_queue<pll,vector<pll>,greater<pll>> pq;
    dist[s]=0; pq.push({0LL,(ll)s});
    while(!pq.empty()){
        ll d=pq.top().first, u=pq.top().second; pq.pop();
        if(d!=dist[u]) continue;
        for(int i=0;i<(int)adj[u].size();i++){
            ll v=adj[u][i].first, w=adj[u][i].second;
            if(dist[u]+w<dist[v]){
                dist[v]=dist[u]+w;
                parent[(int)v]=(int)u;
                pq.push({dist[v],v});
            }
        }
    }
}

// 0-1 BFS
void ZeroOneBFS(int s, int n, vll &dist, vi &parent, vpl *adj)
{
  dist.assign(n + 1, INF);
  parent.assign(n + 1, -1);
  deque<int> dq;
  dist[s] = 0;
  dq.push_front(s);

  while (!dq.empty())
  {
    int u = dq.front();
    dq.pop_front();
    for(int i = 0; i < (int)adj[u].size(); i++)
    {
      int v = adj[u][i].first;
      ll w = adj[u][i].second;
      if (dist[u] + w < dist[v])
      {
        dist[v] = dist[u] + w;
        parent[v] = u;
        if (w == 0)
          dq.push_front(v);
        else
          dq.pb(v);
      }
    }
  }
}

// BFS
void BFS(int s,int n,vi &dist,vi &parent,vi *adj)
{
  dist.assign(n+1,-1);
  parent.assign(n+1,-1);
  queue<int>q;
  dist[s]=0;
  q.push(s);
  while(!q.empty()){
    int u=q.front();
    q.pop();
    for(int v:adj[u]){
      if(dist[v]==-1){
        dist[v]=dist[u]+1;
        parent[v]=u;
        q.push(v);
      }
    }
  }
}

// DFS
void DFS(int u, vb &vis, vi *adj, vi &order)
{
  vis[u] = true;
  order.pb(u);
  for (int v : adj[u])
  {
    if (!vis[v])
      DFS(v, vis, adj, order);
  }
}
// Solution-->
void solve(){

}
signed main(){
    ios_base::sync_with_stdio(false);
    cin.tie(NULL);
    ll tt=1;
    cin>>tt;
    while(tt--)solve();

    return 0;
}



