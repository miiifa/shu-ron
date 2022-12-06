// https://ei1333.github.io/luzhiled/
// http://beet-aizu.hatenablog.com/entry/2017/01/04/113233
// http://www.prefield.com/algorithm/
#include <bits/stdc++.h>
#include <experimental/filesystem>
#include <fstream>
#include <iostream>
#pragma GCC target("avx2")
#pragma GCC optimize("O3")
#pragma GCC optimize("unroll-loops")
// #pragma GCC target("sse,sse2,sse3,ssse3,sse4,popcnt,abm,mmx,avx,tune=native")
constexpr char bn = '\n';
using namespace std;
using ll = long long;
using ld = long double;
using vi = vector<int>;
using vl = vector<ll>;
using vd = vector<ld>;
using vs = vector<string>;
using vb = vector<bool>;
using vvi = vector<vector<int>>;
using vvl = vector<vector<ll>>;
using vvvl = vector<vector<vector<ll>>>;
using vvd = vector<vector<ld>>;
using vvs = vector<vector<string>>;
using vvb = vector<vector<bool>>;
#define pb push_back
#define eb emplace_back
#define fi first
#define se second
template<class T> using vc = vector<T>;
template<class T> using vvc = vector<vector<T>>;
using Graph = vector<vector<ll>>;
const ll INF = 1LL << 60;
void init() {cin.tie(0);ios::sync_with_stdio(false);cout << fixed << setprecision(15);}
const ll tl= 1000000007;
#define REP(i, n) for (int i = 0; i < n; i++)
#define REREP(i, n) for (ll i = n; i >= 0; i--)
#define FOR(i, a, n) for (ll i = a; i < n; i++)
#define REFOR(i, n, a) for (ll i = n; i >= a; i--)
#define CLR(mat,f) memset(mat, f, sizeof(mat))
#define IN(a, b, x) (a<=x&&x<=b)
#define UNIQUE(v) v.erase( unique(v.begin(), v.end()), v.end() ) //被り削除
#define debug cout << "line : " << __LINE__ << " debug" << endl;
#define ini(...) int __VA_ARGS__; in(__VA_ARGS__)
#define inl(...) long long __VA_ARGS__; in(__VA_ARGS__)
#define ind(...) long double __VA_ARGS__; in(__VA_ARGS__)
#define ins(...) string __VA_ARGS__; in(__VA_ARGS__)
#define inc(...) char __VA_ARGS__; in(__VA_ARGS__)
void in(){} template <typename T,class... U> void in(T &t,U &...u){ cin >> t; in(u...);}
void out(){cout << endl;} template <typename T,class... U> void out(const T &t,const U &...u){ cout << t; if(sizeof...(u)) cout << " "; out(u...);}
template<typename T>void die(T x){out(x); exit(0);}
#define in1(A) REP(i,A.size()) in(A[i]);
#define in2(A,B) REP(i,A.size()) in(A[i],B[i]);
#define in3(s,t,u) REP(i,sz(s)){in(s[i] , t[i] , u[i]);}
#define in4(s,t,u,v) REP(i,sz(s)){in(s[i] , t[i] , u[i] , v[i]);}
#define each(x,v) for(auto& x : v)
#define all(v) (v).begin(),(v).end()
#define sz(v) ((int)(v).size())
struct Point{ ld x,y; };
// ld dist(Point a, Point b){return sqrt(abs(a.x-b.x)*abs(a.x-b.x)+abs(a.y-b.y)*abs(a.y-b.y));} // ２点間の距離 
ll gcd(ll a, ll b) { return b != 0 ? gcd(b, a % b) : a; }
ll lcm(ll a,ll b){ return a / gcd(a,b) * b;} 
ll modpow(ll a, ll n, ll mod) {
  ll res = 1;
   while (n > 0) {
      if (n & 1) res = res * a % mod;
      a = a * a % mod;
      n >>= 1;
  }
  return res;
}
ll fact(ll n){ if(n < 2) return 1; return (n * fact(n-1))%tl; } //階乗
inline ll updiv(ll a,ll b){ return (a + b - 1) / b; } //切り上げ
template<typename T,typename U>ll ceil(T a,U b){return (a + b - 1) / b;}
template <class A, class B> inline bool chmax(A &a, const B &b) { return b > a && (a = b, true); }
template <class A, class B> inline bool chmin(A &a, const B &b) { return b < a && (a = b, true); }
#define YES(n) ((n) ? "YES" : "NO"  )
#define Yes(n) ((n) ? "Yes" : "No"  )
#define yes(n) ((n) ? "yes" : "no"  )
int dx[]={-1,0,1,0};
int dy[]={0,1,0,-1};
//-------------------------------------------------------------------------------------------------

// 最小費用流 (あり本p.203,204参照)
// ACLも使えるようになっておく

int E=300,N,cell;
vvi ans,rans;
vvl data;
vvvl dist;
vvl G;
vvl cell_graySum;
vvl cell_gray;
int bl=2;
ll lim=1000000;
// 1.3*10^9:6.5*10^8= 2:1
long double alp=1;
// ハンガリアン法
// #define residue(i,j) (dist[qq][i][j] + ofsleft[i] + ofsright[j])
#define residue(i,j) (G[i][j] + ofsleft[i] + ofsright[j])
vector<int> min_cost_match(int qq) {
    int n = cell*cell;
    int m = n;
    vector<int> toright(n, -1), toleft(m, -1);
    vector<int> ofsleft(n, 0), ofsright(m, 0);
    REP(r, n) {
        vector<bool> left(n, false), right(m, false);
        vector<int> trace(m, -1), ptr(m, r);
        left[r] = true;

        for(;;) {
            ll d = numeric_limits<ll>::max();
            REP(j, m) if (!right[j])
                chmin(d,residue(ptr[j], j));
            REP(i, n) if (left[i])
                ofsleft[i] -= d;
            REP(j, m) if (right[j])
                ofsright[j] += d;
            int b = -1;
            REP(j, m) if (!right[j] && residue(ptr[j], j) == 0)
                b = j;
            trace[b] = ptr[b];
            int c = toleft[b];
            if (c < 0) {
                while(b >= 0) {
                    int a = trace[b];
                    int z = toright[a];
                    toleft[b] = a;
                    toright[a] = b;
                    b = z;
                }
                break;
            }
            right[b] = left[c] = true;
            REP(j, m) if (residue(c, j) < residue(ptr[j], j))
                ptr[j] = c;
        }
    }
    return toright;
}

void change_ans(ll img_idx, ll cell1, ll cell2){
    ll now= img_idx, pre= (img_idx+(N-1))%N, next= (img_idx+1)%N;
    ll cell1_pre= rans[now][cell1],cell2_pre= rans[now][cell2];
    ll cell1_next= ans[now][cell1],cell2_next= ans[now][cell2];
    ans[pre][cell1_pre]= cell2; ans[now][cell2]= cell1_next;
    ans[pre][cell2_pre]= cell1; ans[now][cell1]= cell2_next;
    rans[next][cell1_next]= cell2; rans[now][cell2]= cell1_pre;
    rans[next][cell2_next]= cell1; rans[now][cell1]= cell2_pre;
    
}

// スコアの初期化
// 木（最初と最後をつながない）
ll init_score1(){
  long cost=0;
  for(int i=0; i<cell*cell; i++){
    int idx= i;
    for(int j=0; j<N-1; j++){
      cost+= dist[j][idx][ans[j][idx]];
      idx= ans[j][idx];
    }
  }
  return cost;
}
// 円環
ll init_score2(){
  long cost=0;
  for(int i=0; i<cell*cell; i++){
    int idx= i;
    for(int j=0; j<N-1; j++){
      cost+= dist[j][idx][ans[j][idx]];
      idx= ans[j][idx];
    }
    cost+= dist[N-1][idx][i];
  }
  return cost;
}
// 重心
ll init_score3(){
  long cost=0;
  int idx,k= E/cell;

  for(int i=0; i<cell*cell; i++){
    for(int j=0; j<k*k; j++){
      idx= i;
      ll sum=0;
      for(int t=0; t<N; t++){
        int e= (idx/cell)*E*k +j/k*E +(idx%cell)*k +j%k;
        sum+= data[t][e];
        idx= ans[t][idx];
      }
      sum/= N; // ピクセルの平均
      idx= i;
      for(int t=0; t<N; t++){
        int e= (idx/cell)*E*k +(j/k)*E +(idx%cell)*k +j%k;
        cost+= (ll)pow(data[t][e]-sum,2);
        idx= ans[t][idx];
      }
    }
  }
  // (122)^2*10^2*E*E 1.3*10^8
  return cost;
}
// 組み合わせのグループをナンバリングして、グレースケールの合計値を計算
vvl nums; // i枚目j番目の駒が何グループに所属するのかを保存
vl sum_sys; // iグループのグレースケール値を保存 
vvl sum_sysBl; //i枚目j番目のブロック(bl*bl)の合計値を保存
// 点描 
ll init_score_pointillism(){
    // 前計算

    // 厳密な感じになる。
    // nums,sum_sysの初期化
    nums.resize(N,vl(cell*cell,0));
    sum_sys.resize(cell*cell,0);
    for(int i=0; i<cell*cell; i++){

        int gray=0; // 最大値: 255*(10*10)
        int idx=i;
        for(int j=0; j<N; j++){
            
            gray+= cell_gray[j][idx];
            
            nums[j][idx]= i; 
            idx= ans[j][idx];                                                          
        }
        sum_sys[i]= gray/N;
    }
    // sum_sysBlの初期化 // 最大値: 255*(10*10)*bl^2
    int e= (cell-bl+1);
    sum_sysBl.resize(N,vl(cell*cell,-1));

    REP(i,N){
        REP(j,e*e){
            sum_sysBl[i][j/e*cell +j%e]= 0;
            REP(s,bl*bl){ 
                int pos= j/e*cell +j%e +s/bl*cell +s%bl;
                sum_sysBl[i][j/e*cell +j%e]+= sum_sys[nums[i][pos]];       
            } 
            sum_sysBl[i][j/e*cell +j%e]/= (bl*bl);
        }
    }
    
    // コスト計算
    ll cost= 0;
    REP(i,N){
        REP(j,e*e){
            
            cost+=  pow(sum_sysBl[i][j/e*cell +j%e]-cell_graySum[i][j/e*cell +j%e],2);   
             
        }
    }
    cost/=(e*e);
    // 最大値: ((255*10^2)^2)= 6.5*10^8
//-------------------------------------------------------------------------------
    // // いい塩梅になる。
    // ll cost= 0;
    // int idx;
    // int e= cell-bl+1;
    // for(int i=0; i<e*e; i++){
    //     idx= i/e*cell+i%e;
    //     ll sum=0;
    //     for(int j=0; j<N; j++){
    //         sum+= cell_graySum[j][idx];
    //         idx= ans[j][idx];
    //     }
    
    //     sum/= N; // ピクセルの平均

    //     idx= i/e*cell+i%e;
    //     for(int j=0; j<N; j++){
            
    //         cost+= pow(cell_graySum[j][idx]-sum,2);
    //         idx= ans[j][idx];
    //     }
    // }
    return cost;
}

// 2近傍で入れ替えた後のスコアの増減を返す。
// 点描 
ll replace_score(ll img_idx, ll cell1, ll cell2){
    ll gap= -init_score_pointillism();
    change_ans(img_idx,cell1,cell2);
   
    gap+= init_score_pointillism();
    change_ans(img_idx,cell2,cell1);

    return gap;

    // 差分
    gap= 0;
    // 交換前の計算
    // cell1
    int idx= cell1,i= img_idx;
    do{
            
        // REP(s,min(bl,cell-)){
        //     REP(t,bl){

        //     }
        // }
        idx= ans[i][idx];
        i++; i%=N;
    }while(i!=img_idx);
    REP(i,N){
        
        // REP(i,)    
    
        // REP(s,bl*bl){ 
        //     int pos= j/e*cell +j%e +s/bl*cell +s%bl;
        //     sum_sysBl[i][j/e*cell +j%e]+= sum_sys[nums[i][pos]];       
        // } 
        
    }
    // numsの更新
    // sum_sysの更新
    // sum_sysBlの更新
}
// 円環
ll replace_score2(ll img_idx, ll cell1, ll cell2){
    ll gap=0;
    ll now= img_idx, pre= (img_idx+(N-1))%N, next= (img_idx+1)%N;
    // 切り取った辺のスコア
    gap-= dist[pre][rans[now][cell1]][cell1];
    gap-= dist[pre][rans[now][cell2]][cell2];
    gap-= dist[now][cell1][ans[now][cell1]];
    gap-= dist[now][cell2][ans[now][cell2]];
    
    // 新たに追加（入れ替えた）した辺のスコア
    gap+= dist[pre][rans[now][cell1]][cell2];
    gap+= dist[pre][rans[now][cell2]][cell1];
    gap+= dist[now][cell2][ans[now][cell1]];
    gap+= dist[now][cell1][ans[now][cell2]];

    return gap;
}
// 重心
ll replace_score3(ll img_idx, ll cell1, ll cell2){ // O(k^2*N)
    ll gap=0;
    ll now= img_idx, pre= (img_idx+(N-1))%N, next= (img_idx+1)%N;
    int idx,i;
    ll cost= 0;
    // 切り取った辺のスコア
    // cell1の組み合わせ
    ll k= E/cell;
    REP(j,k*k){
        idx= cell1;
        i= now;
        ll ave= 0;
        do{
            int e= (idx/cell)*E*k +j/k*E +(idx%cell)*k +j%k;
            ave+= data[i][e];
            idx= ans[i][idx];
            i++; i%=N;
        }while(i!=now);
        ave/=N;
        idx= cell1;
        i= now;
        do{
            int e= (idx/cell)*E*k +j/k*E +(idx%cell)*k +j%k;
            cost+= (ll)pow(data[i][e]-ave,2);
            idx= ans[i][idx];
            i++; i%=N;
        }while(i!=now);
    }
    gap-=cost;
    // cell2の組み合わせ
    cost= 0;
   
    REP(j,k*k){
        idx= cell2;
        i= now;
        ll ave= 0;
        do{
            int e= (idx/cell)*E*k +j/k*E +(idx%cell)*k +j%k;
            ave+= data[i][e];
            idx= ans[i][idx];
            i++; i%=N;
        }while(i!=now);
        ave/=N;
        idx= cell2;
        i= now;
        do{
            int e= (idx/cell)*E*k +j/k*E +(idx%cell)*k +j%k;
            cost+= (ll)pow(data[i][e]-ave,2);
            idx= ans[i][idx];
            i++; i%=N;
        }while(i!=now);
    }
 
    gap-=cost;
    // 新しい辺のスコア
    // cell1->cell2の組み合わせ
    cost= 0;
    REP(j,k*k){
        idx= cell2;
        i= now;
        ll ave= 0;
        do{
            int e= (idx/cell)*E*k +j/k*E +(idx%cell)*k +j%k;
            ave+= data[i][e];
            if(i==now) idx= cell1;
            idx= ans[i][idx];
            i++; i%=N;
        }while(i!=now);
        ave/=N;
        idx= cell2;
        i= now;
        do{
            int e= (idx/cell)*E*k +j/k*E +(idx%cell)*k +j%k;
            cost+= (ll)pow(data[i][e]-ave,2);
            if(i==now) idx= cell1;
            idx= ans[i][idx];
            i++; i%=N;
        }while(i!=now);
    }

    gap+=cost;
    // cell2->cell1の組み合わせ
    cost= 0;
    REP(j,k*k){
        idx= cell1;
        i= now;
        ll ave= 0;
        do{
            int e= (idx/cell)*E*k +j/k*E +(idx%cell)*k +j%k;
            ave+= data[i][e];
            if(i==now) idx= cell2;
            idx= ans[i][idx];
            i++; i%=N;
        }while(i!=now);
        ave/=(double)N;
        idx= cell1;
        i= now;
        do{
            int e= (idx/cell)*E*k +j/k*E +(idx%cell)*k +j%k;
            cost+= (ll)pow(data[i][e]-ave,2);
            if(i==now) idx= cell2;
            idx= ans[i][idx];
            i++; i%=N;
        }while(i!=now);
    }
    gap+=cost;
    return gap;
}
// α点描+β重心 スコア（後処理的に行う）
ll replace_score_mix(ll img_idx, ll cell1, ll cell2){
    ll gap= -(1-alp)*init_score_pointillism();
    gap+= alp*replace_score3(img_idx,cell1,cell2);
    change_ans(img_idx,cell1,cell2);
   
    gap+= (1-alp)*init_score_pointillism();
    change_ans(img_idx,cell2,cell1);

    return gap;
}
ll lim_time= 10*60*1000;
ll mm=INF;
vvi T;
// string file= "n3hc";
vector<pair<ll,ll>> ss;
// score関数,fileファイル
// 保存先
//N=3 2近傍　70873行　16000000反復,307021472点
//    3近傍  51487行　29929831反復 308976971
void mountain(){
    random_device rnd;
    mt19937 mt(rnd());
    uniform_int_distribution<> rand_100(0, 9999);
    uniform_int_distribution<> rand_N(0, N-1);
    uniform_int_distribution<> rand_cell(0, cell*cell-1);
    // REP(i,100) out(rand_cell(mt));

//
    ll score= alp*init_score3();//+(1-alp)*init_score_pointillism();
    ss.emplace_back(make_pair(0,score));
    // 山登り
    ll cnt= 1;
    // 3,000,000
    
    int pc=1;
    time_t st= clock();
    double now_time= 0;
    
    ofstream outputfile("./process.txt");
    outputfile << lim_time << endl;
    while(now_time<lim_time){
        // 当確率でn回遷移させる
        // 過去n回分のそれぞれの交換成功確率をメモ(n回も変数にしてもよいかも 定数＝スコアの下がり具合×nとなるようなn)
        // 確率の高い方に遷移（古いデータは捨てる）
        // 両方の確率がある一定値まで下がったらジャンプする（破壊的解法）
        int cell1,cell2,cell3=-1,img_n;
        ll gap;
        if(rand_100(mt)<10000){ // 2近傍
            // 解をランダムに入れ替え
            cell1= rand_cell(mt), cell2= rand_cell(mt);
            img_n= rand_N(mt);
//           
            gap= replace_score3(img_n,cell1,cell2);
        // スコアが良かったら更新
            if(gap<0){
                score+= gap;
                // out(score);
                change_ans(img_n,cell1,cell2);
                ss.emplace_back(make_pair(cnt,score));
            }
            
            if(mm> score) {
                mm= score;
                // T= ans;
            }
            
        } else if(rand_100(mt)<10000){ // 3近傍
            // 解をランダムに入れ替え
            cell1= rand_cell(mt), cell2= rand_cell(mt), cell3= rand_cell(mt);
            img_n= rand_N(mt);
//
            gap= replace_score3(img_n,cell1,cell2);
            change_ans(img_n,cell1,cell2);
//
            gap+= replace_score3(img_n,cell2,cell3);
        // スコアが良かったら更新
            if(gap<0){
                score+= gap;
                change_ans(img_n,cell2,cell3);
                ss.emplace_back(make_pair(cnt,score));
            }else change_ans(img_n,cell1,cell2);
//　破壊的な策を講じる時にだけ更新
            if(mm> score) {
                mm= score;
                // T= ans;
            }
        }else{ // 悪くても交換
            cell1= rand_cell(mt), cell2= rand_cell(mt);
            img_n= rand_N(mt);
//            
            gap= replace_score3(img_n,cell1,cell2);
        // スコアが良かったら更新
            if(score>(100.0/0.002)*gap){
                score+= gap;
                change_ans(img_n,cell1,cell2);
                ss.emplace_back(make_pair(cnt,score));
            }
        }
        // グラフ描画用
        now_time = static_cast<double>(clock() - st) / CLOCKS_PER_SEC * 1000.0;
        if(gap<0 && cnt%1==0){ // cnt%1 は出力頻度 
            if(cell3==-1){
                outputfile << 5 << endl;
                outputfile << img_n << endl;
                outputfile << cell1 << endl;
                outputfile << cell2 << endl;
                outputfile << (ll)now_time << endl;
                outputfile << score << endl;
            }else{
                outputfile << 6 << endl;
                outputfile << img_n << endl;
                outputfile << cell1 << endl;
                outputfile << cell2 << endl;
                outputfile << cell3 << endl;
                outputfile << (ll)now_time << endl;
                outputfile << score << endl;    
            } 
        }
        
        // cnt++;
        // if(cnt*100/lim==pc) {
        //     out(pc,"%");
        //     pc++;
        // }
        
        if((ll)now_time*100/lim_time==pc) {
            out(pc,"%");
            pc++;
        }
        
    }
    outputfile.close();
    // lim
    // 2,3 img_n cell1,2,3
    // cnt score
    ss.emplace_back(make_pair(lim,score));
}
//1,803,692,624
void mountain2(){
    // 選択したかどうか 全て1になればおわり
    vl selected(N,0);
    G.resize(cell*cell,vl(cell*cell,0ll));
    int count= 0;
    ll score= init_score3();
    mm= score;
    out("init:",score);
    time_t st= clock();
    ll now_time;
    ofstream outputfile("./process.txt");
    outputfile << lim_time << endl;
    do{
        count++;
        random_device rnd;
        mt19937 mt(rnd());
        uniform_int_distribution<> rand_N(0, N-1-(count-1));
        
        int img_rnd= rand_N(mt);
        int img_n= 0;
        REP(i,N) {
            if(selected[i]==1) continue;
            if(img_rnd==0) {
                img_n=i;
                break;
            } 
            img_rnd--;
        }
        ll gap= 0;
        
        int k= E/cell;
        // G（N-1と1枚の組み合わせ後のスコア）の初期化
        G.assign(cell*cell,vl(cell*cell,0ll));
        // N-1枚と1枚の二部グラフ
        for(int i=0; i<cell*cell; i++){
            for(int j=0; j<k*k; j++){
                int idx= i;
                ll base=0;
                ll left_cell=-1;
                for(int t=0; t<N; t++){
                    if(t==(img_n+N-1)%N) left_cell= idx;
                    if(t!=img_n){
                        int e= (idx/cell)*E*k +j/k*E +(idx%cell)*k +j%k;
                        base+= data[t][e];
                    }
                    idx= ans[t][idx];
                }
                for(int s=0; s<cell*cell; s++){
                    int e= (s/cell)*E*k +j/k*E +(s%cell)*k +j%k;
                    ll add= data[img_n][e];
                    ll ave= (base+add)/N; // ピクセルの平均
                    idx= i;
                    
                
                    ll px_weight= 0;
                    for(int t=0; t<N; t++){                        
                        int e= (idx/cell)*E*k +(j/k)*E +(idx%cell)*k +j%k;
                        px_weight+= (ll)pow(data[t][e]-ave,2);
                        
                        idx= ans[t][idx];
                    }
                    G[left_cell][s]+= px_weight;
                }
            }
        }
        // Gのハンガリアン
        // scoreの更新
        // ipad goodnotes自由 を参照
        vi min_comb= min_cost_match(img_n);
        score= 0;
        REP(s,cell*cell){
            // score
            int q= min_comb[s]; //変更後の新しいピース
            score+= G[s][q];
        }
        out(img_n,count,score);
        // 更新されたらやり直し
        now_time = static_cast<double>(clock() - st) / CLOCKS_PER_SEC * 1000;
        if(mm>score) {
            // ans,ransの更新
            vi tmp_ans0(cell*cell), tmp_ans1(cell*cell);
            REP(i,cell*cell) {
                tmp_ans0[i]= ans[(img_n-1+N)%N][i];
                tmp_ans1[i]= ans[img_n][i];
            }
            ans[(img_n-1+N)%N]= min_comb; 

            REP(s,cell*cell){
                int q= ans[(img_n-1+N)%N][s]; //変更後の新しいピース
                int p= tmp_ans0[s]; // 元々選ばれていたピース
                int t= tmp_ans1[p]; // 新しく選ばれたピースの次のピース
                // ans,rans 
                ans[img_n][q]= t;
                rans[img_n][q]= s;
                rans[(img_n+1)%N][t]= q;
            }
            // カウンターリセット
            selected.assign(N,0);  
            count= 1;
            mm= score;
            out("更新");
            out(img_n,count,mm);
            
            // 出力(processing.txt) 
            // for(int i=-1; i<cell*cell; i++){
                
            //     if(i==-1) {
            //         outputfile << cell*cell+2 << endl;
            //         outputfile << img_n << endl;
            //         outputfile << now_time << endl;
            //         outputfile << score << endl;
            //     }else outputfile << min_comb[i] << endl;
            // }
        }else if(score>mm) out("error");
        selected[img_n]= 1;
        
        
        // 1回更新後、N-1回連続で更新されなければ、局所最適解と言える。
        if(count==N){
            out("top of head!!");
            out((ll)(now_time),mm);
            break;
        }
        
    }while(lim_time>now_time);
    outputfile.close();
}
// 307483898 らんだむ
// 919683222 306611081 はんがり score2/3
// 919300052 306483180 はんがり score3
// 919258922 306469825 はんがり score2
// 6712136964 2605797160
//-----------------------------------------------------------------------------------------------------------------
int main(){
    init();
    string str;
    ifstream ifs("./Variable/var.txt");
    // N,cell
    if (ifs.fail()) {
        std::cerr << "Failed to open file_var." << std::endl;
        return 0;
    }
    int c=0;
    while (getline(ifs, str)) {
        if(c==0) N= stoi(str.c_str());
        else if(c==1) cell= stoi(str.c_str());
        c++;
    }
    ans.resize(N,vi(cell*cell,0));
    rans.resize(N,vi(cell*cell,0));
    data.resize(N,vl(E*E,0));
    dist.resize(N,vvl(cell*cell,vl(cell*cell,0)));
    cell_gray.resize(N, vl(cell*cell,0));
    cell_graySum.resize(N, vl(cell*cell,-1));
    // data
    ifstream ifs2("./Array/data.txt");
    if (ifs2.fail()) {
        std::cerr << "Failed to open file_data." << std::endl;
        return 0;
    }
    REP(i,N){
        REP(j,E*E){
            if(getline(ifs2, str)){
                data[i][j]= stoi(str.c_str());
            }
        }
    }
    // dist
    ifstream ifs3("./Array/dist.txt");
    if (ifs3.fail()) {
        std::cerr << "Failed to open file_dist." << std::endl;
        return 0;
    }
    REP(i,N){
        REP(j,cell*cell){
            REP(k,cell*cell){
                if(getline(ifs3, str)){
                    dist[i][j][k]= stoi(str.c_str());
                }
            }
        }
    }
    // cell_gray 初期化 
    REP(i,N){
        REP(p,cell*cell){
            ll k= E/cell;
            REP(j,k*k){
                int e= (p/cell)*E*k +j/k*E +(p%cell)*k +j%k;
                // 元の画像i枚目のp番目の位置のグレースケール値の和
                cell_gray[i][p]+= data[i][e];
            }
            
        }
    }
    // cell_graySum 初期化
    int e= cell-bl+1;
    REP(i,N){
        REP(p,e*e){
            cell_graySum[i][p/e*cell +p%e]=0;
            REP(j,bl*bl){
                cell_graySum[i][p/e*cell +p%e]+= cell_gray[i][(p/e+j/bl)*cell +p%e + j%bl];
            }
            cell_graySum[i][p/e*cell +p%e]/=(bl*bl);
        }
    }
    // ans 初期化
    REP(i,N){
        REP(j,cell*cell){
            ans[i][j]= j; // i枚目j番目の次はi+1枚目j番目を選ぶ
        }
    }
//-------------------------------------------------------------------
    // ハンガリアン法
    clock_t start = clock();
    // for(int i=0; i<N-1; i++){
    //     ans[i]= min_cost_match(i);
    // }

    
    T=ans;
    // // ランダム
    REP(i,N) random_shuffle(all(ans[i]));

    // ans,rans初期化
    REP(j,cell*cell){
        int idx= j;
        REP(i,N){
            if(i==N-1) ans[i][idx]= j;
            idx= ans[i][idx];
        }
        idx= j;
        REP(i,N){
            rans[(i+1)%N][ans[i][idx]]= idx; // i枚目j個目のセルを選ぶ前のセル
            idx= ans[i][idx];
        }
    }
    // 初期解を書き出し
    ofstream init_out("./Array/initial_ans.txt");
    for(int i=0; i<N; i++){
        for(int j=0; j<cell*cell; j++){
            init_out << ans[i][j] << endl;
        }
    }
    init_out.close();

   
    // 局所探索法（近傍）
    // mountain(); // 山登り
    // 局所探索法（ハンガリアン）
    mountain2();
    out(mm);
    //計測
    clock_t end = clock();
    const double time = static_cast<double>(end - start) / CLOCKS_PER_SEC * 1000.0;
    printf("time %lf[ms]\n", time);
    // out(file);
    // // スコア用
    // ofstream of1("./plot/"+file+"/score_min.txt");
    // for(auto x: ss){
    //     of1 << x.fi << " " << x.se << endl;
    // }
    // of1 << mm << endl;
    // of1.close();

    // グラフ用
    // ofstream of2("./plot/"+file+"/final_ans_min.txt");
    // for(int i=0; i<N; i++){
    //     for(int j=0; j<cell*cell; j++){
    //         of2 << T[i][j] << endl;
    //     }
    // }
    // of2.clo*se();
    // ans出力
    ofstream outputfile("./Array/after_ans.txt");
    for(int i=0; i<N; i++){
        for(int j=0; j<cell*cell; j++){
            outputfile << ans[i][j] << endl;
        }
    }
    outputfile.close();
}
// g++ -O3 -mtune=native -march=native -mfpmath=both heuristic.cpp
// g++ -fsanitize=address -g -O3 -mtune=native -march=native -mfpmath=both heuristic.cpp
