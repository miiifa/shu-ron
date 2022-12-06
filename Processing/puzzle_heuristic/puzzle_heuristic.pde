// 1,2,3,4,5,6,10,12,15,20,25,30,50,60,75,100,150,300
// 1,2,3,4,5,6,8,9,10,12,15,18,20,24,30,36,40,45,60,72,90,120,225,450
int done=1; // 0->1書き込み終わったら1
int stop=1;
int N=12; //画像の枚数
PImage f[]= new PImage[N]; // 画像
PImage g[]= new PImage[N]; // グレースケール変換
PImage nomake[]= new PImage[N]; // 距離を全く意識しない
PImage tmp;
PImage ma[]= new PImage[N];
int E,k,cell=30; //k:コマいっぺんのサイズ,cell: 全体300
PImage[] h=new PImage[cell*cell];
int data[][]= new int[N][]; // グレースケールの情報を格納 data[y][x]
long dist[][][]; // グレースケールの情報を格納 data[y][x]
String savefile1 = "./../sketch_88puzzle/save.txt";
String savefile2 = "./../puzzle_kai/save.txt";
String save_ans= "./C++/Array/ans.txt";
String save_dist= "./C++/Array/dist.txt";
String save_data= "./C++/Array/data.txt";
String save_var= "./C++/Variable/var.txt";
String after_ans = "./C++/Array/after_ans.txt";
String initial_ans = "./C++/Array/initial_ans.txt";
String after_process = "./C++/process.txt";
String[] proc;
long start,end;
int[][] ans,rans;
int[][][] nums;
int[] sum_px;
//二枚の画像の大きさを480*480に揃える（理由はまだないのでとりあえず240）
//それぞれ1px＊1pxずつのブロックで比較し距離の最小となるような1px＊1pxを生成
// k*kのマスで8*8
void settings(){
  PImage z= loadImage("img/1.png");
  E= z.height; // 画像の縦（横）の長さ
  k= E/cell; // コマの辺の長さ
  tmp= createImage(k, k, RGB); // コマの仮置き
  h= new PImage[cell*cell]; //コマの番号保持
  data= new int[N][E*E]; // グレースケールの情報を格納 data[y][x]
  dist= new long[N][][]; // i,j,k : i枚目j駒とi+1枚目k駒の距離
  size(E*4, E*6); // 出力のサイズ
  for(int i=0; i<N; i++){
    data[i]= new int[E*E]; // i枚目の画像の色情報
    f[i]= loadImage("img/"+(i+1)+".png"); // i枚目の入力画像
    g[i]= createImage(E, E, RGB); // i枚目の出力画像
    nomake[i]= createImage(E, E, RGB); // i枚目の出力画像(アルゴリズム使わない)
    ma[i]= createImage(k, k, RGB);; // コマの例
  }
  
}
long init_score1(int ans[][],long dist[][][]){
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
long init_score2(int ans[][],long dist[][][]){
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
long init_score3(int ans[][]){
  long cost=0;
  int idx;
  for(int i=0; i<cell*cell; i++){
    for(int j=0; j<k*k; j++){
      idx= i;
      long sum=0;
      for(int t=0; t<N; t++){
        int e= (idx/cell)*E*k +j/k*E +(idx%cell)*k +j%k;
        sum+= data[t][e];
        idx= ans[t][idx];
      }
      sum/= N; // ピクセルの平均
      idx= i;
      for(int t=0; t<N; t++){
        int e= (idx/cell)*E*k +(j/k)*E +(idx%cell)*k +j%k;
        cost+= (long)Math.pow(data[t][e]-sum,2);
        idx= ans[t][idx];
      }
    }
  }
  
  return cost;
}
void writef(){
//PrintWriter output1= createWriter(save_ans);
  PrintWriter output2= createWriter(save_dist);
  PrintWriter output3= createWriter(save_data);
  PrintWriter output4= createWriter(save_var);
  output4.println(N);
  output4.flush();
  output4.println(cell);
  output4.flush();
  for(int i=0; i<N; i++){
    for(int j=0; j<E*E; j++){
      output3.println(data[i][j]);
      output3.flush();
    }
    for(int j=0; j<cell*cell; j++){
      //output1.println(ans[i][j]);
      //output1.flush();
      for(int p=0; p<cell*cell; p++){
        output2.println(dist[i][j][p]);
        output2.flush();
      }
    }
  }
  System.exit(0);
}
long startTime,endTime;  
void setup(){
  start = System.currentTimeMillis();
  background(255);

  //image(f1,0,0);
  //image(f2,f1.width,0);
  //long mcost= Long.MAX_VALUE;
  // グレースケール値を取得
  int rt= 100;
  int x1=21,x2=71,x3= rt-x1-x2;
  
  // data[i][j]: i枚目のj番目のピクセルのグレースケール値
  for(int i=0; i<N; i++){
    for(int j=0; j<E*E; j++){
      int x= f[i].pixels[j];
      data[i][j]= (int)(((int)(red(x)*0.2126)+(int)(green(x)*0.7152)+(int)(blue(x)*0.0722))*1);
      g[i].pixels[j]= color(data[i][j]);
    }
  }
  
  for(int i=0; i<N; i++){
    dist[i]= new long[cell*cell][cell*cell]; // 画像iの各セルから画像i+1のセルまでの距離を計算
  }
     
  // 課題1：距離の計算
  // k*kのセルの分け、各々の距離の計算結果をdistに格納
  // 1枚目~N-1枚目
  for(int t=0; t<N-1; t++){
    for(int i=0; i<k; i++){
      for(int j=0; j<k; j++){
        int tmp= k*cell*i+j;
        for(int p1=0; p1<cell*cell; p1++){
          for(int p2=0; p2<cell*cell; p2++){
            int idx1= (p1/cell)*k*k*cell+(p1%cell)*k+tmp;
            int idx2= (p2/cell)*k*k*cell+(p2%cell)*k+tmp;
            long gap= (int)Math.pow(data[t][idx1]-data[t+1][idx2],2);
            dist[t][p1][p2]+= gap;
          }
        }
      }
    }
  }
  // N枚目と1枚目
  for(int i=0; i<k; i++){
    for(int j=0; j<k; j++){
      int tmp= k*cell*i+j;
      for(int p1=0; p1<cell*cell; p1++){
        for(int p2=0; p2<cell*cell; p2++){
          int idx1= (p1/cell)*k*k*cell+(p1%cell)*k+tmp;
          int idx2= (p2/cell)*k*k*cell+(p2%cell)*k+tmp;
          long gap= (int)Math.pow(data[N-1][idx1]-data[0][idx2],2);
          dist[N-1][p1][p2]+= gap;
        }
      }
    }
  }
  // 課題2：割り当て問題
  //Assign as;
  ans= new int[N][cell*cell]; //iとi+1の距離のマッチング
  rans= new int[N][cell*cell]; //iとi-1の距離のマッチング
  
  //for(int i=0; i<N-1; i++){
  //  as= new Assign(dist[i]);
  //  ans[i]= as.min_cost_match();
  //}
  //end= System.currentTimeMillis();
  //print((end - start)+"ms","\n");

  // i枚目j駒目p番目が属している組み合わせのグレースケール値の総和を前計算
  // ピクセルの組み合わせの集合にナンバリング
  nums= new int[N][cell*cell][k*k];
  // 集合の番号でアクセスしてその集合内のピクセルのグレースケール値の総和を保存
  sum_px= new int[E*E];
  for(int i=0; i<cell*cell; i++){
    for(int s=0; s<k; s++){
      for(int t=0; t<k; t++){
        // ここから直す
        int idx=i;
        int gray=0;
        int number= i/cell*E*k +i%cell*k +s*E +t;
        for(int j=0; j<N; j++){
          int dev= idx/cell, mod= idx%cell;
          int c= k*k*cell, d= s*k*cell;
          gray+= data[j][dev*c+mod*k +d +t];
          nums[j][idx][s*k+t]= number; // N個のピクセルの集合をナンバリング
          idx= ans[j][idx];
        }
        sum_px[number]= gray; 
        if(gray<0 || N*255<gray) print(gray,"\n");
      }                                                              
    }
  }
  // 更新はk*k*3  （配列の更新と合成駒込み）
  //これを気にしないで行うと、N*k*k*2*2　（合成駒生成にもう一回分回さなければならない）
  long cost1= 0; // 間のみ O(cell^2*N)
  long cost2= 0; // サイクル O(cell^2*N)
  long cost3= 0; // 重心との差 O(E^2*N)
  
  PImage[] cl= new PImage[N];
  int pp=134; // pp番目のコマを比較
  for(int i=0; i<N; i++){
    cl[i]= createImage(300, 300, RGB);
  }
   //ヒューリスティック
   // データをc++に書き込み
  if(done==0) writef();
  
   
  // ans初期化
  String[] inits = loadStrings(initial_ans);
  for(int i=0; i<N; i++){
    for(int j=0; j<cell*cell; j++){
      ans[i][j]=Integer.parseInt(inits[i*cell*cell+j]);
    }
  }
  // rans初期化
  for(int j=0; j<cell*cell; j++){
      int idx= j;
      for(int i=0; i<N; i++){
          if(i==N-1) ans[i][idx]= j;
          idx= ans[i][idx];
      }
      idx= j;
      for(int i=0; i<N; i++){
          rans[(i+1)%N][ans[i][idx]]= idx; // i枚目j個目のセルを選ぶ前のセル
          idx= ans[i][idx];
      }
  }
  
  // データの受け取り
  // 結果出力用
  if(stop==1){
    String[] lines = loadStrings(after_ans);
    for(int i=0; i<N; i++){
      for(int j=0; j<cell*cell; j++){
        ans[i][j]=Integer.parseInt(lines[i*cell*cell+j]);
      }
    }
  }
  // 経過出力用
  
  if(stop==0) proc = loadStrings(after_process);
 
  // スコア計算
  cost1= init_score1(ans,dist);
  cost2= init_score2(ans,dist);
  cost3= init_score3(ans);
  // スコア表示
  System.out.println(String.format("%,d", cost1));
  System.out.println(String.format("%,d", cost2));
  System.out.println(String.format("%,d", cost3));
  // 強制終了
  //System.exit(0);
  
  // 1~2~3
  for(int i=0; i<cell*cell; i++){
    tmp= createImage(k, k, RGB);
    
    for(int s=0; s<k; s++){
      for(int t=0; t<k; t++){
        // ここから直す
        int idx=i;
        int red=0,green=0,blue=0,gray=0;
        for(int j=0; j<N; j++){
          int dev= idx/cell, mod= idx%cell;
          int c= k*k*cell, d= s*k*cell;
          red+= red(f[j].pixels[dev*c+mod*k +d +t]);
          green+= green(f[j].pixels[dev*c+mod*k +d +t]);
          blue+= blue(f[j].pixels[dev*c+mod*k +d +t]);
          gray+= data[j][dev*c+mod*k +d +t];
          if(i==pp) {
            
            ma[j].pixels[s*k+t]= color(data[j][dev*c +mod*k +d +t]);
          }
          idx= ans[j][idx];
        }
        idx=i;
        // 合成駒生成
        for(int j=0; j<N; j++){
          int dev= idx/cell, mod= idx%cell;
          int c= k*k*cell, d= s*k*cell;
          cl[j].pixels[dev*c+mod*k +d +t]= color(red/N,green/N,blue/N);
          g[j].pixels[dev*c+mod*k +d +t]= color(gray/N);
          //print(color(gray/N),"\n");
          idx= ans[j][idx];
        }  
        //グレー
        tmp.pixels[s*k+t]= color(gray/N);
                                              
      }                                                              
    }
    h[i]=tmp;    
  }
  end= System.currentTimeMillis();
  print((end - start)+"ms","\n");
  
  for(int i=0; i<N; i++){
    image(g[i],E*(i%4),E*(i/4));
    g[i].save("./グレー結果/結果"+(i+1)+".png");
    cl[i].save("./カラー結果/結果"+(i+1)+".png");
    ma[i].save("./駒たち/ma"+(i+1)+".png");
    //nomake[i].save("./nomake/"+(i+1)+".png");
  }
  for(int i=0; i<cell*cell; i++) h[i].save("./cells/"+i+".png");
  // 出力画像
  //PImage img= createImage(E*4, E*3,GRAY);
  //loadPixels();
  //img.pixels = pixels;
  //img.updatePixels();
  //img.save("./実験結果/aa.png");
  //img.save("gray10.png");
    startTime = System.currentTimeMillis();
}

//-------------------draw---------------------------------------
// c++で解いたヒューリスティクスの解の経過をdrawで再現する。（ビジュアライザ）

void change_ans(int img_idx, int cell1, int cell2){
    int now= img_idx, pre= (img_idx+(N-1))%N, next= (img_idx+1)%N;
    //print(now," ",cell1,"\n");
    int cell1_pre= rans[now][cell1];
    int cell2_pre= rans[now][cell2];
    int cell1_next= ans[now][cell1],cell2_next= ans[now][cell2];
    ans[pre][cell1_pre]= cell2; ans[now][cell2]= cell1_next;
    ans[pre][cell2_pre]= cell1; ans[now][cell1]= cell2_next;
    rans[next][cell1_next]= cell2; rans[now][cell2]= cell1_pre;
    rans[next][cell2_next]= cell1; rans[now][cell1]= cell2_pre;
    
}

int proc_idx= 1;
int d_cnt= 0;
int speed=80;
int imp= 0; // 0 全探索 1 工夫あり 2 ハンガリアン一気に交換
int[][] cellbox= new int[speed][];
// 絵を更新
void draw_image(){
  if(imp==0 || imp==1){
      
    int n= Integer.parseInt(proc[proc_idx]); 
    int img_n= Integer.parseInt(proc[proc_idx+1]); 
    //print(img_n,"\n");
    int choiced_cell[]= new int[n-3];
    for(int i=0; i<n-3; i++) choiced_cell[i]= Integer.parseInt(proc[proc_idx+2+i]);
    
    // 解の入れ替え
    for(int i=0; i<n-4; i++) change_ans(img_n,choiced_cell[i],choiced_cell[i+1]);
    
      // 入れ替え部分のみ合成駒を更新
    // 事前計算（入れ替え分の総和） 更新
    if(imp==1){
      for(int s=0; s<k; s++){
        for(int t=0; t<k; t++){
          // ここから直す
       
          for(int i=n-4; i>=0; i--){
            int Ch= choiced_cell[i];
            int Ch_gain= choiced_cell[(i+1)%(n-3)];
            int Ch_a= choiced_cell[((n-3)+i-1)%(n-3)];
            int dev= Ch/cell, mod= Ch%cell,dev2= Ch_gain/cell, mod2= Ch_gain%cell;
            int c= k*k*cell, d= s*k*cell;
            // 元々のsum_pxから値を減らす
            sum_px[nums[img_n][Ch][s*k+t]]-= data[img_n][dev*c+mod*k +d +t];
            // 今ある場所のsum_pxを増やす
            sum_px[nums[img_n][Ch][s*k+t]]+= data[img_n][dev2*c+mod2*k +d +t];
           
          }
          
        }                                                              
      }
      
      for(int s=0; s<k; s++){
        for(int t=0; t<k; t++){
          // ここから直す
       
          for(int i=n-4; i>=0; i--){
            int Ch= choiced_cell[i];
            int Ch_gain= choiced_cell[(i+1)%(n-3)];
            int Ch_a= choiced_cell[((n-3)+i-1)%(n-3)];
            int dev= Ch/cell, mod= Ch%cell,dev2= Ch_gain/cell, mod2= Ch_gain%cell;
            int c= k*k*cell, d= s*k*cell;
          
            //合成駒生成   
            int ave= sum_px[nums[img_n][Ch][s*k+t]]/N;
            int idx= Ch;
            //print(img_n," ",(N+img_n-1)%N,"\n");
            for(int j=0; j<N; j++){
              int pos= (j+img_n)%N;
              
              dev= idx/cell; mod= idx%cell;
              c= k*k*cell; d= s*k*cell;
              if(ave<0 || 255<ave) print(ave,"\n");
              g[pos].pixels[dev*c+mod*k +d +t]= color(ave);
              idx= ans[pos][idx];
            }
          }
          int tmp= nums[img_n][choiced_cell[n-4]][s*k+t];
          for(int i=n-4; i>=0; i--){
            int Ch= choiced_cell[i];
            int Ch_a= choiced_cell[((n-3)+i-1)%(n-3)];
           // numsの入れ替え
            if(i==0){
              nums[img_n][Ch][s*k+t]= tmp;
            }else{
              nums[img_n][Ch][s*k+t]= nums[img_n][Ch_a][s*k+t];
            } 
          }
        }                                                              
      }
    }
    
    //196688 ms 
    if(d_cnt%speed!=0) return;
  
    // 全ての駒を更新
    // 195302 ms
    if(imp==0){  
     for(int i=0; i<cell*cell; i++){
        tmp= createImage(k, k, RGB);
        for(int s=0; s<k; s++){
          for(int t=0; t<k; t++){
            // ここから直す
            int idx=i;
            int gray=0;
            for(int j=0; j<N; j++){
              int dev= idx/cell, mod= idx%cell;
              int c= k*k*cell, d= s*k*cell;
      
              gray+= data[j][dev*c+mod*k +d +t];
              
              idx= ans[j][idx];
            }
            idx=i;
            // 合成駒生成
            for(int j=0; j<N; j++){
              int dev= idx/cell, mod= idx%cell;
              int c= k*k*cell, d= s*k*cell;
              
              g[j].pixels[dev*c+mod*k +d +t]= color(gray/N);
              //print(g[j].pixels[dev*c+mod*k +d +t]," ", gray/N, "\n");
              idx= ans[j][idx];
             
            }                                  
          }                                                              
        } 
      }
    }
    for(int j=0; j<N; j++){
      g[j].updatePixels();
      image(g[j],E*(j%4),E*(j/4));
    }
  }else{
    
  
  }
  
}

// グラフを更新
void draw_graph(){
  int n= Integer.parseInt(proc[proc_idx]); 
  long time= Long.parseLong(proc[proc_idx+n-1]);
  long score= Long.parseLong(proc[proc_idx+n]);
  //size(E*4, E*6); // 出力のサイズ
  long lim= Long.parseLong(proc[0]);
  long score_max= Long.parseLong(proc[Integer.parseInt(proc[1])+1]);
  strokeWeight(1);
  // 縦軸
  line(50,E*3+50,50,E*6-50);
  long keta=-1,tmp_score= score_max;
  long rn=0;
  while(tmp_score!=0){tmp_score/=10; keta++;}
  rn= score_max/(long)Math.pow(10,keta-1);
  fill(0); 
  textSize(18);
  text("*10^"+keta+"points",45,E*3+50);
  textSize(16);
  for(int i=0;i<=10;i++){
    line(45,E*3+80+(E*3-130)/10*(10-i),55,E*3+80+(E*3-130)/10*(10-i));
    text(String.format("%.2f", (double)rn/100.0*i),9,E*3+80+(E*3-130)/10*(10-i));
  } 
  // 横軸
  line(50,E*6-50,E*4-50,E*6-50);
  keta=-1; long tmp_time= Integer.parseInt(proc[0]);
  rn=0;
  while(tmp_time!=0){tmp_time/=10; keta++;}
  rn= Integer.parseInt(proc[0])/(long)Math.pow(10,keta-1);
  fill(0); 
  textSize(18);
  text("*10^"+keta,E*4-70,E*6-70);
  text("steps",E*4-50,E*6-55);
  textSize(16);
  for(int i=0;i<=10;i++){
    line(50+(E*4-130)/10*i,E*6-55,50+(E*4-130)/10*i,E*6-45);
    text(String.format("%.1f", (double)rn/100.0*i),40+(E*4-130)/10*i,E*6-20);
  } 
  // 点
  strokeWeight(2.5);
  float X= 50+((E*4-130)*(((float)time)/lim));
  float Y= E*3+80+(E*3-130)*(1-((float)score)/score_max);
  point(X,Y);
}
void draw(){
  if(stop==1) return;
  //noLoop();
  long st = System.currentTimeMillis();
  long lim= proc.length;
  if(proc_idx<lim) {
    for(int i=0; i<speed; i++){
      
      draw_image();
      draw_graph();
      d_cnt++;
      proc_idx+= Integer.parseInt(proc[proc_idx])+1;
      
      if(proc_idx>=lim) {
        for(int j=0; j<N; j++){
          g[j].updatePixels();
          image(g[j],E*(j%4),E*(j/4));
        }
        break;
      }
    }  
    long e = System.currentTimeMillis();
    print((e - st) + " ms","\n");
  }else{

    noLoop();
    endTime = System.currentTimeMillis();
    print((endTime - startTime) + " ms","\n");

  }

  //print(proc_idx,"\n");

}
