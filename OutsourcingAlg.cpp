#pragma comment(lib, "libssl.lib")
#pragma comment(lib, "libcrypto.lib")

#include <stdio.h>
#include<time.h>
#include<string>
#include<iostream>
#include<openssl/bn.h>
#include <openssl/rand.h>  
#include <openssl/err.h>  
using namespace std;

typedef pair<BIGNUM*, BIGNUM*> PBB; //用来存(k,g^k)
BIGNUM* p, * q;  //大素数
BIGNUM** a, ** b;  //在Rand中用来存阿尔法，贝塔
BIGNUM* g;  //论文中的g
PBB* six_pbb;  //存储生成的6个数对
BIGNUM* h1, * h2, * v1, * v2;  //论文中的h1,h2,v1,v2
BIGNUM** u_in;  //输入的u序列
int i = 2;  //i为q与p-1的倍数关系
int N;  //输入的u,a对数

void getRandNum(int* S, int k, int min, int max)   //获取[min-max]之间不重复的k个随机数保存到数组S中
{
	int i, j, t, m = 0, flag;
	srand(time(NULL));     //随机数种子函数
	for (i = 0; i < k; i++) {  //循环k次得到k个随机数
		while (1){
			flag = 0;  //进入while(1)，标志位置0
			t = rand() % (max - min + 1) + min;   //得到 [min - max]之间的随机数
			for (j = 0; j < m; j++) {   //第一次m = 0,不执行循环语句
				if (S[j] == t) { //新生成的随机数只要和数组中的元素重复
					flag = 1;
					break;
				} //一旦找到一个重复的，直接跳出for循环	
			}
			if (flag == 0) { //第一次flag = 0
				S[m++] = t;  //生成的随机数和数组中已有的元素不重复时，保存到数组中。
				break;     //跳出while循环，继续获得后面的随机数
			}
		}
	}
}

void printBN(BIGNUM* x)  //以十六进制打印x
{
	//char* y = BN_bn2hex(x);
	char* y = BN_bn2dec(x);  //十进制
	printf("%s\n", y);
}

BIGNUM* getRange(BIGNUM* x, BIGNUM* a) // 得到范围为2到a的x
{
	BN_rand_range(x, a); //产生的x满足条件 0 < x < a
	BN_add_word(x, 1);  //得到范围为2到a的x
	return x;
}

void preStep(int n)  //Rand算法中的Preprocessing Step
{
	BIGNUM* g1 = BN_new(), * below_p = BN_new();
	g = BN_new();
	BN_copy(below_p, p);
	BN_sub_word(below_p, 1);

	getRange(g1, below_p); //得到范围为2到p-1的g1
	BIGNUM* bn_i = BN_new();
	BN_CTX* ctx = BN_CTX_new();
	BN_set_word(bn_i, i);
	BN_mod_exp(g, g1, bn_i, p, ctx);

	//Preprocessing Step
	a = (BIGNUM**)malloc(sizeof(BIGNUM*) * (n + 1));
	b = (BIGNUM**)malloc(sizeof(BIGNUM*) * (n + 1));

	for (int j = 1; j <= n; j++)   //给a,b元素分配内存
	{
		a[j] = BN_new();
		b[j] = BN_new();
	}
	for (int j = 1; j <= n; j++)
	{
		getRange(a[j], below_p); //得到范围为2到p-1的a[j]
		BN_mod_exp(b[j], g, a[j], p, ctx);
	}
}

PBB RandAlg(int n, int h)  //Rand算法中的Pair Generation
{
	srand((unsigned)time(NULL));
	int k = rand() % n + 1;
	int* S;
	S = (int*)malloc(sizeof(int) * k);
	getRandNum(S, k, 1, n);    // //获取1到n之间不重复的k个随机数保存到数组S中

	BIGNUM* x = BN_new(), * X = BN_new(), * rem = BN_new(), * bn_x = BN_new(), * bn_h = BN_new();
	BN_CTX* ctx = BN_CTX_new();
	BN_set_word(bn_h, h);
	BN_rand_range(bn_x, bn_h);  //产生的bn_x满足条件 0 < bn_x < h(即1到h-1)
	BN_mod_mul(x, a[S[0]], bn_x, q, ctx);   //先让x,X有一个初值
	BN_mod_exp(X, b[S[0]], bn_x, p, ctx);

	while (1){
		for (int c = 1; c < k; c++)  //x,X已经有初值了，所以从1开始
		{
			int j = S[c];
			BIGNUM* bn_x = BN_new(), * bn_h = BN_new(), * temp1 = BN_new(), * temp2 = BN_new();
			BN_set_word(bn_h, h);
			BN_rand_range(bn_x, bn_h);  //产生的bn_x满足条件 0 < bn_x < h(即1到h-1)
			BN_mod_mul(temp1, a[j], bn_x, q, ctx);
			BN_mod_add(x, x, temp1, q, ctx);
			BN_mod_exp(temp2, b[j], bn_x, p, ctx);
			BN_mod_mul(X, X, temp2, p, ctx);
		}
		BN_mod(rem, x, q, ctx);
		if (!BN_is_zero(rem)) break;
	}
	PBB pbb = { BN_new() ,BN_new() };
	BN_copy(pbb.first, x);
	BN_copy(pbb.second, X);
	return pbb;
}

BIGNUM* Ucal(BIGNUM* num1, BIGNUM* num2)  //U计算num1^num2
{
	BIGNUM* u_ans = BN_new();
	BN_CTX* ctx = BN_CTX_new();
	BN_mod_exp(u_ans, num1, num2, p, ctx);
	return u_ans;
}

BIGNUM* get_ty(BIGNUM* bn_a, BIGNUM* k1, BIGNUM* k3, BIGNUM* k5)
{
	BIGNUM* k5a = BN_new(), * k5a_k3 = BN_new(), * inver_k1 = BN_new(), * ty = BN_new();  //inver_k1是k1的逆元
	BN_CTX* ctx = BN_CTX_new();
	BN_mod_mul(k5a, k5, bn_a, q, ctx);
	BN_mod_sub(k5a_k3, k5a, k3, q, ctx);  //求出k5 * a - k3
	BN_mod_inverse(inver_k1, k1, q, ctx);  //求出k1的逆元
	BN_mod_mul(ty, k5a_k3, inver_k1, q, ctx);  //求得t1 * y1
	return ty;
}

BIGNUM* get_x(BIGNUM* bn_a, BIGNUM* ty)  //求x
{
	BIGNUM* x = BN_new();
	BN_CTX* ctx = BN_CTX_new();
	BN_mod_sub(x, bn_a, ty, q, ctx);  //求出x1
	return x;
}

BIGNUM* get_w(BIGNUM* v, BIGNUM* u)  //求w
{
	BIGNUM* w = BN_new(), * inver_v = BN_new();  
	BN_CTX* ctx = BN_CTX_new();
	BN_mod_inverse(inver_v, v, p, ctx);  //求出v1的逆
	BN_mod_mul(w, u, inver_v, p, ctx);  //求出w1
	return w;
}

BIGNUM* str_to_bn(string s)  //string转BIGNUM
{
	const char* str = s.c_str();
	BIGNUM* bn_s = BN_new();
	BN_dec2bn(&bn_s, str);
	return bn_s;
}

BIGNUM* getExp(BIGNUM* bn_a, BIGNUM* u, BIGNUM* k1, BIGNUM* k3, BIGNUM* k5, BIGNUM* gk, BIGNUM* v, BIGNUM* h)
{
	/*求x1, t1y1*/
	BIGNUM* ty = BN_new(), *x = BN_new();  //inver_k1是k1的逆元
	ty = get_ty(bn_a, k1, k3, k5);
	x = get_x(bn_a, ty); 

	BN_CTX* ctx = BN_CTX_new();
	/*求u^a*/
	BIGNUM* w = BN_new(), * inver_v = BN_new(), * w_x = BN_new(), * h_w = BN_new(), * hw_ty = BN_new();  //res存放u^a
	w = get_w(v, u); 
	w_x = Ucal(w, x);  //服务器U计算w1^x1
	BN_mod_mul(h_w, h, w, p, ctx);  //h1*w1
	hw_ty = Ucal(h_w, ty);  //服务器U计算h1w1^ty
	BIGNUM* res = BN_new(), * res1 = BN_new();
	cout << "g^k3: ";
	printBN(gk);
	cout << "w1^x1: ";
	printBN(w_x);
	cout << "h1w1^t1y1: ";
	printBN(hw_ty);
	cout << "--------------" << endl;
	BN_mod_mul(res1, gk, w_x, p, ctx);
	BN_mod_mul(res, res1, hw_ty, p, ctx);
	
	return res;
}

void Exp()
{
	string u1, a1;
	cout << "请用户T输入u和a:  (十进制)" << endl;
	cin >> u1 >> a1;

	BIGNUM* bn_u1 = BN_new(), * bn_a = BN_new();
	bn_u1 = str_to_bn(u1);
	bn_a = str_to_bn(a1);

	BIGNUM* bn_u = BN_new(), * bn_i = BN_new();
	BN_CTX* ctx = BN_CTX_new();
	BN_set_word(bn_i, i);
	BN_mod_exp(bn_u, bn_u1, bn_i, p, ctx);  //实际的u是输入u^i

	cout << "u: ";
	printBN(bn_u);
	cout << "p: ";
	printBN(p);
	BIGNUM* ans1 = BN_new(), * ans2 = BN_new();
	ans1 = getExp(bn_a, bn_u, six_pbb[0].first, six_pbb[2].first, six_pbb[4].first, six_pbb[2].second, v1, h1);

	BIGNUM* r = BN_new(), * randNum = BN_new(), * ra = BN_new();
	BN_dec2bn(&randNum, "16");  //r的范围取0~16
	BN_rand_range(r, randNum);
	BN_mod_mul(ra, r, bn_a, q, ctx);
	ans2 = getExp(ra, bn_u, six_pbb[1].first, six_pbb[3].first, six_pbb[5].first, six_pbb[3].second, v2, h2);

	BIGNUM* ans1_r = BN_new();
	BN_mod_exp(ans1_r, ans1, r, p, ctx);  //ans1_r就是方法1答案的r次方
	if (!BN_cmp(ans1_r, ans2))
	{
		printf("The answer is right.\nu^a:\n");
		printBN(ans1);
	}
	else printf("error.");
}

BIGNUM* getMExp(BIGNUM** a_in, BIGNUM* k1, BIGNUM* k3, BIGNUM* k5, BIGNUM* gk, BIGNUM* v, BIGNUM* h)
{
	BN_CTX* ctx = BN_CTX_new();
	BIGNUM** x_in, ** w_in, ** w_x_in;
	x_in = (BIGNUM**)malloc(sizeof(BIGNUM*) * N);  //存储x1,x2,...
	w_in = (BIGNUM**)malloc(sizeof(BIGNUM*) * N);  //存储w1,w2,...
	w_x_in = (BIGNUM**)malloc(sizeof(BIGNUM*) * N);  //存储w1^x1,w2^x2,...

	for (int c = 0; c < N; c++)
	{
		x_in[c] = BN_new();
		w_in[c] = BN_new();
		w_x_in[c] = BN_new();
	}
	BIGNUM* my_a = BN_new();
	for (int c = 0; c < N; c++) BN_mod_add(my_a, my_a, a_in[c], q, ctx);  //a1+a2+a3+...

	/*求出ty, x1,x2, ... */
	BIGNUM* ty = BN_new();
	ty = get_ty(my_a, k1, k3, k5);
	for (int c = 0; c < N; c++) x_in[c] = get_x(a_in[c], ty);
	/*求出u^a*/
	BIGNUM* w = BN_new(), * w_x = BN_new(), * h_w = BN_new(), * hw_ty = BN_new();
	BN_set_word(w, 1);
	BN_set_word(w_x, 1);
	for (int c = 0; c < N; c++)
	{
		w_in[c] = get_w(v, u_in[c]);  //w1,w2,w3
		w_x_in[c] = Ucal(w_in[c], x_in[c]);  //服务器U计算w1^x1

		//
		cout << c << " w^x";
		printBN(w_x_in[c]);

		BN_mod_mul(w, w, w_in[c], p, ctx);  //w1*w2*w3....
		BN_mod_mul(w_x, w_x, w_x_in[c], p, ctx); //w1^x1 * w2^x2
	}
	BN_mod_mul(h_w, h, w, p, ctx);  //h1*w1*w2*
	hw_ty = Ucal(h_w, ty);  //服务器U计算h1w1^ty
	BIGNUM* res = BN_new(), * res1 = BN_new();

	//
	cout << "g^k: ";
	printBN(gk);
	cout << "h1w1^ty: ";
	printBN(hw_ty);
	BN_mod_mul(res1, gk, w_x, p, ctx);
	BN_mod_mul(res, res1, hw_ty, p, ctx);
	return res;
}

void MExp()
{
	cout << "请用户T依次输入" << N << "对u和a:  (十进制)" << endl;
	u_in = (BIGNUM**)malloc(sizeof(BIGNUM*) * N);
	BIGNUM** a_in = (BIGNUM**)malloc(sizeof(BIGNUM*) * N);
	BIGNUM** ra_in = (BIGNUM**)malloc(sizeof(BIGNUM*) * N);
	BN_CTX* ctx = BN_CTX_new();
	
	BIGNUM* bn_i = BN_new(), * bn_u1 = BN_new(), * bn_a = BN_new(), * bn_u = BN_new();
	BN_set_word(bn_i, i);
	for (int c = 0; c < N; c++)
	{
		string u1, a1;
		cin >> u1 >> a1;
		u_in[c] = BN_new();
		a_in[c] = BN_new();
		ra_in[c] = BN_new();
		bn_u1 = str_to_bn(u1);
		bn_a = str_to_bn(a1);
		BN_mod_exp(bn_u, bn_u1, bn_i, p, ctx);  //实际的u是输入u^i	
		BN_copy(u_in[c], bn_u);
		BN_copy(a_in[c], bn_a);
		cout << c << " u: ";
		printBN(bn_u);
		cout << "p: ";
		printBN(p);
	}

	BIGNUM* ans1 = BN_new(), * ans2 = BN_new();
	ans1 = getMExp(a_in, six_pbb[0].first, six_pbb[2].first, six_pbb[4].first, six_pbb[2].second, v1, h1);

	BIGNUM* r = BN_new(), * randNum = BN_new(), * my_ra = BN_new();
	BN_dec2bn(&randNum, "16");
	BN_rand_range(r, randNum);
	for (int c = 0; c < N; c++) BN_mod_mul(ra_in[c], r, a_in[c], q, ctx);  //得到ra1,ra2,ra3，...
	ans2 = getMExp(ra_in, six_pbb[1].first, six_pbb[3].first, six_pbb[5].first, six_pbb[3].second, v2, h2);

	BIGNUM* ans1_r = BN_new();
	BN_mod_exp(ans1_r, ans1, r, p, ctx);  //ans1_r就是方法1答案的r次方

	if (!BN_cmp(ans1_r, ans2))
	{
		printf("The answer is right.\nu^a:\n");
		printBN(ans1);
	}
	else printf("error.");
}

int main()
{
	p = BN_new();
	q = BN_new();
	BN_generate_prime(q, 32, 1, NULL, NULL, NULL, NULL);  //产生32bit的素数q
	BIGNUM* temp = BN_new();
	
	BN_copy(temp, q);//将q复制给temp,正确返回temp
	while (1)
	{
		BN_mul_word(temp, i);
		BN_add_word(temp, 1);  //大数temp加上1，值储存在temp中
		if (BN_is_prime(temp, 128, NULL, NULL, NULL))  //判断temp是否为素数，错误概率小于 0.25^checks
		{
			BN_copy(p, temp);
			break;
		}
		i++;
		BN_copy(temp, q);
	}
	/*T run 6 Rand*/
	six_pbb = (PBB*)malloc(sizeof(PBB) * 6);
	preStep(64); //目前测试,n定为64
	for (int c = 0; c < 6; c++)
	{
		six_pbb[c].first = BN_new();
		six_pbb[c].second = BN_new();
		six_pbb[c] = RandAlg(64, 64);  //n,h目前测试，固定下来
	}
	/*对h1,h2,v1,v2赋值*/
	h1 = BN_new(), h2 = BN_new(), v1 = BN_new(), v2 = BN_new();
	BN_CTX* ctx = BN_CTX_new();
	BN_mod(h1, six_pbb[0].second, p, ctx);
	BN_mod(h2, six_pbb[1].second, p, ctx);
	BN_mod(v1, six_pbb[4].second, p, ctx);
	BN_mod(v2, six_pbb[5].second, p, ctx);
	/*trick*/
	int choice;
	cout << "1. Exp" << endl;
	cout << "2. SExp" << endl;
	cout << "3. MExp" << endl;
	cin >> choice;
	switch (choice)
	{
	case 1: 
		Exp();
		break;
	case 2:
		N = 2;
		MExp();
		break;
	case 3:
		cout << "输入u,a的对数：";
		cin >> N;
		MExp();
		break;
	}
	return 0;
}
