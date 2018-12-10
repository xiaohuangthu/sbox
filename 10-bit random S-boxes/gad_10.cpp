//This version is based on the properties of regular columns in lat.
//In this version, we solve the linear equations with branch and cut method and determine the sbox bitwisely.
//Besides that, in this version, we will use the core set theroy which is the symetric structure in the internal nodes to save memory and time complexity.
//In the nodes of the tree, we record the core set. Expand it to a full set when needed.
//In this version, we use continuous memory.
//In this version, we develop a heuristic algorithm.
//#include<conio.h>
#include<vector>
#include<time.h>
#include<iostream>
#include <stdlib.h>
#include<fstream>
#include <cstdlib>
#include <stdint.h>

using namespace std;
#define n 10//n is the input size of sbox.
#define m 10//m is the output size of sbox.
#define SIZE 1024
int BIJECK = 1;
int s[1024][1025], ddt[1024][1024], tmp_table[1024][1024];
int cnt = 0;
int cnt_c = 0;

int chkDDT(int sbox[SIZE])
{
	int i, j, out, flag;
	//int DDT[SIZE][SIZE] = { 0 };

	for (i = 0; i<SIZE; i++)
	{
		for (j = 0; j<SIZE; j++)
		{
			//the input diff is i, compute the output diff out
			tmp_table[i][j] = 0;
		}
	}

	for (i = 0; i<SIZE; i++)
	{
		for (j = 0; j<SIZE; j++)
		{
			//the input diff is i, compute the output diff out
			out = sbox[j] ^ sbox[i^j];
			tmp_table[i][out]++;
		}
	}
	flag = 1;
	for (i = 0; i < SIZE; i++)
	{
		if (flag == 0)break;
		for (j = 0; j < SIZE; j++)
		{
			if (tmp_table[i][j] != ddt[i][j])
			{
				flag = 0;
				break;
			}
		}
	}
	if (flag == 1)
	{
		cnt++;
		return 1;
	}
	else
	{
		return 0;
	}
}
int BuildDDT(int sbox[SIZE], int ddt[SIZE][SIZE])
{

	int x1, x2, dx, dy;
	for (x1 = 0; x1 < SIZE; x1++)
		for (x2 = 0; x2 < SIZE; x2++)
			ddt[x1][x2] = 0;
	for (x1 = 0; x1 < SIZE; x1++)
		for (dx = 0; dx < SIZE; dx++) {
			x2 = x1 ^ dx;
			if ((sbox[x1] == -1) || (sbox[x2] == -1))
				continue;
			dy = sbox[x1] ^ sbox[x2];
			ddt[dx][dy]++;
		}
	return 0;
}


bool chkAssign(int ar[SIZE], int size, int val) {
	int i;
	for (i = 0; i < size; i++) {
		if (BIJECK && ar[i] == val)// bijectiveness check
			return false;
		if (ddt[i ^ size][ar[i] ^ val] == 0)		// assignemnt validy check according to ddt
			return false;
	}
	return true;
}
void find_next_multi(int ar[SIZE], int size, int *flag) {
	int possAssign;
	//*flag = 1;
	if (size == SIZE) {	// reached possible solution		
		if (chkDDT(ar))
		{
			*flag = 0;
		};// found result. check it. if good, print it.
		return;
	}

	if (*flag == 1)
	{
		for (possAssign = 1; possAssign <= s[size][0]; possAssign++) {
			if (chkAssign(ar, size, s[size][possAssign])) {		// found good assignemnt. add it
				ar[size] = s[size][possAssign];
				find_next_multi(ar, size + 1, flag);
			}
		}
		//if we are here, reached dead-end, no good assignment can be found. have to trace back.
		//we are back to the previous step, try the next possible assignment
		return;
	}
	else
	{
		return;
	}

}
int main(int argc, char** argv)
//int main()
{
	int ii, i, j, k, begin, begin_1;
	int SBOX[SIZE] = { 0 };
	//int *SBOX = new int[SIZE];
	//int collect = atoi(argv[1]);
	int ab = atoi(argv[1]);
	//int collect = 4;
	//cout << collect << "\t";


	char buffer[32]; // The filename buffer.
	// Put "file" then k then ".txt" in to filename.
	snprintf(buffer, sizeof(char) * 32, "sbox-%i-%i.txt",n, ab);
	cout << buffer << endl;
	int test = 1;

	ifstream fin;

	fin.open(buffer);
	for (i = 0; i < SIZE; i++)
	{
		/*for(j=0;j<SIZE;j++)
		{
			fin>>ddt[i][j];
		}*/
		fin >> SBOX[i];
	}
	fin.close();
	BuildDDT(SBOX, ddt);
	
	
	
	int flag, tmp_com, scale;
	int target = 0, tmp = 0;

	int counter = 0, ctr = 0, index_C = 1, tmp1;
	//time_t t = 0, t1 = 0, t_sd = 0, t_match = 0, t2 = 0, t_c = 0;
	clock_t t = 0, t1 = 0, t_sd = 0, t_match = 0, t2 = 0, t_c = 0;

	int sbox[SIZE] = { 0 }, ar[SIZE];
	

	for (i = 0; i < SIZE; i++)
	{
		for (j = 0; j < SIZE; j++) {
			s[i][j] = -1;
			tmp_table[i][j] = 0;
		}
		s[i][SIZE] = -1;
	}

	s[0][0] = 1;					// we fix 0 to be assigned to 0, as all other assignmetns are simply linear shifts that doesn't change the DDT.
	s[0][1] = 0;

	ctr = 0;
	for (i = 1; i < SIZE; i++)
	{
		for (j = 0; j < SIZE; j++)
		{
			if (ddt[i][j])// & ddt[i^1][j^sol])			// if 0 gets assined to 0, then i^0 = i and sbox(i)^sbox(0) = sbox(i), which means that each non zero value in 
			{
				s[i][++ctr] = j;	// column j in the ddt[i] row indicates that j is a possible sbox(i) assignment. in addition checking compliance with the s(1) fixture. ctr counts the possibilities. 
			}
		}
		s[i][0] = ctr;
		ctr = 0;
	}

	flag = 0;
	t1 = clock();
	for (ii = 0; ii < test; ii++)
	{
		ar[0] = 0;
		flag = 1;
		cnt = 0;
		find_next_multi(ar, 1, &flag);
		if (cnt == 0)
		{
			cout << "Error:no sbox is found" << endl;
		}
	}

	t1 = clock() - t1;
	cout << (float(t1)) / (test * CLOCKS_PER_SEC) << endl;

	//cout << "Press any key to exit..." << endl;
	//_getch();
	return 0;
}
