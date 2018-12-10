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
#define n 13//n is the input size of sbox.
#define m 13//m is the output size of sbox.
#define SIZE 8192
int BIJECK = 1;
int s[SIZE][SIZE], ddt[SIZE][SIZE];
int SBOX[SIZE] = { 0 };
unsigned long long cnt = 0;

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
void cnt_next(int ar[SIZE], int size, int fix, int *flag) {
	int possAssign, i, flag_1;
	if (*flag == 0)
	{
		return;
	}
	else {
		if (size == fix) {	// reached possible solution
			for (possAssign = 1; possAssign <= s[size][0]; possAssign++) {
				if (chkAssign(ar, size, s[size][possAssign])) {		// found good assignemnt. add it
					ar[size] = s[size][possAssign];
					cnt++;
					flag_1 = 1;
					for (i = 0; i < fix + 1; i++)
					{
						if (SBOX[i] != ar[i])
						{
							flag_1 = 0;
							break;
						}
					}

					if (flag_1 == 1)
					{
						*flag = 0;return;
					}
					
				}
			}
		}
		else {
			for (possAssign = 1; possAssign <= s[size][0]; possAssign++) {
				if (chkAssign(ar, size, s[size][possAssign])) {		// found good assignemnt. add it
					if (*flag == 0)
					{
						return;
					}
					ar[size] = s[size][possAssign];
					cnt_next(ar, size + 1, fix, flag);
				}
			}
			return;
		}
	}
	
}
int main(int argc, char** argv)
//int main()
{
	int i, j;
	
	int fix = 4;
	int ab = atoi(argv[1]);
	//int fix= atoi(argv[2]);

	char buffer[32]; // The filename buffer.
	// Put "file" then k then ".txt" in to filename.
	snprintf(buffer, sizeof(char) * 32, "sbox-%i-%i.txt",n, ab);
	cout << buffer << endl;
	ifstream fin;

	fin.open(buffer);
	for (i = 0; i < SIZE; i++)
	{
		fin >> SBOX[i];
	}
	fin.close();
	BuildDDT(SBOX, ddt);

	int sbox[SIZE] = { 0 }, ar[SIZE] = {0};
	

	for (i = 0; i < SIZE; i++)
	{
		for (j = 0; j < SIZE; j++) {
			s[i][j] = -1;
		}
		s[i][SIZE] = -1;
	}

	s[0][0] = 1;					// we fix 0 to be assigned to 0, as all other assignmetns are simply linear shifts that doesn't change the DDT.
	s[0][1] = 0;
	s[1][0] = 1;
	s[1][1] = SBOX[1];

	int ctr = 0;
	for (i = 2; i < SIZE; i++)
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
	int flag = 1;
	cnt_next(ar, 1, fix, &flag);

	cout << cnt << endl;
	//cout << "Press any key to exit..." << endl;
	//_getch();
	return 0;
}
