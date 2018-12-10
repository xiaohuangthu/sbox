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
#define n 12//n is the input size of sbox.
#define m 12//m is the output size of sbox.
#define SIZE 4096
int log_size[SIZE + 1] = { 0 };
int square[SIZE*SIZE / 4 + 1] = { 0 };
//int *square, *log_size;
int bound = 2000;
int BIJECK = 1;
int s[SIZE][SIZE], ddt[SIZE][SIZE], tmp_table[SIZE][SIZE];
int cnt = 0;
int cnt_c = 0;
char dotproduct[SIZE][SIZE], dotproduct_1[SIZE][SIZE];


bool mypredicate(int i, int j) {
	return (i == -j);
}
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
void findtheaxis(int *target, int vector_size, int axis_index[n], int *full_set)
{
	int symetric_axis = log_size[vector_size];
	int i, j, k, j0, begin, begin_1, half_size, block_size, size_of_full = 1;
	for (i = 0; i < vector_size; i++)
	{
		full_set[i] = target[i];
	}

	//we need to decide whether target vector is symetric along with this axis.
	vector<int> tmp(vector_size, 0);
	vector<int> tmp_1(vector_size, 0);
	for (i = 0; i < symetric_axis; i++)
	{
		block_size = 1 << (i + 1);
		half_size = block_size / 2;

		for (j = 0; j < vector_size / block_size; j++)
		{
			for (k = 0; k < half_size; k++)
			{
				tmp[j * block_size + k] = target[j * block_size + k + half_size];
				tmp[j * block_size + k + half_size] = target[j * block_size + k];
			}
		}
		axis_index[i] = 1;
		for (j = 0; j < size_of_full; j++)
		{
			for (k = 0; k < vector_size; k++)
			{
				tmp_1[k] = full_set[j*vector_size + k];
			}
			if (equal(tmp.begin(), tmp.end(), tmp_1.begin()))
			{
				axis_index[i] = 0;
				break;
			}
			else if (equal(tmp.begin(), tmp.end(), tmp_1.begin(), mypredicate))
			{
				axis_index[i] = 0;
				break;
			}
		}
		if (axis_index[i] & i != symetric_axis)//not i-symmetric
		{
			for (j0 = size_of_full; j0 < size_of_full << 1; j0++)
			{
				for (j = 0; j < vector_size / block_size; j++)
				{
					begin = j0*vector_size + j*block_size;
					begin_1 = (j0 - size_of_full)*vector_size + j * block_size;
					for (int k = 0; k < half_size; k++)
					{
						full_set[begin + k] = full_set[begin_1 + +k + half_size];
						full_set[begin + k + half_size] = full_set[begin_1 + k];
					}
				}
			}
			size_of_full = size_of_full << 1;
		}
	}
}
void permute(int ell, int ej, int *vec)
{
	int i, j, tmp, win_size, vec_size, begin, begin_1;
	win_size = 1 << ej;
	vec_size = 1 << ell;

	for (i = 0; i < 1 << (ell - ej - 1); i++)
	{
		begin = 2 * i*win_size;
		begin_1 = (2 * i + 1)*win_size;
		for (j = 0; j < win_size; j++)
		{
			tmp = vec[begin + j];
			vec[begin + j] = vec[begin_1 + j];
			vec[begin_1 + j] = tmp;
		}
	}
}
void symatric_expand(int * axis_index, int * axis_index_1, int *core_vector, int index, int vector_length, int *full_set)
{
	int symetric_axis = log_size[vector_length];
	int ctr = 0, i, j, k, block_size, half_size, size_1, j0, block_1, block;
	for (i = 0; i < vector_length; i++)
	{
		full_set[i] = core_vector[index*vector_length + i];
	}

	for (i = 0; i < symetric_axis; i++)
	{
		if (axis_index[i] & axis_index_1[i])
		{
			block_size = 1 << (i + 1);
			half_size = block_size / 2;
			size_1 = 1 << ctr;
			ctr++;

			for (j0 = 0; j0 < size_1; j0++)
			{
				for (j = 0; j < vector_length / block_size; j++)
				{
					block = (j0 + size_1)*vector_length + j * block_size;
					block_1 = j0 * vector_length + j * block_size;
					for (k = 0; k < half_size; k++)
					{
						full_set[block + k] = full_set[block_1 + k + half_size];
						full_set[block + k + half_size] = full_set[block_1 + k];
					}
				}
			}
		}

	}
}
int detect_eq(vector<int> core_vector, int ej, int ell)
{
	int tmp1[SIZE] = { 0 }, tmp[SIZE] = { 0 };
	int i, j;
	vector<int> tmp2(1 << ell, 0), tmp3(1 << ell, 0);

	for (i = 0; i < 1 << ell; i++)
	{
		tmp[i] = core_vector[i];
	}
	permute(ell, ej, tmp);
	for (i = 0; i < 1 << ell; i++)
	{
		tmp3[i] = tmp[i];
	}

	for (i = 0; i < 1 << ej; i++)
	{
		for (j = 0; j < 1 << ell; j++)
		{
			tmp1[j] = tmp3[j];
		}
		for (j = 0; j < ej; j++)
		{
			if ((i >> j) & 0x1 == 1)
			{
				permute(ell, j, tmp1);
			}
		}
		for (j = 0; j < 1 << ell; j++)
		{
			tmp2[j] = tmp1[j];
		}
		if (equal(core_vector.begin(), core_vector.end(), tmp2.begin()) || equal(core_vector.begin(), core_vector.end(), tmp2.begin(), mypredicate))
		{
			return i + (1 << ej);
		}
	}
}
void perms(int posi, int *vec, int ell)
{
	int i, j;
	for (i = 0; i < ell; i++)
	{
		if ((posi >> i) & 0x1 == 1)
		{
			permute(ell, i, vec);
		}
	}
}
void filter(int * full_set, int posi, int *indictor, int full_set_size, int vec_size)
{
	int i, j, k, ell;
	ell = log_size[vec_size];
	int tmp[SIZE] = { 0 };
	vector<int> tmp1(vec_size), tmp2(vec_size);
	for (i = 0; i < full_set_size; i++)
	{
		if (indictor[i])
		{
			for (j = 0; j < vec_size; j++)
			{
				tmp[j] = full_set[i*vec_size + j];
			}
			perms(posi, tmp, ell);
			for (j = 0; j < vec_size; j++)
			{
				tmp1[j] = tmp[j];
			}

			for (j = i + 1; j < full_set_size; j++)
			{
				if (indictor[j])
				{
					for (k = 0; k < vec_size; k++)
					{
						tmp2[k] = full_set[j*vec_size + k];
					}
					if (equal(tmp1.begin(), tmp1.end(), tmp2.begin()) || equal(tmp1.begin(), tmp1.end(), tmp2.begin(), mypredicate))
					{
						indictor[j] = 0;
					}
				}
			}
		}
	}
}
void rec_leaves(int ** target_subsums, int num_of_vector[SIZE], int num_blocks)
{
	int i, tmp, tmp1;
	for (i = 0; i < num_blocks; i++)
	{
		tmp = (target_subsums[i][0] + target_subsums[i + num_blocks][0]) / 2;
		tmp1 = (target_subsums[i][0] - target_subsums[i + num_blocks][0]) / 2;

		target_subsums[i][0] = tmp;
		target_subsums[i][1] = tmp1;

		num_of_vector[i] = 1;
		num_of_vector[i + num_blocks] = 0;
	}
}

int rec_internal(int layer, int ** target_subsums, int *full_set, int *tmp_node, int num_of_vector[SIZE], int num_blocks, int **axis_index, int **chk_parity)
{
	int vector_size = 1 << (layer - 1);
	int double_size = 1 << layer;
	int subrow[SIZE] = { 0 };
	int i, j, k, flag, flag_forbid, multi, tmp, i1, i2, sub_fullset_size, tmp1, tmp_size, start_index, k2, num_forbid[n], posi, indictor[SIZE];
	vector<int> tmp_vec(vector_size, 0);

	flag_forbid = 0;
	for (i = 0; i < num_blocks << 1; i++)
	{
		for (j = 0; j < num_of_vector[i]; j++)
		{
			tmp = 0;
			for (k = 0; k < vector_size; k++)
			{
				if ((target_subsums[i][j*vector_size + k] >> 1) & 0x1)
				{
					tmp++;
				}
			}
			chk_parity[i][j] = tmp;
		}
	}

	for (i = 0; i < num_blocks; i++)
	{
		multi = 0;
		flag_forbid = 0;
		for (j = 0; j < layer - 1; j++)
		{
			if (axis_index[i][j] & axis_index[i + num_blocks][j])
			{
				multi++;
			}
			if (layer > 2)
			{
				if (axis_index[i][j] == 0 & axis_index[i + num_blocks][j] == 0)
				{
					flag_forbid = 1;
					num_forbid[j] = 1;
				}
				else
				{
					num_forbid[j] = 0;
				}

			}
		}

		sub_fullset_size = 1 << multi;

		tmp_size = 0;
		if (flag_forbid == 0)
		{
			for (j = 0; j < num_of_vector[i + num_blocks]; j++)
			{
				symatric_expand(axis_index[i], axis_index[i + num_blocks], target_subsums[i + num_blocks], j, vector_size, full_set);
				//construct the full set
				for (k = 0; k < num_of_vector[i]; k++)
				{
					if (chk_parity[i][k] == chk_parity[i + num_blocks][j])
					{
						for (k2 = 0; k2 < sub_fullset_size; k2++)
						{
							flag = 1;

							for (i1 = 0; i1 < vector_size; i1++)
							{
								tmp = (target_subsums[i][k*vector_size + i1] + full_set[k2*vector_size + i1]) / 2;
								tmp1 = (target_subsums[i][k*vector_size + i1] - full_set[k2*vector_size + i1]) / 2;
								if (tmp1 > num_blocks | tmp1< -num_blocks | tmp> num_blocks | tmp < -num_blocks)
								{
									flag = 0;
									break;
								}
								if (tmp & 0x1 == 1 | tmp1 & 0x1 == 1)
								{
									flag = 0;
									break;
								}
								else
								{
									subrow[2 * i1] = tmp;
									subrow[2 * i1 + 1] = tmp1;
								}

							}

							if (flag)
							{
								if (tmp_size == bound)
								{
									//cout << "Memory is not enough." << endl;
									return 0;
								}

								for (i2 = 0; i2 < double_size; i2++)
								{
									tmp_node[tmp_size*double_size + i2] = subrow[i2];
								}
								tmp_size++;
							}
						}
					}

				}
			}
		}
		else
		{
			for (j = 0; j < num_of_vector[i + num_blocks]; j++)
			{
				symatric_expand(axis_index[i], axis_index[i + num_blocks], target_subsums[i + num_blocks], j, vector_size, full_set);
				//construct the full set
				for (k = 0; k < num_of_vector[i]; k++)
				{
					if (chk_parity[i][k] == chk_parity[i + num_blocks][j])
					{
						for (i1 = 0; i1 < sub_fullset_size; i1++)
						{
							indictor[i1] = 1;
						}
						for (i1 = 0; i1 < layer - 1; i1++)
						{
							if (num_forbid[i1] == 1)
							{
								for (i2 = 0; i2 < vector_size; i2++)
								{
									tmp_vec[i2] = target_subsums[i][k*vector_size + i2];
								}
								posi = detect_eq(tmp_vec, i1, layer - 1);
								filter(full_set, posi, indictor, sub_fullset_size, vector_size);
							}
						}
						for (k2 = 0; k2 < sub_fullset_size; k2++)
						{
							flag = 1;
							if (indictor[k2])
							{
								for (i1 = 0; i1 < vector_size; i1++)
								{
									tmp = (target_subsums[i][k*vector_size + i1] + full_set[k2*vector_size + i1]) / 2;
									tmp1 = (target_subsums[i][k*vector_size + i1] - full_set[k2*vector_size + i1]) / 2;
									if (tmp1 > num_blocks | tmp1< -num_blocks | tmp> num_blocks | tmp < -num_blocks)
									{
										flag = 0;
										break;
									}
									if (tmp & 0x1 == 1 | tmp1 & 0x1 == 1)
									{
										flag = 0;
										break;
									}
									else
									{
										subrow[2 * i1] = tmp;
										subrow[2 * i1 + 1] = tmp1;
									}

								}

								if (flag)
								{
									if (tmp_size == bound)
									{
										//cout << "Memory is not enough." << endl;
										return 0;
									}

									for (i2 = 0; i2 < double_size; i2++)
									{
										tmp_node[tmp_size*double_size + i2] = subrow[i2];
									}
									tmp_size++;
								}
							}

						}

					}

				}
			}
		}

		num_of_vector[i] = tmp_size;
		num_of_vector[i + num_blocks] = 0;

		for (j = 0; j < tmp_size; j++)//copy the tmp node to the target_subsums[i]
		{
			for (k = 0; k < double_size; k++)
			{
				target_subsums[i][j*double_size + k] = tmp_node[j*double_size + k];
			}
		}
	}
	return 1;
}

void rec_final(int ** target_subsums, int *full_set, int *tmp_node, int num_of_vector[SIZE], int num_blocks, int **axis_index, int **chk_parity)
{
	int vector_size = 1 << (n - 1);
	int double_size = SIZE;
	int subrow[SIZE] = { 0 };
	int i, j, k, multi, flag_forbid, num_forbid[n], indictor[SIZE], i1, i2, k2, flag, tmp, sub_fullset_size, tmp1, tmp_size, posi;
	vector<int> tmp_vec(vector_size, 0);

	for (i = 0; i < num_blocks; i++)
	{
		multi = 0;
		for (j = 0; j < n - 1; j++)
		{
			if (axis_index[i][j] & axis_index[i + num_blocks][j])
			{
				multi++;
			}
			if (axis_index[i][j] == 0 & axis_index[i + num_blocks][j] == 0)
			{
				flag_forbid = 1;
				num_forbid[j] = 1;
			}
		}

		sub_fullset_size = 1 << multi;

		tmp_size = 0;
		if (flag_forbid == 0)
		{
			for (j = 0; j < num_of_vector[i + num_blocks]; j++)
			{
				symatric_expand(axis_index[i], axis_index[i + num_blocks], target_subsums[i + num_blocks], j, vector_size, full_set);
				//construct the full set
				for (k = 0; k < num_of_vector[i]; k++)
				{
					for (k2 = 0; k2 < sub_fullset_size; k2++)
					{
						flag = 1;

						for (i1 = 0; i1 < vector_size; i1++)
						{
							tmp = (target_subsums[i][k*vector_size + i1] + full_set[k2*vector_size + i1]) / 2;
							tmp1 = (target_subsums[i][k*vector_size + i1] - full_set[k2*vector_size + i1]) / 2;
							if (tmp1 > num_blocks | tmp1< -num_blocks | tmp> num_blocks | tmp < -num_blocks)
							{
								flag = 0;
								break;
							}
							else
							{
								subrow[2 * i1] = tmp;
								subrow[2 * i1 + 1] = tmp1;
							}

						}

						if (flag)
						{
							for (i2 = 0; i2 < double_size; i2++)
							{
								tmp_node[tmp_size*double_size + i2] = subrow[i2];
							}
							tmp_size++;
						}
					}

				}
			}

			num_of_vector[i] = tmp_size;
			num_of_vector[i + num_blocks] = 0;

			for (j = 0; j < tmp_size; j++)//copy the tmp node to the target_subsums[i]
			{
				for (k = 0; k < double_size; k++)
				{
					target_subsums[i][j*double_size + k] = tmp_node[j*double_size + k];
				}
			}
		}
		else
		{
			for (j = 0; j < num_of_vector[i + num_blocks]; j++)
			{
				symatric_expand(axis_index[i], axis_index[i + num_blocks], target_subsums[i + num_blocks], j, vector_size, full_set);
				//construct the full set
				for (k = 0; k < num_of_vector[i]; k++)
				{
					for (i1 = 0; i1 < sub_fullset_size; i1++)
					{
						indictor[i1] = 1;
					}
					for (i1 = 0; i1 < n - 1; i1++)
					{
						if (num_forbid[i1] == 1)
						{
							for (i2 = 0; i2 < vector_size; i2++)
							{
								tmp_vec[i2] = target_subsums[i][k*vector_size + i2];
							}
							posi = detect_eq(tmp_vec, i1, n - 1);
							filter(full_set, posi, indictor, sub_fullset_size, vector_size);
						}
					}
					for (k2 = 0; k2 < sub_fullset_size; k2++)
					{
						flag = 1;

						for (i1 = 0; i1 < vector_size; i1++)
						{
							tmp = (target_subsums[i][k*vector_size + i1] + full_set[k2*vector_size + i1]) / 2;
							tmp1 = (target_subsums[i][k*vector_size + i1] - full_set[k2*vector_size + i1]) / 2;
							if (tmp1 > num_blocks | tmp1< -num_blocks | tmp> num_blocks | tmp < -num_blocks)
							{
								flag = 0;
								break;
							}
							else
							{
								subrow[2 * i1] = tmp;
								subrow[2 * i1 + 1] = tmp1;
							}

						}

						if (flag)
						{
							for (i2 = 0; i2 < double_size; i2++)
							{
								tmp_node[tmp_size*double_size + i2] = subrow[i2];
							}
							tmp_size++;
						}
					}

				}
			}

			num_of_vector[i] = tmp_size;
			num_of_vector[i + num_blocks] = 0;

			for (j = 0; j < tmp_size; j++)//copy the tmp node to the target_subsums[i]
			{
				for (k = 0; k < double_size; k++)
				{
					target_subsums[i][j*double_size + k] = tmp_node[j*double_size + k];
				}
			}
		}

	}
}

int ** rec(int layer, int ** target_subsums, int num_of_vector[SIZE], int *tmp_node, int *full_set, int **chk_parity, int *flag, int **axis_index)
{
	int num_blocks = SIZE / (1 << layer);//also equal to sum_size
	int vector_size = 1 << (layer - 1);
	int double_size = 1 << layer;
	int i, j;

	*flag = 1;
	if (layer > 1)
	{
		for (i = 0; i < num_blocks; i++)
		{
			findtheaxis(target_subsums[i], vector_size, axis_index[i], full_set);
			findtheaxis(target_subsums[i + num_blocks], vector_size, axis_index[i + num_blocks], full_set);
		}
	}

	if (layer == 1)
	{
		rec_leaves(target_subsums, num_of_vector, num_blocks);
	}
	else if (layer > 1 && layer < n)
	{
		*flag = rec_internal(layer, target_subsums, full_set, tmp_node, num_of_vector, num_blocks, axis_index, chk_parity);
	}
	else
	{
		rec_final(target_subsums, full_set, tmp_node, num_of_vector, num_blocks, axis_index, chk_parity);
	}

	if (*flag == 1)
	{
		if (layer < n)
		{
			target_subsums = rec(layer + 1, target_subsums, num_of_vector, tmp_node, full_set, chk_parity, flag, axis_index);
			return target_subsums;
		}
		else
		{
			for (i = 0; i < num_of_vector[i]; i++)
			{
				if (target_subsums[0][SIZE*i] == -1)
				{
					for (j = 0; j < SIZE; j++)
					{
						target_subsums[0][SIZE*i + j] = -target_subsums[0][SIZE*i + j];
					}
				}
			}
			return target_subsums;
		}
	}
	else
	{
		return target_subsums;
	}
}

int Innerproduct(int a, int b)
{
	int c = a&b;
	c ^= c >> 8;
	c ^= c >> 4;
	c ^= c >> 2;
	c ^= c >> 1;
	return (c & 0x1);
}
int VerifytheRow(int *vector, int sum[SIZE])
{
	int i, j, target;
	for (i = 0; i<SIZE; i++)
	{
		target = 0;
		for (j = 0; j<SIZE; j++)
		{
			target = target + dotproduct_1[i][j] * sum[j];
		}

		if (target != 2 * vector[i] & target != (-2) * vector[i])
		{
			return 0;
		}

	}

	return 1;
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
bool chkAssign_2(int ar[SIZE], int num_good, int good_set[n], int output[n][SIZE], int size) {

	int i, target, flag;
	flag = 0;
	for (i = 0; i < num_good; i++)
	{
		target = dotproduct[ar[size]][good_set[i]];
		if (output[i][size] == 1 & target == 1)
		{
			return false;
		}
		if (output[i][size] == -1 & target == 0)
		{
			return false;
		}
	}

	return true;
}
void find_next_multi(int ar[SIZE], int num_good, int good_set[], int output[n][SIZE], int size, int *flag) {
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
				if (chkAssign_2(ar, num_good, good_set, output, size)) {
					find_next_multi(ar, num_good, good_set, output, size + 1, flag);
				}
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
void ComputeColumn(int index, int column[SIZE])
{
	unsigned long tmp_index = 0;
	int acc, i, j;
	for (i = 0; i < SIZE; i++)//i-th row of the table
	{
		acc = 0;
		for (j = 0; j < SIZE; j++)
		{
			acc = acc + tmp_table[i][j] * dotproduct_1[j][index];
		}
		if (acc != 0 && square[acc / 4] == 0)
		{
			cout << "Error!";
		}
		column[i] = square[acc / 4];
	}
}
int main(int argc, char** argv)
//int main()
{
	int ii, i, j, k, begin, begin_1;
	int SBOX[SIZE] = { 0 };
	//int *SBOX = new int[SIZE];
	int collect = atoi(argv[1]);
	int ab = atoi(argv[2]);
	//int collect = 4;
	cout << collect << "\t";


	char buffer[32]; // The filename buffer.
	// Put "file" then k then ".txt" in to filename.
	snprintf(buffer, sizeof(char) * 32, "sbox-%i-%i.txt",n, ab);
	cout << buffer << endl;
	int test = 1;
	int **axis_index = new int*[SIZE];

	
	int **chk_parity = new int*[SIZE];

	for (i = 0; i < SIZE; i++)
	{
		axis_index[i] = new int[n];
		chk_parity[i] = new int[bound];
	}


	for (i = 0; i <= n; i++)
	{
		log_size[1 << i] = i;
	}

	for (i = 0; i <= SIZE / 2; i++)
	{
		square[i*i] = i;
	}

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
	//differential to linear
	for (i = 0; i < SIZE; i++) {
		for (j = 0; j < SIZE; j++)
		{
			dotproduct[i][j] = Innerproduct(i, j);
			dotproduct_1[i][j] = -2 * dotproduct[i][j] + 1;
		}
	}

	int **sums = new int*[SIZE];
	sums[0] = new int[SIZE*bound];

	int *tmp_node = new int[bound*SIZE];
	int *full_set_1 = new int[SIZE*SIZE];
	int num_of_vector[SIZE] = { 0 }, flag, column[SIZE] = { 0 }, num_good, tmp_com, scale;
	int **all_valid = new int *[m];
	int target = 0, tmp = 0;

	int counter = 0, ctr = 0, index_C = 1, tmp1, size_of_valid[m] = { 0 }, axis[m] = { 0 }, tmp_column[SIZE] = { 0 }, output[n][SIZE] = { 0 };
	//time_t t = 0, t1 = 0, t_sd = 0, t_match = 0, t2 = 0, t_c = 0;
	clock_t t = 0, t1 = 0, t_sd = 0, t_match = 0, t2 = 0, t_c = 0;
	int good_set[m] = { 0 };

	int indictor[SIZE] = { 0 }, sbox[SIZE] = { 0 }, ar[SIZE];
	for (i = 1; i < n + 1; i++)
	{
		all_valid[i - 1] = new int[10 * SIZE];
		for (j = 1 << (i - 1); j < 1 << i; j++)
		{
			sums[j] = new int[SIZE*bound / (1 << i)];
		}
	}


	for (i = 0; i < SIZE; i++)
	{
		indictor[i] = 1;
	}

	for (i = 0; i < SIZE; i++)
	{
		for (j = 0; j < SIZE; j++) {
			s[i][j] = -1;
			tmp_table[i][j] = 0;
		}
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
		for (i = 0; i < SIZE; i++)
		{
			indictor[i] = 1;
		}
		if (collect >= 1)
		{
			t = clock();
			for (j = 0; j < SIZE; j++)
			{
				if(test>1)
				{
					for (k = 0; k<SIZE; k++)
					{
						tmp_table[k][j] = 0;
					}
				}
				
				for (k = 0; k < SIZE; k++)
				{
					tmp = ddt[k][j];
					if (tmp)
					{
						for (i = 0; i<SIZE; i++)
						{
							tmp_table[i][j] = tmp_table[i][j] + dotproduct_1[i][k] * tmp;
						}
					}
				}
			}
			t = clock() - t;
			t_c = t_c + t;
		}
		num_good = 0;
		index_C = 1;
		while (num_good < collect && index_C < SIZE)
		{
			if (indictor[index_C] == 1)
			{
				t = clock();
				ComputeColumn(index_C, column);
				cnt_c++;
				t = clock() - t;
				t_c = t_c + t;
				//cout << "running time to convert one column is " << t << endl;
				for (i = 0; i < SIZE; i++)
				{
					sums[i][0] = column[i] << 1;
					num_of_vector[i] = 1;
				}
				t = clock();
				sums = rec(1, sums, num_of_vector, tmp_node, full_set_1, chk_parity, &flag, axis_index);


				if (flag == 1)
				{
					if (collect == 1 && num_of_vector[0] > 1)
					{
						index_C++;
						continue;
					}
					//cout << "running time to compute a good column is " << t << endl;
					good_set[num_good] = index_C;

					for (i = 0; i < 1 << num_good; i++)//find the linear related indices
					{
						tmp_com = index_C;
						for (j = 0; j < num_good; j++)
						{
							tmp_com = tmp_com ^ (((i >> j) & 0x1) * good_set[j]);
						}
						indictor[tmp_com] = 0;
					}

					size_of_valid[num_good] = num_of_vector[0];
					for (i = 0; i < size_of_valid[num_good]; i++)
					{
						for (j = 0; j < SIZE; j++)
						{
							all_valid[num_good][i*SIZE + j] = sums[0][i*SIZE + j];
						}
					}
					num_good++;
				}
				t = clock() - t;
				t_sd = t_sd + t;
				//else {
				//	cout << "running time to compute a bad column is " << t << endl;
				//}
			}
			index_C++;
		}

	}

	cout << "There are " << num_good << " good columns found. " << endl;
	if (num_good<2 & collect>0)
	{
		
		return 0;
	}

	cout << ((float)t_c) / (test * CLOCKS_PER_SEC) << "\t";
	cout << ((float)t_sd) / (test * CLOCKS_PER_SEC) << "\t";


	t = clock();
	for (ii = 0; ii < test; ii++)
	{
		i = 1;
		while (i < num_good)
		{
			ComputeColumn(good_set[i - 1] ^ good_set[i], column);
			ctr = 0;
			if (i == 1)
			{
				for (j = 0; j < size_of_valid[i]; j++)
				{
					if (j == 0)
					{
						findtheaxis(all_valid[i], SIZE, axis, full_set_1);
					}
					else
					{
						symatric_expand(axis, axis, all_valid[i], j, SIZE, full_set_1);
					}

					scale = 0;
					for (k = 0; k < n; k++)
					{
						if (axis[k] == 1)
						{
							scale++;
						}
					}
					scale = 1 << scale;

					for (k = 0; k < size_of_valid[i - 1]; k++)
					{
						begin = SIZE*k;
						for (tmp = 0; tmp < scale; tmp++)
						{
							begin_1 = SIZE*tmp;
							for (tmp1 = 0; tmp1 < SIZE; tmp1++)
							{
								tmp_column[tmp1] = all_valid[i - 1][begin + tmp1] * full_set_1[begin_1 + tmp1];
							}
							if (VerifytheRow(column, tmp_column))
							{
								for (tmp1 = 0; tmp1 < SIZE; tmp1++)
								{
									all_valid[i][tmp1] = full_set_1[begin_1 + tmp1];
									all_valid[i - 1][tmp1] = all_valid[i - 1][begin + tmp1];
								}
								ctr++;
							}
						}
					}
				}
			}
			else
			{
				for (j = 0; j < size_of_valid[i]; j++)
				{
					if (j == 0)
					{
						findtheaxis(all_valid[i], SIZE, axis, full_set_1);
					}
					else
					{
						symatric_expand(axis, axis, all_valid[i], j, SIZE, full_set_1);
					}

					scale = 0;
					for (k = 0; k < n; k++)
					{
						if (axis[k] == 1)
						{
							scale++;
						}
					}
					scale = 1 << scale;

					for (tmp = 0; tmp < scale; tmp++)
					{
						begin_1 = SIZE*tmp;
						for (tmp1 = 0; tmp1 < SIZE; tmp1++)
						{
							tmp_column[tmp1] = all_valid[i - 1][tmp1] * full_set_1[begin_1 + tmp1];
						}
						if (VerifytheRow(column, tmp_column))
						{
							for (tmp1 = 0; tmp1 < SIZE; tmp1++)
							{
								all_valid[i][tmp1] = full_set_1[begin_1 + tmp1];
							}
							ctr++;
						}
					}
				}
			}

			if (ctr == 0)
			{
				cout << "Error: No match for the SD solutions!" << endl;
				//_getch();
				return 0;
			}
			else if (ctr > 1)
			{
				cout << "Error: More than one match is found!" << endl;
				//fout.close();
				//_getch();
				return 0;
			}
			i++;
		}
	}

	t_match = t_match + clock() - t;
	cout << (float(t_match)) / (test * CLOCKS_PER_SEC) << "\t";

	t2 = clock();
	for (ii = 0; ii < test; ii++)
	{
		if (num_good == m)
		{
			for (i = 0; i < n; i++)
			{
				for (j = 0; j < SIZE; j++)
				{
					output[i][j] = 1;
				}
			}

			for (i = 0; i < 1 << num_good; i++)
			{
				tmp = 0;
				for (j = 0; j < num_good; j++)
				{
					tmp = tmp ^ ((i >> j) & 0x1) * good_set[j];
				}

				for (j = 0; j < n; j++)
				{
					if (tmp == 1 << j)
					{
						for (k = 0; k < m; k++)
						{
							if ((i >> k) & 0x1 == 1)
							{
								for (tmp1 = 0; tmp1 < SIZE; tmp1++)
								{
									output[j][tmp1] = output[j][tmp1] * all_valid[k][tmp1];
								}
							}
						}
						break;
					}
				}
			}

			for (i = 0; i < SIZE; i++)
			{
				sbox[i] = 0;
				for (j = 0; j < n; j++)
				{
					if (output[j][i] == -1)
					{
						sbox[i] = sbox[i] ^ (1 << j);
					}
				}
			}

			if (chkDDT(sbox) == 0)
			{
				cout << "Error:no sbox is found" << endl;
			}
		}
		else
		{
			//t2 = clock();
			for (i = 0; i < num_good; i++)
			{
				for (j = 0; j < SIZE; j++)
				{
					if (all_valid[i][0] == -1)
					{
						for (j = 0; j < SIZE; j++)
						{
							output[i][j] = -all_valid[i][j];
						}

					}
					else
					{
						for (j = 0; j < SIZE; j++)
						{
							output[i][j] = all_valid[i][j];
						}
					}
				}
			}

			//fout.open("result_8_bit.txt");
			ar[0] = 0;
			flag = 1;
			cnt = 0;
			find_next_multi(ar, num_good, good_set, output, 1, &flag);
			if (cnt == 0)
			{
				cout << "Error:no sbox is found" << endl;
			}
			//fout.close();
		}
	}
	t2 = clock() - t2;
	cout << (float(t2)) / (test * CLOCKS_PER_SEC) << "\t";

	t1 = clock() - t1;
	cout << (float(t1)) / (test * CLOCKS_PER_SEC) << endl;

	for (i = 0; i < SIZE; i++)
	{
		delete[] sums[i];
		delete[] axis_index[i];
	}
	for (i = 0; i < n; i++)
	{
		delete[] all_valid[i];
	}

	delete[] full_set_1;
	delete[] tmp_node;
	delete[] sums;
	delete[] all_valid;
	delete[] axis_index;
	//cout << "Press any key to exit..." << endl;
	//_getch();
	return 0;
}
