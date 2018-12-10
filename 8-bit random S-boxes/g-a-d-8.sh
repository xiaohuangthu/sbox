#!/bin/bash
for j in {0..99}; 
do
	nice -19 ./g_d_8 "$j"
done
