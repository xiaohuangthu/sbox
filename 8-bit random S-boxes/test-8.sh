#!/bin/bash
for j in {0..99}; 
do
	nice -19 ./random-8 "2" "$j"
done
