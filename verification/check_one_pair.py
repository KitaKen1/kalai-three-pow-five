#!/usr/bin/env python3
"""Exhaust the nine elementary seven-vertex pair counts in the written proof."""
import json

ROWS=((7,15,14,6,29),(7,16,16,7,32),(7,17,17,7,32),
      (7,17,18,8,35),(7,17,19,9,38),(7,18,19,8,35),
      (7,18,20,9,38),(7,18,21,10,41),(7,18,22,11,44))

def compositions(n,k):
    if k==1:
        yield (n,)
        return
    for c in range(n+1):
        for rest in compositions(n-c,k-1):yield (c,)+rest

def main():
    survivors=[];tested=0
    for k in range(19,23):
        for c in compositions(8,9):
            tested+=1
            numerator=2*k+2*sum(x*r[1] for x,r in zip(c,ROWS))-122
            if numerator%3:continue
            e=numerator//3
            r=8+sum(x*row[3] for x,row in zip(c,ROWS))
            if e<0 or e+r>118:continue
            if 9*c[0]+4*c[1]+3*(k==19)+3*e>210:continue
            survivors.append({'full_row_edge_count':k,'pair_counts':c,'e':e,'r':r})
    assert survivors==[{'full_row_edge_count':20,'pair_counts':(4,0,4,0,0,0,0,0,0),'e':58,'r':60}],survivors
    print(json.dumps({'status':'passed','whole_theorem_verified':False,
                      'tested_integer_profiles':tested,'survivors':survivors},indent=2))

if __name__=='__main__':main()
