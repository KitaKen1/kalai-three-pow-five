#!/usr/bin/env python3
"""Independent integer enumeration for the zero-stress two-full-pair proof."""
import json
from .check_one_pair import compositions,ROWS

SIX=((6,13,13,6,26),(6,14,15,7,29),(6,14,16,8,32))
FULL=((19,8),(19,9),(20,8),(20,9),(20,10),(21,8),
      (21,9),(21,10),(22,8),(22,9),(22,10))

def main():
    survivors=[];tested=0
    for s in range(3):
        for f in compositions(2,11):
            for c in compositions(6,9):
                tested+=1
                num=2*SIX[s][1]+2*sum(k*m for m,(k,r) in zip(f,FULL))+2*sum(m*R[1] for m,R in zip(c,ROWS))-122
                if num%3:continue
                e=num//3
                r=SIX[s][3]+sum(m*r for m,(k,r) in zip(f,FULL))+sum(m*R[3] for m,R in zip(c,ROWS))
                if e<0 or e%2 or r%2 or e+r>118:continue
                if 9*c[0]+4*c[1]+4*f[0]+8*f[1]+3*e>210:continue
                survivors.append({'six_row_index':s,'seven_pair_counts':c,'full_pair_counts':f,'e':e,'r':r})
    expected=[(0,(2,4,0,0,0,0,0,0,0),(2,0,0,0,0,0,0,0,0,0,0),56,62),
              (0,(4,0,2,0,0,0,0,0,0),(0,0,1,0,0,1,0,0,0,0,0),58,60)]
    got=[(x['six_row_index'],x['seven_pair_counts'],x['full_pair_counts'],x['e'],x['r']) for x in survivors]
    assert sorted(got)==sorted(expected),survivors
    print(json.dumps({'status':'passed','whole_theorem_verified':False,
                     'tested_integer_profiles':tested,'survivors':survivors},indent=2))

if __name__=='__main__':main()
