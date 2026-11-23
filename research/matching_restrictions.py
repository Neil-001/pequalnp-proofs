"""Encode a restriction on raw matching inputs, allowing constant and raw outputs."""
from argparse import ArgumentParser
from itertools import product
from pathlib import Path

from matching_synthesis import Instance


def restricted(limit, pattern):
    if len(pattern) != 6 or set(pattern)-set("01*"):
        raise ValueError("expected six entries from 0, 1, *")
    free = [i for i, value in enumerate(pattern) if value == "*"]
    rows = [r for r in product((0,1),repeat=6)
            if all(value == "*" or int(value) == r[i] for i,value in enumerate(pattern))]
    cnf = Instance()
    truth = cnf.new()
    cnf.clauses.append([truth])
    wires = [[-truth,truth,*(truth if row[i] else -truth for i in free)] for row in rows]
    base = 2+len(free)
    prev = []
    for i in range(limit):
        a,b = cnf.choice(base+i),cnf.choice(base+i)
        conj, disj, neg = cnf.choice(3)
        for select in (a,b):
            cnf.clauses.extend(([-select[0]],[-select[1]]))
        for index,choice in enumerate(a):
            cnf.clauses.extend([-choice,-earlier] for earlier in b[:index])
            cnf.clauses.append([-neg,-choice,b[index]])
            cnf.clauses.append([-choice,-b[index],neg])
        for index,choice in enumerate(prev):
            cnf.clauses.extend([-choice,-earlier] for earlier in b[:index])
        prev=b
        for w in wires:
            lhs,rhs=cnf.mux(a,w),cnf.mux(b,w)
            out=cnf.new()
            cnf.clauses.extend(([-conj,-out,lhs],[-conj,-out,rhs],[-conj,out,-lhs,-rhs],
                                [-disj,out,-lhs],[-disj,out,-rhs],[-disj,-out,lhs,rhs],
                                [-neg,-out,-lhs],[-neg,out,lhs]))
            w.append(out)
    for color in range(3):
        selectors=cnf.choice(base+limit)
        for i,select in enumerate(selectors):
            for row,w in zip(rows,wires,strict=True):
                value=any(row[j] and row[3+(j+color)%3] for j in range(3))
                cnf.clauses.append([-select,w[i] if value else -w[i]])
    return cnf


if __name__ == "__main__":
    parser=ArgumentParser(description=__doc__)
    parser.add_argument("gates",type=int)
    parser.add_argument("pattern")
    parser.add_argument("destination",type=Path)
    args=parser.parse_args()
    restricted(args.gates,args.pattern).write(args.destination)
