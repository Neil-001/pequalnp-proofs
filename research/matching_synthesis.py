"""Encode the three cyclic matchings on six bits as a fan-in-two circuit SAT instance.

The first selectable wire is constant false, matching out-of-range reads.
A missing operand or an empty gate is represented by a repeated operand or
a constant. Unused gates allow a smaller circuit to fit any larger bound.
The solver chooses the three output wires independently.
"""
import argparse
from itertools import combinations, product
from pathlib import Path


class Instance:
    def __init__(self):
        self.variables = 0
        self.clauses = []
        self.gates = []
        self.outputs = []

    def new(self):
        self.variables += 1
        return self.variables

    def choice(self, count):
        bits = [self.new() for _ in range(count)]
        self.clauses.append(bits)
        self.clauses.extend([-a, -b] for a, b in combinations(bits, 2))
        return bits

    def mux(self, selectors, wires):
        result = self.new()
        for select, wire in zip(selectors, wires, strict=True):
            self.clauses.extend(([-select, -result, wire], [-select, result, -wire]))
        return result

    def write(self, destination):
        with destination.open("w") as out:
            print("p cnf", self.variables, len(self.clauses), file=out)
            for clause in self.clauses:
                print(*clause, 0, file=out)


def canonical_raw_layer(cnf, truth):
    patterns = sorted(
        [(b, a, op) for a, b in combinations(range(1, 7), 2) for op in (0, 1)]
        + [(a, a, 2) for a in range(1, 7)]
    )
    present = {}
    for b, a, op in patterns:
        candidates = []
        for ops, lhs, rhs in cnf.gates:
            hit = cnf.new()
            literals = (ops[op], lhs[a], rhs[b])
            cnf.clauses.extend([-hit, literal] for literal in literals)
            cnf.clauses.append([hit, *(-literal for literal in literals)])
            candidates.append(hit)
        flag = cnf.new()
        cnf.clauses.append([-flag, *candidates])
        cnf.clauses.extend([-hit, flag] for hit in candidates)
        present[b, a, op] = flag
    # Pick a lexicographically maximal raw-gate set among all transformations
    # preserving the three matchings up to output permutation.
    for flip, sign, lshift, rshift in product((0, 1), (1, -1), range(3), range(3)):
        rename = {}
        for side, offset in product(range(2), range(3)):
            delta = (lshift, rshift)[side]
            rename[1+3*side+offset] = 1+3*(side ^ flip)+(sign*offset+delta) % 3
        prefix = truth
        for b, a, op in patterns:
            lo, hi = sorted((rename[a], rename[b]))
            first, second = present[b, a, op], present[hi, lo, op]
            if first == second:
                continue
            equal = cnf.new()
            cnf.clauses.extend(([-prefix, first, -second],
                                [-prefix, -first, -second, equal],
                                [-prefix, first, second, equal]))
            prefix = equal


def pin_budget(cnf, truth, products, value, lower, raw=6, positions=None):
    # Fix each original input in turn. Two Boolean flags track whether a wire
    # has become identically false or true by constant propagation.
    for pin in range(raw) if positions is None else positions:
        zero = [truth] + [truth if j == pin and not value else -truth for j in range(raw)]
        one = [-truth] + [truth if j == pin and value else -truth for j in range(raw)]
        removed = []
        paid = 0
        for e in products:
            hit = pin in (e % 3, 3+(e % 3+e//3) % 3)
            paid += int(hit)
            zero.append(truth if hit and not value else -truth)
            one.append(-truth)
        for ops, lhs, rhs in cnf.gates:
            az, ao = cnf.mux(lhs, zero), cnf.mux(lhs, one)
            bz, bo = cnf.mux(rhs, zero), cnf.mux(rhs, one)
            z, o, gone = cnf.new(), cnf.new(), cnf.new()
            AND, OR, NOT = ops
            # Forward implications suffice. Every flag forced here has a
            # valid constant or gate-removal justification.
            cnf.clauses.extend(([-AND,-az,z],[-AND,-bz,z],[-AND,-ao,-bo,o],
                                [-OR,-ao,o],[-OR,-bo,o],[-OR,-az,-bz,z],
                                [-NOT,-ao,z],[-NOT,-az,o]))
            cnf.clauses.extend([-flag,gone] for flag in (az,ao,bz,bo))
            zero.append(z)
            one.append(o)
            removed.append(gone)
        cap = len(cnf.gates)+len(products)-lower-paid
        if cap < 0:
            cnf.clauses.append([])
        else:
            cnf.clauses.extend([-v for v in group] for group in combinations(removed,cap+1))


def encode(limit, sparse=False, canonical=False, minimal=False, monotone=False, symmetry=False, pairs=False, products=(), fix_first=False, sparse_minimum=False, first=None, fix_zero=False, pins=False, pin_zero=False, product_cap=None, sparse_bound=False, restricted_first=False, nested=False):
    cnf = Instance()
    truth = cnf.new()
    cnf.clauses.append([truth])
    rows = list(product((False, True), repeat=6))
    if pairs:
        rows = [r for r in rows if sum(r) <= 2]
    elif sparse:
        rows = [r for r in rows if sum(r[:3]) <= 1 and sum(r[3:]) <= 1]
    if sparse_minimum and (limit != 12 or products or fix_first):
        raise ValueError("the twelve-gate minimum applies to the original sparse problem")
    if fix_first or fix_zero:
        if sparse or pairs or products or symmetry:
            raise ValueError("use the full five-input restriction with --fix-first")
        rows = [r for r in rows if r[0] == bool(fix_first)]
    wires = [[-truth] + [truth if x else -truth for x in row[int(fix_first or fix_zero):]] for row in rows]
    uses = [[] for _ in range(limit)]
    previous_rhs = []
    previous_lhs = []
    for row, columns in zip(rows, wires, strict=True):
        for edge in products:
            j, color = edge % 3, edge // 3
            columns.append(truth if row[j] and row[3+(j+color) % 3] else -truth)
    base = 7-int(fix_first or fix_zero)+len(products)
    redundant = []
    for i in range(limit):
        lhs = cnf.choice(base+i)
        rhs = cnf.choice(base+i)
        operations = cnf.choice(3)
        conjunction, disjunction, negation = operations
        cnf.gates.append((operations, lhs, rhs))
        if monotone:
            cnf.clauses.append([-negation])
        for gate in range(i):
            uses[gate].extend((lhs[base+gate], rhs[base+gate]))
        # Commutative gates take operands in wire order. A NOT can use the
        # same wire twice because only its first operand contributes.
        for index, select in enumerate(lhs):
            for earlier in rhs[:index]:
                cnf.clauses.append([-select, -earlier])
            cnf.clauses.append([-negation, -select, rhs[index]])
        if canonical:
            # Every target is nonconstant. Constant-fold a realizing circuit,
            # then remove identity gates. It can be padded with unused gates.
            cnf.clauses.extend(([-lhs[0]], [-rhs[0]]))
            for lo, hi in zip(lhs, rhs, strict=True):
                cnf.clauses.append([-lo, -hi, negation])
            # Choose ready gates in increasing (maximum input, minimum input)
            # order. A newly ready gate uses the just-created wire, whose
            # index exceeds both inputs of the gate that created it.
            for prev, selected in enumerate(previous_rhs):
                for earlier in rhs[:prev]:
                    cnf.clauses.append([-selected, -earlier])
                for oldlo, oldsel in enumerate(previous_lhs[:prev+1]):
                    for early in lhs[:oldlo]:
                        cnf.clauses.append([-selected, -rhs[prev], -oldsel, -early])
            if i == 0 and not products and not (fix_first or fix_zero):
                # Transposition, simultaneous reflection, and independent
                # cyclic shifts preserve the set of the three targets.
                # The orbits for a raw pair are same-side and cross-side.
                cnf.clauses.append([lhs[1]])
                cnf.clauses.append([rhs[1], rhs[2], rhs[4]])
        if restricted_first and canonical and i == 0 and (fix_first or fix_zero):
            # The pin leaves reflection swapping the two other left inputs,
            # independent right rotations, and simultaneous reflection.
            options = {(1,1),(3,3),(1,2),(1,3),(3,4)}
            for a in range(1,6):
                for b in range(a,6):
                    if (a,b) not in options:
                        cnf.clauses.append([-lhs[a],-rhs[b]])
        previous_lhs, previous_rhs = lhs, rhs
        incomparable_ab, incomparable_ba, output_bits = [], [], []
        sparse_ab, sparse_ba, sparse_out = [], [], []
        for row, columns in zip(rows, wires, strict=True):
            a, b = cnf.mux(lhs, columns), cnf.mux(rhs, columns)
            out = cnf.new()
            cnf.clauses.extend((
                [-conjunction, -out, a], [-conjunction, -out, b],
                [-conjunction, out, -a, -b],
                [-disjunction, out, -a], [-disjunction, out, -b],
                [-disjunction, -out, a, b],
                [-negation, -out, -a], [-negation, out, a],
            ))
            columns.append(out)
            if (minimal or sparse_minimum or sparse_bound) and (not sparse_minimum or (sum(row[:3]) <= 1 and sum(row[3:]) <= 1)):
                output_bits.append(out)
                ab, ba = cnf.new(), cnf.new()
                cnf.clauses.extend(([-ab, a], [-ab, -b], [-ba, b], [-ba, -a]))
                incomparable_ab.append(ab)
                incomparable_ba.append(ba)
                if sparse_bound and sum(row[:3]) <= 1 and sum(row[3:]) <= 1:
                    sparse_ab.append(ab)
                    sparse_ba.append(ba)
                    sparse_out.append(out)
        if sparse_bound:
            if fix_first or fix_zero or products:
                raise ValueError("this sparse bound assumes six raw inputs and no additional wires")
            expendable = cnf.new()
            redundant.append(expendable)
            cnf.clauses.extend(([expendable,negation,*sparse_ab], [expendable,negation,*sparse_ba],
                                [expendable,*sparse_out], [expendable,*(-v for v in sparse_out)]))
        if minimal or sparse_minimum:
            # Comparable operands make AND/OR return an existing wire.
            cnf.clauses.extend(([negation, *incomparable_ab], [negation, *incomparable_ba],
                                output_bits, [-bit for bit in output_bits]))
    for color in range(3):
        output = cnf.choice(limit)
        cnf.outputs.append(output)
        for select, gate in zip(output, range(limit), strict=True):
            uses[gate].append(select)
            # All six variables can be pivotal even on the sparse rows.
            # A cone with g binary gates covers at most g+1 inputs.
            if canonical and not products and gate < 4-int(fix_first)-2*int(fix_zero):
                cnf.clauses.append([-select])

            for row, columns in zip(rows, wires, strict=True):
                value = any(row[j] and row[3+(j+color) % 3] for j in range(3))
                cnf.clauses.append([-select, columns[base+gate] if value else -columns[base+gate]])
    if canonical:
        # No distinct target implies another, and no two are complements.
        # Consequently a designated output cannot directly feed another.
        for earlier, later in combinations(range(limit), 2):
            _, lhs, rhs = cnf.gates[later]
            for color, other in product(range(3), repeat=2):
                if color != other:
                    prefix = [-cnf.outputs[color][earlier], -cnf.outputs[other][later]]
                    cnf.clauses.extend((prefix + [-lhs[base+earlier]], prefix + [-rhs[base+earlier]]))
    if sparse_bound:
        if limit < 12:
            raise ValueError("use the independent sparse certificate through size eleven")
        cnf.clauses.extend([-v for v in group] for group in combinations(redundant,limit-12+1))
    if product_cap is not None:
        if not canonical or fix_first or fix_zero:
            raise ValueError("the product cap requires canonical six-input gates")
        direct = []
        for ops, lhs, rhs in cnf.gates:
            cross = cnf.new()
            for a in range(1,4):
                for b in range(4,7):
                    cnf.clauses.append([-ops[0],-lhs[a],-rhs[b],cross])
            direct.append(cross)
        # A minimum circuit never duplicates a direct product. Extra unused
        # gates for padding may be chosen to be NOT gates on computed wires.
        cap = product_cap-len(products)
        if cap < 0:
            cnf.clauses.append([])
        else:
            cnf.clauses.extend([-v for v in group] for group in combinations(direct,cap+1))
    if nested:
        if not fix_first or not canonical:
            raise ValueError("nested restrictions need the first left input fixed true")
        for positions, on, off in ((range(2),7,6),(range(2,5),6,7)):
            pin_budget(cnf,truth,(),True,on,5,positions)
            pin_budget(cnf,truth,(),False,off,5,positions)
    if pins or pin_zero:
        if not canonical or fix_first or fix_zero:
            raise ValueError("pin bounds apply to the normalized six-input search")
        if pins:
            pin_budget(cnf, truth, products, True, 11)
        if pin_zero:
            pin_budget(cnf, truth, products, False, 9)
    if first is not None:
        if not canonical or products or fix_first:
            raise ValueError("first-gate cases refer to the canonical six-input problem")
        ops, lhs, rhs = cnf.gates[0]
        op, second = {"not": (2, 1), "and-side": (0, 2), "or-side": (1, 2),
                      "and-cross": (0, 4), "or-cross": (1, 4)}[first]
        cnf.clauses.extend(([ops[op]], [lhs[1]], [rhs[second]]))
    if symmetry:
        if not canonical or products:
            raise ValueError("raw-layer symmetry requires canonical ordering and no prescribed products")
        canonical_raw_layer(cnf, truth)
    if minimal:
        # A minimum circuit has no unused gates. An UNSAT result with this
        # flag gives a lower bound only after every smaller size is excluded.
        cnf.clauses.extend(uses)
    return cnf


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("gates", type=int)
    parser.add_argument("destination", type=Path)
    parser.add_argument("--sparse", action="store_true")
    parser.add_argument("--canonical", action="store_true")
    parser.add_argument("--minimal", action="store_true")
    parser.add_argument("--monotone", action="store_true")
    parser.add_argument("--symmetry", action="store_true")
    parser.add_argument("--pairs", action="store_true")
    parser.add_argument("--products", type=int, nargs="*", choices=range(9), default=[],
                        help="free precomputed products, numbered by matching then by left input")
    parser.add_argument("--fix-first", action="store_true", help="fix left input zero to true")
    parser.add_argument("--sparse-minimum", action="store_true",
                        help="use the independent lower bound of twelve on sparse inputs")
    parser.add_argument("--first", choices=["not", "and-side", "or-side", "and-cross", "or-cross"])
    parser.add_argument("--fix-zero", action="store_true", help="fix the first left input to false")
    parser.add_argument("--pins", action="store_true", help="apply the true-restriction lower bound")
    parser.add_argument("--pin-zero", action="store_true", help="apply the false-restriction lower bound")
    parser.add_argument("--product-cap", type=int, help="use an independently verified bound on raw cross-products")
    parser.add_argument("--sparse-bound", action="store_true", help="at least twelve gates survive on the sparse rows")
    parser.add_argument("--restricted-first", action="store_true", help="normalize the first gate for a pinned input")
    parser.add_argument("--nested", action="store_true", help="apply the four two-input restriction bounds")
    args = parser.parse_args()
    encode(args.gates, args.sparse, args.canonical, args.minimal, args.monotone, args.symmetry, args.pairs, args.products, args.fix_first, args.sparse_minimum, args.first, args.fix_zero, args.pins, args.pin_zero, args.product_cap, args.sparse_bound, args.restricted_first, args.nested).write(args.destination)
