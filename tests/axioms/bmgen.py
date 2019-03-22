
## Generator of "binary maze" instances for the blocker-strips domain.
## Note: Instance size is approx O(2^depth).

import sys
import random

if len(sys.argv) < 2:
    print(sys.argv[0] + ": <depth>")
    sys.exit(0)

depth = int(sys.argv[1])
assert depth > 1

levels = [ list(range(2**d)) for d in range(0, depth) ]
levels.append(levels[depth - 1][:])

n = 0
for i in list(range(depth + 1))[::-1]:
    for j in range(len(levels[i])):
        levels[i][j] = n
        n += 1
    random.shuffle(levels[i])

#print(levels)
#print(n)

print("(define (problem binary-maze-" + str(depth) + ")")
print("  (:domain blocker-strips)")
print("  (:objects", end="")
for k in range(n):
    print(" n" + str(k), end="")
print(")") # end :objects
print("  (:init")
print("    (is-zero n0)")
for k in range(n - 1):
    print("    (next n" + str(k) + " n" + str(k + 1) + ")")
for k in levels[depth]:
    print("    (exit n" + str(k) + ")")
# edges
for i in range(len(levels[depth])):
    print("    (edge n" + str(levels[depth][i]) +
          " n" + str(levels[depth - 1][i]) + ")")
    print("    (edge n" + str(levels[depth - 1][i]) +
          " n" + str(levels[depth][i]) + ")")
    if i > 0:
        print("    (edge n" + str(levels[depth][i - 1]) +
              " n" + str(levels[depth - 1][i]) + ")")
        print("    (edge n" + str(levels[depth - 1][i]) +
              " n" + str(levels[depth][i - 1]) + ")")

for j in range(depth - 1):
    for i in range(len(levels[j])):
        # levels[j][i] -> levels[j+1][2*i]
        print("    (edge n" + str(levels[j][i]) +
              " n" + str(levels[j + 1][2*i]) + ")")
        print("    (edge n" + str(levels[j + 1][2*i]) +
              " n" + str(levels[j][i]) + ")")
        # levels[j][i] -> levels[j+1][(2*i)+1]
        print("    (edge n" + str(levels[j][i]) +
              " n" + str(levels[j + 1][(2*i) + 1]) + ")")
        print("    (edge n" + str(levels[j + 1][(2*i) + 1]) +
              " n" + str(levels[j][i]) + ")")

print("    (cat n" + str(n - 1) + ")")
print("    (blockers-turn)")

print("   )") # end :init

print("  (:goal (trapped))")
print("  )")
