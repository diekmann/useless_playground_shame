


def d(E, v0):
	print E
	V = list(set([(v0,x) for x in ([b for (a,b) in E if a == v0 and b != v0] + [a for (a,b) in E if b == v0 and a != v0])]))
	Discovered = [(v0,v0)]
	#V = [(v0,v0)]
	#Discovered = []
	cycle = False
	
	while V != [] and not cycle:
		assert(all(x != y for (x,y) in V))
		assert(all(x != y or x == v0 for (x,y) in Discovered))
		assert(set(V+[(x,y) for (x,y) in V]).intersection(set(Discovered+[(x,y) for (x,y) in Discovered])) == set())
		(vparent,v) = V[0]
		succs = [b for (a,b) in E if a == v and b != vparent and b != v] + [a for (a,b) in E if b == v and a != vparent and a!= v]
		succs = list(set(succs))
		print "(%s,%s) %s %s %s" % (vparent,v, succs, V, Discovered)
		#if set(succs).intersection(set(Discovered)) != set():
		if v in [b for (_, b) in Discovered]: # or v in [a for (a, _) in Discovered]:
			print "cycle: %s, %s, ..." % ((vparent,v), [(a,b) for (a,b) in Discovered if b == vparent])
			cycle = True
		else:
			V = V[1:]
			Discovered = [((vparent,v))] + Discovered
			V = [(v,a) for a in succs] + V
	return cycle


assert(not  d([(1,2)], 1))
assert(not  d([(1,1)], 1))
assert(not  d([(1,2), (2,1)], 1))
assert(not  d([(1,2), (2,1), (2,3), (3,2)], 1))
assert(not  d([(1,2), (1,1), (2,2), (9,10)], 1))
assert(not  d([(1,2), (2,3), (8,8)], 1))
assert(  d([(1,2), (2,3), (3,5), (5,1)], 1))
assert(  d([(1,2), (2,3), (3,5), (1,5)], 1))
assert(  d([(1,2), (2,3), (3,5), (5,8), (1,42), (42,2)], 1))
assert(not  d([(1,2), (2,3), (3,5), (5,8), (1,42)], 1))
assert(  d([(1,2), (2,3), (3,5), (5,8), (1,42), (42, 3)], 3))
assert(not  d([(1,2), (2,3), (3,5), (5,8)], 1))
assert(not  d([(1,2), (2,3), (3,5), (5,8), (42,1)], 1))
assert(not  d([(1,2), (2,3), (3,5), (5,8), (42,1), (8,8)], 1))
assert(not  d([(2,1), (2,2), (2,3), (3,2), (3,3)], 3))
assert(not  d([(2,1), (1,2), (2,3), (3,2), (3,3)], 3))
assert(  d([(1, 1), (1, 2), (1, 3), (3, 1), (3, 2), (3, 3)], 3))


