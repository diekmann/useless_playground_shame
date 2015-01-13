filename = "....txt"

import os
if not os.path.isfile(filename):
	print("Error: file not found")
	import sys
	sys.exit(-1)
print("evaluating file {}".format(filename))
from collections import defaultdict
s = defaultdict(int)
with open(filename, mode='r', encoding='utf-8') as f:
	for l in f:
		l = l.strip()
		tmp = l.split('.')
		l = tmp[-2]+'.'+tmp[-1]
		if len(tmp[-2]) <= 2 and len(tmp) >= 3:
			l = tmp[-3]+'.'+l
		s[l] +=1
s = [(k,s[k]) for k in sorted(s, key=s.get)]
from pprint import pprint
pprint(s)
