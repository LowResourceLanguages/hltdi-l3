import cPickle
import sys


"""
Given two filenames which are bitexts perfectly aligned to each other on every line,
Generate a single file that has both texts and initial alignment.
The output file would look like
----
line1_from_file1
line1_from_file2
line1_alignment
line2_from_file1
line2_from_file2
line2_alignment
...
"""

if len(sys.argv) > 4:
	file1 = sys.argv[1]
	file2 = sys.argv[2]
	start_line = int(sys.argv[3])
	end_line = int(sys.argv[4])
else:
	exit(1)

print "Reading", file1, "..." 
print "Reading", file2, "..." 

f1 = open(file1, 'r')
f2 = open(file2, 'r')
fout = open("texts.aln",'w')

line_idx = 0
for f1_line in f1:
	f2_line = f2.readline()
	line_idx = line_idx + 1
	if line_idx < start_line:
		continue
	if line_idx > end_line:
		break
		
	fout.write(f1_line)
	fout.write(f2_line)
	
	alignment = [None] * (1 + len(f1_line.split()))
	cPickle.dump(alignment,fout)

print "Done. Created an output file 'texts.aln' with %i lines" % (line_idx)
f1.close()
f2.close()
fout.close()
