This tools generate an alignment file from two files which are parallel texts


Usage: python gen_align.py <file1> <file2> <start line> <end line>
eg)python gen_align.py kor.txt eng.txt 1 10
--> this will create a file "texts.aln" which has 10 pairs of senteces from both files and initalized alignment for each pair of sentences.
This will look like

----
���� �� ���� �� �� �ٸ鼭 , ��� ��� �� �� ���� �� ���� ���� �� ���� ü�� �� ���� �� �� ���� �� ��� ��� �� �� �ķ� �̳� �⺻ ����ǰ �� �� �� �� �� �� ���� �� �� ���ϴ�
There are advantages and disadvantages , they have free education for everybody and health care , but they also have problems with the food and how they get fundamental stuff for everybody .
(lp1
NaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNa.
....

