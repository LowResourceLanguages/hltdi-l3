This tools generate an alignment file from two files which are parallel texts


Usage: python gen_align.py <file1> <file2> <start line> <end line>
eg)python gen_align.py kor.txt eng.txt 1 10
--> this will create a file "texts.aln" which has 10 pairs of senteces from both files and initalized alignment for each pair of sentences.
This will look like

----
장점 과 단점 이 있 다면서 , 모든 사람 들 을 위하 ㄴ 무상 교육 과 보건 체계 를 가지 고 있 지만 또 모든 사람 들 이 식량 이나 기본 생필품 을 얻 는 데 있 어 문제 가 있 습니다
There are advantages and disadvantages , they have free education for everybody and health care , but they also have problems with the food and how they get fundamental stuff for everybody .
(lp1
NaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNaNa.
....

