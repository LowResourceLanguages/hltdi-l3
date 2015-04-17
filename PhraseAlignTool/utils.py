import re
import cPickle

#PUNCTUATION = ['"', "''", '``', ';', ':', ',', '.', '--', '?', '!', '(', ')']
PUNCTUATION = ['"', ';', ':', ',', '.', '?', '!']
RE_SPECIAL_CHARACTERS = ['.', '^', '$', '*', '+', '?', '{', '}', '(', ')', '[', ']', '|']

def get_wordlist(s,low=False):
	"""
	From a string, get a list of words
	"""
	if low:
		s = s.lower()
	
	# remove punctuations
	#for x in PUNCTUATION:
	#	s = s.replace(x,' ')
	# split the string with space, tab, newline to get a list of words
	wordlist = s.split()
	return wordlist
	
'''	
def get_wordlist(s,low=False):
	"""
	From a string, get a list of words
	"""
	if low:
		s = s.lower()
	
	# remove punctuations
	for x in PUNCTUATION:
		s = s.replace(x,' ')
	# split the string with space, tab, newline to get a list of words
	wordlist = s.split()
	return wordlist
'''
def remove_stopwords(wlist):
	newlist = []
	for w in wlist:
		if w not in STOPWORDS:
			newlist.append(w)
	return newlist


def get_unaligned_word_indexes(alignment,target_len):
	"""
	Returns a tuple of lists of word indexes that have not been aligned (value:None)
	given target_len (source_len is unnecessary because it is the length of alignment)
	eg) return ([2],[1,3])
	"""
	if alignment == None or alignment == []:
		return ([],[])
	src_list = []
	for idx, n in enumerate(alignment[1:],1):
		if n == None:
			src_list.append(idx)
	tar_list = remAfromB(alignment,range(1,target_len+1))
	return (src_list, tar_list)
	
def remAfromB(A,B):
	"""
	Return a list of B's elements that are not included in A
	For example, remAfromB([[1],[3,4]],range(7)) --> 
	"""
	if not isinstance(B,list):
			return B
	newB = B
	if not isinstance(A,list):
		if A in newB:
			newB.remove(A)
			return newB
	# at this point, both A and B are lists
	for n in A:
		if isinstance(n,list):
			newB = remAfromB(n,newB)
		else:
			if n in newB:
				newB.remove(n)
	return newB
	
def get_aligned_pairs(alignment):
	'''
	Given an alignment, return two list 'src_phrases', 'tar_phrases' which are paired.
	alignment = [None, [1,2], [4], [0], [3], [4], [4]]
	--> [[[1],[2,5,6],[4]], [[1,2],[4],[3]]]
	'''
	if alignment == None or alignment == []:
		return ([],[])
	pairs = {}
	for idx, n in enumerate(alignment[1:],1):
		if n == None or n == [0]:
			continue
		pairs[tuple(n)] = pairs.get(tuple(n),[]) + [idx]
	return (pairs.values(),map(list,pairs.keys())) 

def get_aligned_pairs2(alignment):
	'''
	Given an alignment, return two list 'src_phrases', 'tar_phrases' which are paired.
	Includes the alignment to NULL too unlike 'get_aligned_pairs()'
	alignment = [[5,6], [1,2], [4], [0], [3], None, [4], [4], [0]]
	--> [[0], [1], [3, 8], [4], [2, 6, 7]] [[5, 6], [1, 2], [0], [3], [4]]
	'''
	if alignment == None or alignment == []:
		return ([],[])
	pairs = {}
	for idx, n in enumerate(alignment):
		if n == None:
			continue
		pairs[tuple(n)] = pairs.get(tuple(n),[]) + [idx]
	return (pairs.values(),map(list,pairs.keys())) 

def pairs2alignment(alnp1,alnp2,p1_len):
	'''
	Given aligned pairs and pair1 length, return an alignment.
	This is the reverse function of 'get_aligned_pairs2()'.
	alnp1 = [[0], [1], [3, 8], [4], [2, 6, 7]], alnp2 = [[5, 6], [1, 2], [0], [3], [4]]
	--> [[5,6], [1,2], [4], [0], [3], None, [4], [4], [0]]
	'''
	alignment = []
	for i in range(p1_len):
		found = False
		for p_idx, phrase in enumerate(alnp1):
			if i in phrase:
				alignment.append(alnp2[p_idx])
				found = True
				break
		if not found:
			alignment.append(None)
	return alignment

def clear_align(alnp1,alnp2,p1,p2):
	'''
	Given aligned pairs and new selections from both sides
	it changes the aligned pairs
	alnp1 = [[0], [1], [3, 8], [4], [2, 6, 7]], alnp2 = [[5, 6], [1, 2], [0], [3], [4]], p1=[3], p2=[]
	--> alnp1=[[0], [8], [4], [2, 6, 7]], alnp2 = [[5, 6], [1, 2], [0], [3], [4]]
	alnp1 = [[0], [1], [3], [4], [2, 6, 7]], alnp2 = [[5, 6], [1, 2], [0], [3], [4]], p1=[3], p2=[]
	--> alnp1=[[0], [], [4], [2, 6, 7]], alnp2 = [[5, 6], [1, 2], [0], [3], [4]] 
	# keep going to remove null list and its counterpart
	--> alnp1=[[0], [4], [2, 6, 7]], alnp2 = [[5, 6], [0], [3], [4]]
	'''
	for w_idx in p1:
		for p_idx, phrase in enumerate(alnp1):
			if w_idx in phrase:
				phrase.remove(w_idx)
				if len(phrase)==0: # phrase == []
					alnp1.pop(p_idx)
					alnp2.pop(p_idx)
	for w_idx in p2:
		for p_idx, phrase in enumerate(alnp2):
			if w_idx in phrase:
				phrase.remove(w_idx)
				if len(phrase)==0: # phrase == []
					alnp1.pop(p_idx)
					alnp2.pop(p_idx)

def null_align(alnp1,alnp2,p1,p2):
	'''
	Given aligned pairs and new selections from both sides
	it alignes the selections to NULL
	alnp1 = [[0], [1], [3, 8], [4], [2, 6, 7]], alnp2 = [[5, 6], [1, 2], [0], [3], [4]], p1=[2], p2=[1]
	--> alnp1=[[0], [1], [3, 8, 2], [4], [6, 7]], alnp2 = [[5, 6, 1], [2], [0], [3], [4]]
	'''
	clear_align(alnp1,alnp2,p1,p2)
	
	if [0] in alnp1:
		alnp1_null_idx = alnp1.index([0])
		alnp2[alnp1_null_idx] = alnp2[alnp1_null_idx] + p2
	else:
		alnp1.append([0])
		alnp2.append(p2)
		
	if [0] in alnp2:
		alnp2_null_idx = alnp2.index([0])
		alnp1[alnp2_null_idx] = alnp1[alnp2_null_idx] + p1
	else:
		alnp2.append([0])
		alnp1.append(p1)


			
def realign(alnp1,alnp2,p1,p2):
	'''
	Given aligned pairs and new selections from both sides
	it realigns the pairs
	alnp1 = [[0], [1], [3, 8], [4], [2, 6, 7]], alnp2 = [[5, 6], [1, 2], [0], [3], [4]], p1=[3], p2=[1,2]
	--> alnp1=[[0], [8], [4], [2, 6, 7], [3]], alnp2=[[5, 6], [0], [3], [4], [1, 2]]
	alnp1 = [[0], [1], [3, 8], [4], [2, 6, 7]], alnp2 = [[5, 6], [1, 2], [0], [3], [4]], p1=[3], p2=[1]
	--> alnp1=[[0], [1], [8], [4], [2, 6, 7], [3]], alnp2=[[5, 6], [2], [0], [3], [4], [1, 2]]
	We treat NULL in the same way for now despite the potential issues about this. 
	alnp1 = [[0], [1], [3, 8], [4], [2, 6, 7]], alnp2 = [[5, 6], [1, 2], [0], [3], [4]], p1=[0], p2=[3]
	--> alnp1=[[0], [1], [8], [2, 6, 7], [3]], alnp2=[[5, 6, 3], [2], [0], [4], [1, 2]]
	'''
	clear_align(alnp1,alnp2,p1,p2)
	alnp1.append(p1)
	alnp2.append(p2)

def get_aligned_widx(alnp1):
	widxs = set([])
	for p in alnp1:
		widxs = widxs | set(p)
	return list(widxs)
		
def get_null_aligned_widx(alnp1,alnp2):
	alnp1_null_aligned = []
	alnp2_null_aligned = []
	if [0] in alnp1:
		alnp1_null_idx = alnp1.index([0])
		alnp2_null_aligned = alnp2[alnp1_null_idx]
	if [0] in alnp2:
		alnp2_null_idx = alnp2.index([0])
		alnp1_null_aligned = alnp1[alnp2_null_idx]
	return alnp1_null_aligned,alnp2_null_aligned
	
def phrase_construct(ls,idxls):
	newls = []
	pre_i = None
	for i in idxls:
		if newls == []:
			newls.append(ls[i-1])
		elif i > pre_i + 1:
			newls += ['<any>', ls[i-1]]
		else:
			newls.append(ls[i-1])
		pre_i = i

	s = ' '.join(str(n) for n in newls)
	return (newls, s)

	
	
def save_object(obj,filename):
	fout = open(filename, "w")
	print "Writing", filename, "..."
	cPickle.dump(obj,fout)
	fout.close()

def load_object(filename):
	fin = open(filename, "r")
	print "Reading", filename, "..."
	obj = cPickle.load(fin)
	fin.close()
	return obj
	
def contain_assigned_word(ph,alignment):
	# ph is a phrase which is tuple of word indexes eg) (1,3,4)
	#print ph,alignment
	for i,align in enumerate(alignment):
		if align != None:	# i-th word is aligned to something
			if i in ph:
				return True
	return False
		
def generate_phset(i,phset,alignment):
	phset_old_ones = set([])
	for ph in phset:
		if not contain_assigned_word(ph,alignment):
			phset_old_ones.add(ph)
	#print phset_old_ones
	if alignment[i] != None:
		phset_new_ones = set([])
	else:			
		phset_new_ones = set([(i,)])
		for ph in phset_old_ones:
			phset_new_ones.add(ph + (i,))
	return ( phset_old_ones | phset_new_ones, phset_new_ones)

def get_word_idx_from_str_idx(l2_str,str_idx):
	str2word = []
	word_idx = 0
	for i, c in enumerate(l2_str):
		if not c.isspace():
			if i==0 or l2_str[i-1].isspace():
				word_idx += 1
		str2word.append(word_idx)
	return [str2word[k] for k in str_idx]

def find_match_in_target(mstr,list2,alignment):
	'''
	eg) msg = 'have <any> in mind'
	    list2 = ['I', 'have', 'a', 'good', 'idea', 'in', 'mind']
	    cf. <any> can match any sequence of non-empty words
	For now, just concern the string match without any other constraints
	This converts list l2 to str to use python regular expression.
	'''
	# mask words that have already been aligned by copying only unaligned words from list2
	l2 = ['<Assigned>']*len(list2)
	unaligned_s, unaligned_t = get_unaligned_word_indexes(alignment,len(list2))
	for i in unaligned_t: 
		l2[i-1] = list2[i-1]	# since word index starts from '1', use i-1 in lists of word but i in alignment
		
	l1 = mstr.split()
	l1_exp = []
	l2_str = ' '.join(l2)
	for w in l1:
		if w == '<any>':
			l1_exp.append('.+')
		else:
			# escape special characters in regular expression
			for c in RE_SPECIAL_CHARACTERS:
				w = w.replace(c,'\\'+c)
			l1_exp.append('('+w+')')
	
	s = ' '.join(l1_exp)
	#print s
	try:
		p = re.compile(s)
	except:
		print 'Error in re.compile():', s
		exit(1)
	m = p.search(l2_str)
	if m == None:
		return []
	else:
		n = len(m.groups())
		str_idx = [m.span(i)[0] for i in range(1,n+1)]
		#print n, m.groups(), str_idx, l2_str
		return get_word_idx_from_str_idx(l2_str,str_idx)

# phrase_dic (draft. very likely to be updated)
# Each phrase entry has multiple meanings with its list of references
# eg) 'on earth' --> {'target string 1':[('bitext',150)], 'target string 2':[('bitext',11786),('bitext',11947)]}

# phrase_dic (draft. very likely to be updated)
# 	A tree consisting of word nodes
# 	word node is a class whose members are
#			1. name --> word string. eg)'Just', 'reminder',...
#			2. meanings --> dictionary of <target phrase string>:[<reference 1>, ..., <reference n>] key-value pairs
# 			 eg) 'on earth' --> {'target string 1':[('bitext',150)], 'target string 2':[('bitext',11786),('bitext',11947)]}
#			3. branch --> dictionary of <source word>:addresses of children nodes
#		<source/target phrase string>
#				case 1. actual words. eg) 'have in mind', ''(when there is no corresponding word)
#								can be learned directly from bitext instances
#				case 2. actual words + class. eg> 'have <any> in mind', 'have <NP> in mind'
#								can be obtained from tailored example by human agents.
#								can be obtained by generalization of individual instances
#				case 3. constraints. (no specific idea yet)
#		<reference>
#				case 1. ('bitext',line_idx)	
#				case 2. ('tailor example',index)
#				case 3. ('generalization',list of <knowledge source>)
#				case 4. ('rule', priority)
#				case 5. 

class PhraseTree():
	"""
	"""
	def __init__(self,name=None):
		self.name = name
		self.meanings = {}
		self.branch = {}
		#print 'constructor:', self.name, self.meanings, self.branch
	
	def add(self, phrase, target_str, ref):
		"""
		"""
		wlist = phrase[:]	# copy contents not to change the original phrase
		if wlist == []:
			if target_str not in self.meanings:
					self.meanings[target_str] = []
			self.meanings[target_str].append(ref)
		else:
			w = wlist.pop(0)
			if w not in self.branch:
				b = PhraseTree(w)
				self.branch[w] = b
			self.branch[w].add(wlist, target_str, ref)

	def get(self, wlist):
		"""
		"""
		if wlist == []:
			return self	# [] if there is no meaning learned for the phrase (wlist)
		else:
			w = wlist.pop(0)
			if w not in self.branch:
				return None
			else:
				return self.branch[w].get(wlist)

	def show(self, prefix=""):
		"""
		"""
		print prefix+self.name
		for mstr in self.meanings:
			print mstr, self.meanings[mstr]
		for w in self.branch:
			self.branch[w].show(prefix+self.name+" ")

	def get_word_set(self):
		"""
		Return a set of all words included in the dic
		"""
		ws = set([])
		for w in self.branch:
			ws.add(w)
			ws |= self.branch[w].get_word_set()
		return ws
		
			