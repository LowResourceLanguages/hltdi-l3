#!/usr/bin/python
# -*- coding: utf-8 -*-


# PhraseAlignment
import wx 
import os
import utils
import cPickle

	
def StringLen(s):
	'''
	wxPython counts characters not bytes to represent position (points) in texts
	This function assumes all characters that are not single byte characters are double byte.
	So it would be good to find more general function for this.
	'''
	idx = 0
	length = 0
	while idx < len(s):
		if ord(s[idx]) < 0x80:	# single byte character
			idx += 1
		else:							# double byte character, maybe incorrect for some character but true for Korean
			idx += 2
		length = length + 1
	return length
	
class TextWordCtrl(wx.TextCtrl):
	'''
	'''
	def SetValue(self,text):	
		# keep a word list to manipulate easily
		self.wlist = text.split()

		self.Clear()
		self.WriteText(" ".join(self.wlist) + "\n")	# remove potential double space and convert tab into space.
		
		self.w_end_points = []
		self.w_selected = []
		cur_pos = 0
		for w in self.wlist:
			cur_pos = cur_pos + StringLen(w)
			self.w_end_points.append(cur_pos)
			self.w_selected.append(False)
			cur_pos = cur_pos + 1	# space
		
		self.widx_at_mouse_pointer = None
	
#	def get_word_at(self, cidx_pos):
#		'''
#		Given a character postion,
#		returns the word, widx, the word's range(starting position and end position)
#		'''
#		pre_cidx = -1
#		for widx, cidx in enumerate(self.w_end_points):
#			if cidx >= cidx_pos:
#				return widx, pre_cidx+1, cidx)
#			pre_cidx = cidx
#		return (None,None,cidx_pos,cidx_pos)

	def get_word_at(self, cidx_pos):
		'''
		Given a character postion,
		returns the word index over it.
		'''
		pre_cidx = -1
		for widx, cidx in enumerate(self.w_end_points):
			if cidx >= cidx_pos:
				return widx
			pre_cidx = cidx
		return None

	def get_word_range(self, widx):
		'''
		Given a word index,
		returns the word's range(starting position and end position)
		'''
		if widx == None:
			return 0,0
			
		if widx == 0:
			start_cidx = 0
		else:
			start_cidx = self.w_end_points[widx-1]+1

		return start_cidx, self.w_end_points[widx]
		
	def toggle_selection(self, widx_list=[]):
		'''
		Takes either list of word index or character index
		and toggle the selection while painting accordingly.
		'''	
		for widx in widx_list:
			# get the range of the word
			f,t = self.get_word_range(widx)

			if self.w_selected[widx]:
				self.w_selected[widx] = False
				self.SetStyle(f,t, self.parent.style_default_color)
			else:
				self.w_selected[widx] = True
				self.SetStyle(f,t, wx.TextAttr("white", "blue"))
				

	def set_selection(self, widx_list="all", choice=True):
		'''
		Takes a list of word indexes
		and set the selection while painting accordingly
		'''
		if widx_list == "all":
			self.w_selected = [choice for k in self.w_selected]
			if choice:
				for widx in range(len(self.w_end_points)):
					f,t = self.get_word_range(widx)
					self.SetStyle(f,t, wx.TextAttr("white", "blue"))
			else:
				self.SetStyle(0,self.GetLastPosition(),self.parent.style_default_color)
		else:				# select some words
			for widx in widx_list:
				f,t = self.get_word_range(widx)
				if choice:
					self.w_selected[widx] = True
					self.SetStyle(f,t, wx.TextAttr("white", "blue"))
				else:
					self.w_selected[widx] = False
					self.SetStyle(f,t, self.parent.style_default)
		
	def set_style(self, widx_list, style, choice=True):
		'''
		Takes a list of word indexes
		and set the style
		'''
		if widx_list == "all":	# highlight all/none
			if choice:
				for widx in range(len(self.w_end_points)):
					f,t = self.get_word_range(widx)
					self.SetStyle(f,t,style)
			else:
				self.SetStyle(0,self.GetLastPosition(),self.parent.style_default)
		else:				# highlight a word
			for widx in widx_list:
				f,t = self.get_word_range(widx)
				if choice:
					self.SetStyle(f,t, style)
				else:
					self.SetStyle(f,t, self.parent.style_default)
			
			
def word_to_group(w_idx, phrases):
	"""
	returns a phrase (a list of word indexes) where the word belong.
	phrase is a list of word indexes. eg) [3,8]
	phrases is a list of phrase. eg) [[0], [1], [3, 8], [4], [2, 6, 7]]
	"""
	if w_idx == None:
		return [], None
	else:
		w_idx = w_idx + 1	# because the indexes for real words in phrases start from 1
		
	for p_idx, p in enumerate(phrases):
		if w_idx in p:
			return p, p_idx
	return [w_idx], None
		
def load_texts_align(filename):
	texts1 = []
	texts2 = []
	alignments = []

	f = open(filename, 'r')
	line_idx = 0
	while True:
		try:
			line = f.readline()
			if len(line) != 0:	# there is a empty line at the end
				texts1.append(line)
			line = f.readline()
			if len(line) != 0:
				texts2.append(line)
			alignments.append(cPickle.load(f))
			line_idx = line_idx + 1
		except EOFError:
			break
	f.close()
	return (texts1,texts2,alignments)
	
class PhraseAlignment(wx.Frame):
	'''
	Main Class for this application
	'''
	def __init__(self, parent, id, title):
		wx.Frame.__init__(self, parent, id, title, size=(1000, 400))

		# variables
		self.modify = False
		self.last_name_saved = ''
		self.replace = False

		# setting up menubar
		menubar = wx.MenuBar()

		file = wx.Menu()

		open = wx.MenuItem(file, 102, '&Open\tCtrl+O', 'Open an existing file')
		open.SetBitmap(wx.Bitmap('icons/stock_open-16.png'))
		file.AppendItem(open)
		file.AppendSeparator()

		save = wx.MenuItem(file, 103, '&Save\tCtrl+S', 'Save the file')
		save.SetBitmap(wx.Bitmap('icons/stock_save-16.png'))
		file.AppendItem(save)

		saveas = wx.MenuItem(file, 104, 'Save &As...\tShift+Ctrl+S', 'Save the file with a different name')
		saveas.SetBitmap(wx.Bitmap('icons/stock_save_as-16.png'))
		file.AppendItem(saveas)
		file.AppendSeparator()

		quit = wx.MenuItem(file, 105, '&Quit\tCtrl+Q', 'Quit the Application')
		quit.SetBitmap(wx.Bitmap('icons/stock_exit-16.png'))
		file.AppendItem(quit)

		edit = wx.Menu()
		edit.Append(109, '&GoTo\tCtrl+G', 'Jump to a sentence')
		edit.Append(110, 'Select &All\tCtrl+A', 'Select the entire text')

		view = wx.Menu()
		view.Append(111, '&Statusbar', 'Show StatusBar')

		help = wx.Menu()
		about = wx.MenuItem(help, 112, '&About\tF1', 'About PhraseAlignment')
		about.SetBitmap(wx.Bitmap('icons/stock_about-16.png'))
		help.AppendItem(about)

		menubar.Append(file, '&File')
		menubar.Append(edit, '&Edit')
		menubar.Append(view, '&View')
		menubar.Append(help, '&Help')
		self.SetMenuBar(menubar)

		self.Bind(wx.EVT_MENU, self.OnOpenFile, id=102)
		self.Bind(wx.EVT_MENU, self.OnSaveFile, id=103)
		self.Bind(wx.EVT_MENU, self.OnSaveAsFile, id=104)
		self.Bind(wx.EVT_MENU, self.QuitApplication, id=105)
		self.Bind(wx.EVT_MENU, self.OnGoToLineRequest, id=109)
		self.Bind(wx.EVT_MENU, self.OnSelectAll, id=110)
		self.Bind(wx.EVT_MENU, self.ToggleStatusBar, id=111)
		self.Bind(wx.EVT_MENU, self.OnAbout, id=112)

		# setting up toolbar
		self.toolbar = self.CreateToolBar( wx.TB_HORIZONTAL | wx.NO_BORDER | wx.TB_FLAT | wx.TB_TEXT )
		self.toolbar.AddSimpleTool(802, wx.Bitmap('icons/stock_open.png'), 'Open', '')
		self.toolbar.AddSimpleTool(803, wx.Bitmap('icons/stock_save.png'), 'Save', '')
		self.toolbar.AddSeparator()
		self.toolbar.AddSimpleTool(804, wx.Bitmap('icons/stock_select_all.png'), 'Select All', '')
		self.toolbar.AddSeparator()
		self.toolbar.AddSimpleTool(805, wx.Bitmap('icons/stock_arrow_left.png'), 'Previous Sentence', '')
		self.toolbar.AddSimpleTool(806, wx.Bitmap('icons/stock_arrow_right.png'), 'Next Sentence', '')
		self.toolbar.AddSeparator()
		self.toolbar.AddSimpleTool(807, wx.Bitmap('icons/stock_font_size_up.png'), 'Font Size Up', '')
		self.toolbar.AddSimpleTool(808, wx.Bitmap('icons/stock_font_size_down.png'), 'Font Size Down', '')

		self.toolbar.Realize()

		self.Bind(wx.EVT_TOOL, self.OnOpenFile, id=802)
		self.Bind(wx.EVT_TOOL, self.OnSaveFile, id=803)
		self.Bind(wx.EVT_TOOL, self.OnSelectAll, id=804)
		self.Bind(wx.EVT_TOOL, self.OnPrevSentence, id=805)
		self.Bind(wx.EVT_TOOL, self.OnNextSentence, id=806)
		self.Bind(wx.EVT_TOOL, self.OnFontUp, id=807)
		self.Bind(wx.EVT_TOOL, self.OnFontDown, id=808)

		vbox = wx.BoxSizer(wx.VERTICAL)
		hbox1 = wx.BoxSizer(wx.HORIZONTAL)
		hbox2 = wx.BoxSizer(wx.HORIZONTAL)
		
		self.textc1 = TextWordCtrl(self, 1000, '', style=wx.TE_MULTILINE | wx.TE_RICH2)
		self.textc2 = TextWordCtrl(self, 1001, '', style=wx.TE_MULTILINE | wx.TE_RICH2 )
		self.textc1.parent = self
		self.textc2.parent = self
		self.textc1.SetEditable(False)
		self.textc2.SetEditable(False)
		self.textc1.SetCursor(wx.StockCursor(wx.CURSOR_ARROW))
		self.textc2.SetCursor(wx.StockCursor(wx.CURSOR_ARROW))
		self.textc1.Bind(wx.EVT_KEY_DOWN, self.OnKeyDown)
		self.textc2.Bind(wx.EVT_KEY_DOWN, self.OnKeyDown)

		
		self.font = self.textc1.GetFont()
		self.font_bold = wx.Font(self.font.GetPointSize(),self.font.GetFamily(),self.font.GetStyle(),wx.BOLD)
		self.font_bold_underlined = wx.Font(self.font.GetPointSize(),self.font.GetFamily(),self.font.GetStyle(),wx.BOLD,True)

		self.style_default = wx.TextAttr("black","white",self.font)
		self.style_default_color = wx.TextAttr("black","white")
		self.style_highlight = wx.TextAttr("black", "yellow")
		self.style_bold = wx.TextAttr("black", "white",self.font_bold)
		self.style_bold_underlined = wx.TextAttr("black", "white",self.font_bold_underlined)
		
		hbox1.Add(self.textc1, 1, wx.EXPAND, 0)
		hbox1.Add(self.textc2, 1, wx.EXPAND, 0)
		
		hbox2.Add(wx.Button(self, 101, label='Clear Align', size=(120, 40)), 0, wx.CENTER, 5)
		hbox2.Add(wx.Button(self, 102, label='Align', size=(120, 40)), 0, wx.CENTER, 5)
		hbox2.Add(wx.Button(self, 103, label='Null Align', size=(120, 40)), 0, wx.CENTER, 5)
		vbox.Add(hbox1, 1, wx.EXPAND, 0)
		vbox.Add(hbox2, 0, wx.ALIGN_CENTER|wx.TOP, 5)
		self.Bind(wx.EVT_BUTTON, self.OnClearAlign, id=101)
		self.Bind(wx.EVT_BUTTON, self.OnAlign, id=102)
		self.Bind(wx.EVT_BUTTON, self.OnNullAlign, id=103)

		self.SetSizer(vbox)
				
		self.Bind(wx.EVT_CLOSE, self.QuitApplication)

		self.StatusBar()

		self.Centre()
		self.Show(True)

	def DoNothing(self, event):
		'''
		to prevent original action of TextCtrl
		'''
		pass

	def MarkAignedWords(self):
		'''
		Make the aligned words stand out with bold font
		'''
		aligned_w_idxs1 = utils.get_aligned_widx(self.phrases1)
		aligned_w_idxs2 = utils.get_aligned_widx(self.phrases2)
		p1_null_aligned, p2_null_aligned = utils.get_null_aligned_widx(self.phrases1,self.phrases2)
		#print aligned_w_idxs1,aligned_w_idxs2, self.phrases1, self.phrases2
		
		widxs1_aligned_to_words = list(set(aligned_w_idxs1)-set(p1_null_aligned)-set([0]))
		self.textc1.SetStyle(0,self.textc1.GetLastPosition(),self.style_default)
		self.textc1.set_style([i-1 for i in widxs1_aligned_to_words],self.style_bold)
		self.textc1.set_style([i-1 for i in p1_null_aligned],self.style_bold_underlined)

		widxs2_aligned_to_words = list(set(aligned_w_idxs2)-set(p2_null_aligned)-set([0]))
		self.textc2.SetStyle(0,self.textc2.GetLastPosition(),self.style_default)
		self.textc2.set_style([i-1 for i in widxs2_aligned_to_words],self.style_bold)
		self.textc2.set_style([i-1 for i in p2_null_aligned],self.style_bold_underlined)
		
	def ClearSelections(self):
		'''
		Reset word selections of both texts and reset their style
		'''		
		self.textc1.set_selection("all",False)
		self.textc2.set_selection("all",False)
		
	def OnAlign(self, event):
		'''
		With selection from both sides, this does the realignment
		'''
		# if we don't have a selection on BOTH side, just return
		if True not in self.textc1.w_selected or True not in self.textc2.w_selected:	
			return
		p1 = [i+1 for i,v in enumerate(self.textc1.w_selected) if self.textc1.w_selected[i] ]
		p2 = [i+1 for i,v in enumerate(self.textc2.w_selected) if self.textc2.w_selected[i] ]
		utils.realign(self.phrases1,self.phrases2,p1,p2)
		print p1, p2, "have been aligned"
		#print self.textc1.w_selected

		self.ClearSelections()
		self.MarkAignedWords()

		self.modify = True
		self.statusbar.SetStatusText(' modified', 1)

			
	def OnClearAlign(self, event):
		'''
		Clear the alignment of the selected words. It doesn't matter whether the selection is from one side or both side
		'''
		# if we don't have any selection on either side, just return
		if True not in self.textc1.w_selected and True not in self.textc2.w_selected:	
			return
		p1 = [i+1 for i,v in enumerate(self.textc1.w_selected) if self.textc1.w_selected[i] ]
		p2 = [i+1 for i,v in enumerate(self.textc2.w_selected) if self.textc2.w_selected[i] ]
		utils.clear_align(self.phrases1,self.phrases2,p1,p2)
		print "The alignments of", p1, p2, "have been Cleared "

		self.ClearSelections()
		self.MarkAignedWords()
		self.modify = True
		self.statusbar.SetStatusText(' modified', 1)

	def OnNullAlign(self, event):
		'''
		Align the selected words to NULL
		'''
		# if we don't have any selection on either side, just return
		if True not in self.textc1.w_selected and True not in self.textc2.w_selected:	
			return
		p1 = [i+1 for i,v in enumerate(self.textc1.w_selected) if self.textc1.w_selected[i] ]
		p2 = [i+1 for i,v in enumerate(self.textc2.w_selected) if self.textc2.w_selected[i] ]
		utils.null_align(self.phrases1,self.phrases2,p1,p2)
		print p1, p2, "have been Aligned to <NULL>"

		self.ClearSelections()
		self.MarkAignedWords()
		self.modify = True
		self.statusbar.SetStatusText(' modified', 1)

	def SetFontSize(self, font_size):
		'''
		'''
		font = self.textc1.GetFont()
		self.font = wx.Font(font_size, font.GetFamily(), font.GetStyle(), font.GetWeight())
		self.textc1.SetFont(self.font)
		self.textc2.SetFont(self.font)
		
		self.font_bold = wx.Font(font_size, font.GetFamily(), font.GetStyle(), wx.BOLD)
		self.font_bold_underlined = wx.Font(font_size, font.GetFamily(), font.GetStyle(), wx.BOLD, True)

		self.style_default = wx.TextAttr("black","white",self.font)
		self.style_bold = wx.TextAttr("black", "white",self.font_bold)
		self.style_bold_underlined = wx.TextAttr("black", "white",self.font_bold_underlined)
		
		self.MarkAignedWords()

	def OnFontUp(self, event):
		'''
		'''
		font_size = self.textc1.GetFont().GetPointSize()
		#print font_size, "->", font_size+2
		self.SetFontSize(font_size+2)

	def OnFontDown(self, event):
		'''
		'''
		font_size = self.textc1.GetFont().GetPointSize()
		#print font_size, "->" , font_size-2
		self.SetFontSize(font_size-2)
				
	def GoToSentence(self, new_line_num):
		'''
		'''
		if new_line_num <= 0:
			new_line_num = 0
		elif new_line_num >= len(self.texts1)-1:
			new_line_num = len(self.texts1)-1

		if new_line_num == self.line_num:
			return
			
		# move the current pairwise alignment information to the original alignment variablle.
		self.alignments[self.line_num] = utils.pairs2alignment(self.phrases1,self.phrases2,len(self.textc1.wlist)+1)

		# change line number
		self.line_num = new_line_num
		# load texts and alignment with new line number
		self.textc1.SetValue(self.texts1[self.line_num])
		self.textc2.SetValue(self.texts2[self.line_num])
		self.phrases1, self.phrases2 = utils.get_aligned_pairs2(self.alignments[self.line_num])

		self.textc1.SetFont(self.font)
		self.textc2.SetFont(self.font)
		
		self.MarkAignedWords()
		self.statusbar.SetStatusText('Sentence %d/%d' % (self.line_num+1,len(self.texts1)), 2)
		

	def OnPrevSentence(self, event):
		'''
		'''
		self.GoToSentence(self.line_num-1)
		
	def OnNextSentence(self, event):
		'''
		'''
		self.GoToSentence(self.line_num+1)
		
	def OnMouseMotion(self, event):
		'''
		'''
		if event.GetId() == 1000:
			textc = self.textc1
			phrases = self.phrases1
			other_textc = self.textc2
			other_phrases = self.phrases2
		else:
			textc = self.textc2
			phrases = self.phrases2
			other_textc = self.textc1
			other_phrases = self.phrases1
		
		# get pixel position
		pix_pos = event.GetPosition()
		# get character position(point) from the given pixel position
		(row, col) = textc.HitTestPos(pix_pos)
		
		# get word index
		widx = textc.get_word_at(col)
		
		# Do this action only when the mouse moves over a different word and there is no selection on either side.
		if textc.widx_at_mouse_pointer != widx and True not in textc.w_selected and True not in other_textc.w_selected:
			# update and remember word index at mouse pointer
			textc.widx_at_mouse_pointer = widx
			# get the group (phrase) that the word belongs to
			# the phrase can have just one word (the widx) in case the word is aligned alone
			# In case the word is not aligned yet, ph=[widx], ph_idx=None.
			# In case widx=None when the mouse is over none of the words, ph=[], ph_idx = None
			ph, ph_idx = word_to_group(widx,phrases)
			
			# color on the side where the mouse is
			textc.SetStyle(0,textc.GetLastPosition(), self.style_default_color)
			textc.set_style([i-1 for i in ph],self.style_highlight)	# note that widx start from 0 while alignment word indexes start from 1 because 0 is reserved for NULL
			
			# color on the other side 
			other_textc.SetStyle(0,other_textc.GetLastPosition(), self.style_default_color)
			if ph_idx != None and other_phrases[ph_idx] != [0]:
				other_textc.set_style([i-1 for i in other_phrases[ph_idx]],self.style_highlight)	# note that widx start from 0 while alignment word indexes start from 1 because 0 is reserved for NULL
			
			
	def OnWordSelection(self, event):
		'''
		Selection is made by mouse click.
		'''
		if event.GetId() == 1000:
			textc = self.textc1
		else:
			textc = self.textc2
			
		insert_p = textc.GetInsertionPoint()
		#print event.GetId(), insert_p, text.w_end_points
		
		widx = textc.get_word_at(insert_p)
		f,t = textc.get_word_range(widx)
		if widx != None:	# selected a word
			textc.toggle_selection([widx])
		else:	# clicked on empty area
			textc.set_selection("all",False)
		
		# propagate the event. Otherwise original behavior of TextCtrl make things strange
		event.Skip()
		
	def OnGoToLineRequest(self, event):
		dlg = wx.TextEntryDialog(self, 'Enter a line number (1-%d)' % len(self.texts1), '','%d' % (self.line_num+1), wx.OK | wx.OK_DEFAULT | wx.CANCEL)
		val = dlg.ShowModal()
		if val == wx.ID_OK:
			in_str = dlg.GetValue()
			try:
				ln = int(in_str)
			except:
				pass
			else:
				self.GoToSentence(ln-1)
				
		dlg.Destroy()
		
	def OnOpenFile(self, event):
		file_name = os.path.basename(self.last_name_saved)
		if self.modify:
			dlg = wx.MessageDialog(self, 'Save changes?', '', wx.YES_NO | wx.YES_DEFAULT | wx.CANCEL |
						wx.ICON_QUESTION)
			val = dlg.ShowModal()
			if val == wx.ID_YES:
				self.OnSaveFile(event)
				self.DoOpenFile()
			elif val == wx.ID_CANCEL:
				dlg.Destroy()
			else:
				self.DoOpenFile()
		else:
			self.DoOpenFile()

	def DoOpenFile(self):
		wcd = 'PhraseAlignment files (*.aln)|*.aln'
		dir = os.getcwd()
		open_dlg = wx.FileDialog(self, message='Choose a file', defaultDir=dir, defaultFile='',
						wildcard=wcd, style=wx.OPEN|wx.CHANGE_DIR)
		if open_dlg.ShowModal() == wx.ID_OK:
			path = open_dlg.GetPath()

			try:
				self.line_num = 0
				(self.texts1,self.texts2,self.alignments) = load_texts_align(path)
				#print len(self.texts1),len(self.texts2),len(self.alignments)
				self.textc1.SetValue(self.texts1[self.line_num])
				self.textc2.SetValue(self.texts2[self.line_num])
				self.phrases1, self.phrases2 = utils.get_aligned_pairs2(self.alignments[self.line_num])
				self.last_name_saved = path
				self.statusbar.SetStatusText('', 1)
				self.modify = False

				self.textc1.Bind(wx.EVT_LEFT_UP , self.OnWordSelection)
				self.textc2.Bind(wx.EVT_LEFT_UP , self.OnWordSelection)
				self.textc1.Bind(wx.EVT_LEFT_DCLICK , self.DoNothing)	
				self.textc2.Bind(wx.EVT_LEFT_DCLICK , self.DoNothing)
				self.textc1.Bind(wx.EVT_MOTION , self.OnMouseMotion)
				self.textc2.Bind(wx.EVT_MOTION , self.OnMouseMotion)

				self.MarkAignedWords()
				self.statusbar.SetStatusText('Sentence %d/%d' % (self.line_num+1,len(self.texts1)), 2)

			except IOError, error:
				dlg = wx.MessageDialog(self, 'Error opening file\n' + str(error))
				dlg.ShowModal()

			except UnicodeDecodeError, error:
				dlg = wx.MessageDialog(self, 'Error opening file\n' + str(error))
				dlg.ShowModal()

		open_dlg.Destroy()

	def OnSaveFile(self, event):
		if self.last_name_saved:
			# move the current pairwise alignment information to the original alignment variablle.
			self.alignments[self.line_num] = utils.pairs2alignment(self.phrases1,self.phrases2,len(self.textc1.wlist)+1) 
			try:
				fout = open(self.last_name_saved, 'w')
				for i, t1 in enumerate(self.texts1):
					fout.write(t1)
					fout.write(self.texts2[i])
					cPickle.dump(self.alignments[i],fout)
				fout.close()
				self.statusbar.SetStatusText(os.path.basename(self.last_name_saved) + ' saved', 0)
				self.modify = False
				self.statusbar.SetStatusText('', 1)

			except IOError, error:
				dlg = wx.MessageDialog(self, 'Error saving file\n' + str(error))
				dlg.ShowModal()
		else:
			self.OnSaveAsFile(event)

	def OnSaveAsFile(self, event):
		wcd='PhraseAlignment files (*.aln)|*.aln'
		dir = os.getcwd()
		save_dlg = wx.FileDialog(self, message='Save file as...', defaultDir=dir, defaultFile='',
						wildcard=wcd, style=wx.SAVE | wx.OVERWRITE_PROMPT)
		if save_dlg.ShowModal() == wx.ID_OK:
			path = save_dlg.GetPath()

			# move the current pairwise alignment information to the original alignment variablle.
			self.alignments[self.line_num] = utils.pairs2alignment(self.phrases1,self.phrases2,len(self.textc1.wlist)+1) 
			try:
				fout = open(path, 'w')
				for i, t1 in enumerate(self.texts1):
					fout.write(t1)
					fout.write(self.texts2[i])
					cPickle.dump(self.alignments[i],fout)
				fout.close()
				
				self.last_name_saved = os.path.basename(path)
				self.statusbar.SetStatusText(self.last_name_saved + ' saved', 0)
				self.modify = False
				self.statusbar.SetStatusText('', 1)

			except IOError, error:
				dlg = wx.MessageDialog(self, 'Error saving file\n' + str(error))
				dlg.ShowModal()
		save_dlg.Destroy()

	def QuitApplication(self, event):
		if self.modify:
			dlg = wx.MessageDialog(self, 'Save before Exit?', '', wx.YES_NO | wx.YES_DEFAULT |
						wx.CANCEL | wx.ICON_QUESTION)
			val = dlg.ShowModal()
			if val == wx.ID_YES:
				self.OnSaveFile(event)
				if not self.modify:
					wx.Exit()
			elif val == wx.ID_CANCEL:
				dlg.Destroy()
			else:
				self.Destroy()
		else:
			self.Destroy()

	def OnSelectAll(self, event):
		self.textc1.set_selection("all",True)
		self.textc2.set_selection("all",True)

	def OnKeyDown(self, event):
		keycode = event.GetKeyCode()
		#print keycode
		#if keycode == wx.WXK_INSERT:
		if keycode == ord('A'):
			self.OnAlign(None)
		elif keycode == ord('F') or keycode == wx.WXK_RIGHT:
			self.OnNextSentence(None)
		elif keycode == ord('D') or keycode == wx.WXK_LEFT:
			self.OnPrevSentence(None)

	def ToggleStatusBar(self, event):
		if self.statusbar.IsShown():
			self.statusbar.Hide()
		else:
			self.statusbar.Show()

	def StatusBar(self):
		self.statusbar = self.CreateStatusBar()
		self.statusbar.SetFieldsCount(3)
		self.statusbar.SetStatusWidths([-5, -2, -1])

	def OnAbout(self, event):
		dlg = wx.MessageDialog(self, 'PhraseAlignment\nIkhyun Park\nikpark@indiana.edu\n2011',
								'About PhraseAlignment', wx.OK | wx.ICON_INFORMATION)
		dlg.ShowModal()
		dlg.Destroy()

app = wx.App()
PhraseAlignment(None, -1, 'Phrase Alignment Tool')
app.MainLoop()