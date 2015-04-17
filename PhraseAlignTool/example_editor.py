#!/usr/bin/python

# Editor

import wx
import os

class Editor(wx.Frame):
    def __init__(self, parent, id, title):
        wx.Frame.__init__(self, parent, id, title, size=(600, 500))

        # variables
        self.modify = False
        self.last_name_saved = ''
        self.replace = False

        # setting up menubar
        menubar = wx.MenuBar()

        file = wx.Menu()
        new = wx.MenuItem(file, 101, '&New\tCtrl+N', 'Creates a new document')
        new.SetBitmap(wx.Bitmap('icons/stock_new-16.png'))
        file.AppendItem(new)

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
        cut = wx.MenuItem(edit, 106, '&Cut\tCtrl+X', 'Cut the Selection')
        cut.SetBitmap(wx.Bitmap('icons/stock_cut-16.png'))
        edit.AppendItem(cut)

        copy = wx.MenuItem(edit, 107, '&Copy\tCtrl+C', 'Copy the Selection')
        copy.SetBitmap(wx.Bitmap('icons/stock_copy-16.png'))
        edit.AppendItem(copy)

        paste = wx.MenuItem(edit, 108, '&Paste\tCtrl+V', 'Paste text from clipboard')
        paste.SetBitmap(wx.Bitmap('icons/stock_paste-16.png'))
        edit.AppendItem(paste)

        delete = wx.MenuItem(edit, 109, '&Delete', 'Delete the selected text')
        delete.SetBitmap(wx.Bitmap('icons/stock_delete-16.png',))

        edit.AppendItem(delete)
        edit.AppendSeparator()
        edit.Append(110, 'Select &All\tCtrl+A', 'Select the entire text')

        view = wx.Menu()
        view.Append(111, '&Statusbar', 'Show StatusBar')

        help = wx.Menu()
        about = wx.MenuItem(help, 112, '&About\tF1', 'About Editor')
        about.SetBitmap(wx.Bitmap('icons/stock_about-16.png'))
        help.AppendItem(about)

        menubar.Append(file, '&File')
        menubar.Append(edit, '&Edit')
        menubar.Append(view, '&View')
        menubar.Append(help, '&Help')
        self.SetMenuBar(menubar)

        self.Bind(wx.EVT_MENU, self.NewApplication, id=101)
        self.Bind(wx.EVT_MENU, self.OnOpenFile, id=102)
        self.Bind(wx.EVT_MENU, self.OnSaveFile, id=103)
        self.Bind(wx.EVT_MENU, self.OnSaveAsFile, id=104)
        self.Bind(wx.EVT_MENU, self.QuitApplication, id=105)
        self.Bind(wx.EVT_MENU, self.OnCut, id=106)
        self.Bind(wx.EVT_MENU, self.OnCopy, id=107)
        self.Bind(wx.EVT_MENU, self.OnPaste, id=108)
        self.Bind(wx.EVT_MENU, self.OnDelete, id=109)
        self.Bind(wx.EVT_MENU, self.OnSelectAll, id=110)
        self.Bind(wx.EVT_MENU, self.ToggleStatusBar, id=111)
        self.Bind(wx.EVT_MENU, self.OnAbout, id=112)

        # setting up toolbar
        self.toolbar = self.CreateToolBar( wx.TB_HORIZONTAL | wx.NO_BORDER | wx.TB_FLAT | wx.TB_TEXT )
        self.toolbar.AddSimpleTool(801, wx.Bitmap('icons/stock_new.png'), 'New', '')
        self.toolbar.AddSimpleTool(802, wx.Bitmap('icons/stock_open.png'), 'Open', '')
        self.toolbar.AddSimpleTool(803, wx.Bitmap('icons/stock_save.png'), 'Save', '')
        self.toolbar.AddSeparator()

        self.toolbar.AddSimpleTool(804, wx.Bitmap('icons/stock_cut.png'), 'Cut', '')
        self.toolbar.AddSimpleTool(805, wx.Bitmap('icons/stock_copy.png'), 'Copy', '')
        self.toolbar.AddSimpleTool(806, wx.Bitmap('icons/stock_paste.png'), 'Paste', '')
        self.toolbar.AddSeparator()

        self.toolbar.AddSimpleTool(807, wx.Bitmap('icons/stock_exit.png'), 'Exit', '')
        self.toolbar.Realize()

        self.Bind(wx.EVT_TOOL, self.NewApplication, id=801)
        self.Bind(wx.EVT_TOOL, self.OnOpenFile, id=802)
        self.Bind(wx.EVT_TOOL, self.OnSaveFile, id=803)
        self.Bind(wx.EVT_TOOL, self.OnCut, id=804)
        self.Bind(wx.EVT_TOOL, self.OnCopy, id=805)
        self.Bind(wx.EVT_TOOL, self.OnPaste, id=806)
        self.Bind(wx.EVT_TOOL, self.QuitApplication, id=807)

        self.text = wx.TextCtrl(self, 1000, '', size=(-1, -1), style=wx.TE_MULTILINE | wx.TE_PROCESS_ENTER)
        self.text.SetFocus()
        self.text.Bind(wx.EVT_TEXT, self.OnTextChanged, id=1000)
        self.text.Bind(wx.EVT_KEY_DOWN, self.OnKeyDown)

        self.Bind(wx.EVT_CLOSE, self.QuitApplication)

        self.StatusBar()

        self.Centre()
        self.Show(True)

    def NewApplication(self, event):
        editor = Editor(None, -1, 'Editor')
        editor.Centre()
        editor.Show()

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
        wcd = 'All files (*)|*|Editor files (*.ef)|*.ef'
        dir = os.getcwd()
        open_dlg = wx.FileDialog(self, message='Choose a file', defaultDir=dir, defaultFile='',
                        wildcard=wcd, style=wx.OPEN|wx.CHANGE_DIR)
        if open_dlg.ShowModal() == wx.ID_OK:
            path = open_dlg.GetPath()

            try:
                file = open(path, 'r')
                text = file.read()
                file.close()
                if self.text.GetLastPosition():
                    self.text.Clear()
                self.text.WriteText(text)
                self.last_name_saved = path
                self.statusbar.SetStatusText('', 1)
                self.modify = False

            except IOError, error:
                dlg = wx.MessageDialog(self, 'Error opening file\n' + str(error))
                dlg.ShowModal()

            except UnicodeDecodeError, error:
                dlg = wx.MessageDialog(self, 'Error opening file\n' + str(error))
                dlg.ShowModal()

        open_dlg.Destroy()

    def OnSaveFile(self, event):
        if self.last_name_saved:

            try:
                file = open(self.last_name_saved, 'w')
                text = self.text.GetValue()
                file.write(text)
                file.close()
                self.statusbar.SetStatusText(os.path.basename(self.last_name_saved) + ' saved', 0)
                self.modify = False
                self.statusbar.SetStatusText('', 1)

            except IOError, error:
                dlg = wx.MessageDialog(self, 'Error saving file\n' + str(error))
                dlg.ShowModal()
        else:
            self.OnSaveAsFile(event)

    def OnSaveAsFile(self, event):
        wcd='All files(*)|*|Editor files (*.ef)|*.ef|'
        dir = os.getcwd()
        save_dlg = wx.FileDialog(self, message='Save file as...', defaultDir=dir, defaultFile='',
                        wildcard=wcd, style=wx.SAVE | wx.OVERWRITE_PROMPT)
        if save_dlg.ShowModal() == wx.ID_OK:
            path = save_dlg.GetPath()

            try:
                file = open(path, 'w')
                text = self.text.GetValue()
                file.write(text)
                file.close()
                self.last_name_saved = os.path.basename(path)
                self.statusbar.SetStatusText(self.last_name_saved + ' saved', 0)
                self.modify = False
                self.statusbar.SetStatusText('', 1)

            except IOError, error:
                dlg = wx.MessageDialog(self, 'Error saving file\n' + str(error))
                dlg.ShowModal()
        save_dlg.Destroy()

    def OnCut(self, event):
        self.text.Cut()

    def OnCopy(self, event):
        self.text.Copy()

    def OnPaste(self, event):
        self.text.Paste()

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

    def OnDelete(self, event):
        frm, to = self.text.GetSelection()
        self.text.Remove(frm, to)

    def OnSelectAll(self, event):
        self.text.SelectAll()

    def OnTextChanged(self, event):
        self.modify = True
        self.statusbar.SetStatusText(' modified', 1)
        event.Skip()

    def OnKeyDown(self, event):
        keycode = event.GetKeyCode()
        if keycode == wx.WXK_INSERT:
            if not self.replace:
                self.statusbar.SetStatusText('INS', 2)
                self.replace = True
            else:
                self.statusbar.SetStatusText('', 2)
                self.replace = False
        event.Skip()

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
        dlg = wx.MessageDialog(self, '\tEditor\t\n Another Tutorial\njan bodnar 2005-2006',
                                'About Editor', wx.OK | wx.ICON_INFORMATION)
        dlg.ShowModal()
        dlg.Destroy()

app = wx.App()
Editor(None, -1, 'Editor')
app.MainLoop()