from tkinter import *
# from tkinter.font import *
import math

CW = 800
CH = 600

SENT_H = 50
Y_OFF = 10
X_OFF = 20
DIM_GAP = 10
DIM_OFF = 70

class Multigraph(Canvas):
    """Canvas for displaying the multigraph for a sentence."""

    node_rad = 3

    def __init__(self, parent, width=CW, height=CH, nnodes=9,
                 dims=['En LP', 'En ID', 'Sem', 'Am ID', 'Am LP'],
#                 dims=['En ID', 'Sem', 'Am ID'],
                 translation=True):
        Canvas.__init__(self, parent, width=width, height=height)
#        self.draw_arrow(10, 50, 40, 20, 60, 10, 80, 10, 100, 20, 130, 50)
        self.parent = parent
        self.width = width
        self.height = height
        self.translation = translation
        self.dim_labels = dims
        # Calculate the width, height, and positions of the dimensions
        self.get_dim_dims()
        # Figure node coordinates
        node_dist = self.dim_width / nnodes
        node_offsets = [node_dist * (i + .5) for i in range(nnodes)]
##        for index, off in enumerate(node_offsets):
##            dim1.make_node(index, off,
##                           filled = (index % 3 != 0),
##                           eos = (index == nnodes - 1))
##            dim2.make_node(index, off,
##                           eos = (index == nnodes - 1))
##            dim3.make_node(index, off,
##                           eos = (index == nnodes - 1))
        self.dims = []
        for label, x, y in zip(dims, self.dim_x, self.dim_y):
            d = Dimension(self, coords=(x, y), label=label,
                          width=self.dim_width, height=self.dim_height)
            self.dims.append(d)
            d.draw()
            for index, off in enumerate(node_offsets):
                d.make_node(index, off, eos = (index == nnodes - 1))

        self.dims[0].make_arc(8, 0, tp='root')
        self.dims[0].make_arc(1, 3, tp='sbj')
        self.dims[0].make_arc(7, 4, tp='mod')
        self.dims[0].make_arc(3, 4, tp='rel')
        self.dims[0].make_arc(0, 5, tp='obj')
##        dim1.make_arc(8, 1, tp='sbj')
##        dim1.make_arc(1, 7, tp='obj', color='gray')
##        self.dims = [dim1, dim2, dim3]
        self.node_connections = []
        self.connect_nodes()

        self.sentences = []
        in_sent = Sentence(self, ['the', 'woman', 'cleaned', 'the', 'house', 'in', 'the', 'city', '.'],
                           coords=(self.dim_x[0], 580),
                           width=self.dim_width)
        in_sent.draw()
        self.sentences.append(in_sent)
##        self.connect_sent(in_sent, dim1)
        out_sent = Sentence(self, ["እከተማዋ", "ያለውን", "ቤት", "ሴቷ", "ጠረገችው", "።"],
                            node_indices=[7, 5, 4, 1, 2, 8],
                            coords=(self.dim_x[-1], 20),
                            width=self.dim_width)
        out_sent.draw()
        self.sentences.append(out_sent)
##        self.connect_sent(out_sent, dim3)

#        self.draw_arrow(10, 80, 80, 20, 150, 80)
#        self.draw_arc_label((80, 50), 'sbj')

    def get_dim_dims(self):
        # Calculate the width, height, and positions of the dimensions
        w = self.width - 2 * X_OFF
        h = self.height - SENT_H - 2 * Y_OFF
        if self.translation:
            h -= SENT_H
        ndims = len(self.dim_labels)
        # Width of dimensions
        x_off = DIM_OFF * (ndims - 1)
        w_sum = w - x_off
        w1 = w_sum  # / ndims
#        print('Dim w {}'.format(w1))
        # Height of dimensions
        y_off = DIM_GAP * (ndims - 1)
        h_sum = h - y_off
        h1 = h_sum / ndims
#        print('Dim h {}'.format(h1))
        # Figure out the x coordinates of dimensions
        x_coords = []
        x = X_OFF
        for d in self.dim_labels:
            x_coords.append(x)
            x += DIM_OFF
        # Figure out the y coordinates of dimensions
        y_coords = []
        y = self.height - SENT_H - Y_OFF - h1
        for d in self.dim_labels:
            y_coords.append(y)
            y -= DIM_GAP + h1
        self.dim_width = w1
        self.dim_height = h1
        self.dim_x = x_coords
        self.dim_y = y_coords

    def connect_nodes(self):
        for index, dim in enumerate(self.dims[:-1]):
            next_dim = self.dims[index + 1]
            for node1, node2 in zip(dim.nodes, next_dim.nodes):
                cx1, cy1 = node1.center
                cx2, cy2 = node2.center
                c_id = self.create_line(cx1, cy1, cx2, cy2,
                                        dash=(3,3))
                self.node_connections.append(c_id)

    def connect_sent(self, sent, dim):
        dim_nodes = dim.nodes
        nodes = [dim_nodes[index] for index in sent.node_indices]
        for word, node in zip(sent.ids, nodes):
            wx, wy = self.coords(word)
            nx, ny = node.center
            self.create_line(wx, wy, nx, ny, dash=(1, 3))

class Dimension:
    """Graphical representation of an XDG dimension."""

    Y_OFF = 15

    def __init__(self, canvas, coords=(50, 50), width=500,
                 height=160, color='black', label='ID'):
        self.canvas = canvas
        self.color = color
        self.label = label
        self.coords = coords
        self.width = width
        self.height = height
        self.h2w = self.height / self.width
#        print('h2w {}'.format(self.h2w))
        self.nodes = []

    def draw(self):
        c0, c1 = self.coords
        self.id = self.canvas.create_rectangle(c0, c1, c0 + self.width, c1 + self.height)
        if self.label:
            self.make_label()

    def make_label(self):
        x = self.coords[0] + 25
        y = self.coords[1] + 10
        self.label_id = self.canvas.create_text(x, y, text=self.label,
                                                font = ("Helvetica", "14"))

    def make_node(self, index, offset, eos=False,
                  filled=True):
        node = Node(self.canvas,
                    center=(self.coords[0] + offset,
                            self.coords[1] + self.height - self.Y_OFF),
                    filled=filled,
                    index=index,
                    eos=eos)
        self.nodes.append(node)
        node.draw()

    def make_arc(self, i_head, i_dep, tp='', color='black'):
        head = self.nodes[i_head]
        dep = self.nodes[i_dep]
        right = i_dep > i_head
        start = head.get_upper_right() if right else head.get_upper_left()
        head.source
        end = dep.top
#        dep.get_upper_left() if right else dep.get_upper_right()
        arc = Arc(self.canvas, head, dep, start=start, end=end,
                  tp=tp, color=color, h2w=1.6 * self.h2w)
        arc.draw()

class Node:
    """Graphical representation of an XDG node."""

    R = 7
    CORNER_OFF = 7 * math.cos(math.radians(45))

    def __init__(self, canvas, center=(100, 100), index=0, filled=True, eos=False):
        self.canvas = canvas
        self.center = center
        self.filled = filled
        self.index = index
        self.eos = eos
        self.arcs = []
        # upper-left, upper-right,
        # lower-right, lower-left
        cx, cy = self.center
        rad = 2 if self.eos else self.CORNER_OFF
        self.corners = [(cx-rad, cy-rad),
                        (cx+rad , cy-rad ),
                        (cx+rad , cy+rad ),
                        (cx-rad , cy+rad )]
        self.top = (cx, cy-rad)
        self.source = center if self.eos else (cx, cy-rad)

    def get_upper_left(self):
        return self.corners[0]

    def get_upper_right(self):
        return self.corners[1]

    def draw(self):
        x1, y1 = self.corners[0]
        x2, y2 = self.corners[2]
        if self.eos:
            self.id = self.canvas.create_oval(x1, y1, x2, y2, fill='black')
        else:
            self.id = self.canvas.create_oval(x1, y1, x2, y2,
                                              fill='black' if self.filled else '')

class Arc:
    """Graphical representation of an XDG arc."""

    def __init__(self, canvas, head, dep, tp='', color='black',
                 start=(0,0), end=(100,100), h2w=.625):
        self.canvas = canvas
        self.head = head
        self.dep = dep
        self.type = tp
        self.start = start
        self.end = end
        self.midpoint = (0,0)
        self.label = None
        self.label_center = (0,0)
        self.label_id = 0
        self.color = color
        self.h2w = h2w
        self.label_h2w = h2w * .5

    def draw(self):
        x0, y0 = self.start
        x2, y2 = self.end
        if x2 > x0:
            x1 = x0 + (x2 - x0) / 2
        else:
            x1 = x2 + (x0 - x2) /2
        y1 = y0 - self.h2w * abs(x2 - x0)
        self.midpoint = (x1, y1)
        self.id = self.canvas.create_line(x0, y0, x1, y1, x2, y2,
                                          smooth=True, arrow='last',
                                          fill=self.color,
                                          splinesteps=24)
        if self.type:
            self.make_label()

    def make_label(self):
        self.label = Label(self.canvas, text=self.type,
                           font=("Courier", "10"))
        self.label_center = (self.midpoint[0],
                             self.start[1] - self.label_h2w * abs(self.start[0] - self.end[0]))
        self.label_id = self.canvas.create_window(self.label_center[0],
                                                  self.label_center[1],
                                                  window=self.label)
    

#    def draw_arc_label(self, center, text=''):
#        label = Label(self.parent, text=text)
#        cx, cy = center
#        self.create_window(cx, cy, window=label)
        

class Sentence:
    """A sentence being translated or parsed."""

    def __init__(self, canvas, words, coords=(0,0),
                 node_indices=None, inp=True, width=500):
        self.canvas = canvas
        self.words = words
        self.coords = coords
        self.width = width
        # Input or output sentence
        self.inp = inp
        # Indices of nodes to join to words
        self.node_indices = node_indices if node_indices else range(len(words))
        self.ids = []

    def draw(self):
        gap = self.width / len(self.words)
        x, y = self.coords
        x += gap / 2
        for word in self.words:
            id = self.canvas.create_text(x, y,
                                         text=word,
                                         justify=CENTER)
            self.ids.append(id)
            x += gap

class GraphText(Text):

    def __init__(self, parent, width=50, height=5):
        Text.__init__(self, parent, width=width, height=height)
        self.insert('0.5', "ጤናይስጥልኝ")

def run():
    root = Tk()
#    text = GraphText(root, width=width, height=height)
#    text.grid()
    canvas = Multigraph(root)
    canvas.grid()
    root.mainloop()


