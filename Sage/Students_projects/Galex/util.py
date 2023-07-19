import numpy as np
from random import uniform, seed as set_seed
import matplotlib.pyplot as plt

plt.rcParams.update({
    "figure.facecolor":  (1.0, 0.0, 0.0, 0.0),
    "axes.facecolor":    (0.0, 1.0, 0.0, 0.0),
    "savefig.facecolor": (0.0, 0.0, 1.0, 0.0),
    "axes.edgecolor": (0,1,1,1),
    "xtick.color": (0,1,1,1),
    "ytick.color": (0,1,1,1),
    "lines.color": (1,0,1),
    "xtick.labelsize": 'large',
    "ytick.labelsize": 'large',
})


class Plotter:
    def __init__(self, xmin=0, xmax=4, ymin=0, ymax=6, errmin=None, errmax=None):
        self.ERRMIN = errmin if errmin is not None else [-1]
        self.ERRMAX = errmax if errmax is not None else [1]
        self.XMIN, self.XMAX = xmin, xmax
        self.YMIN, self.YMAX = ymin, ymax
        self.entities = []

    def plot_pts(self, xs, ys, *args, **kwargs):
        self.entities.append(('points', xs, ys, args, kwargs))

    def plot_func(self, f, *args, **kwargs):
        self.entities.append(('func', f, args, kwargs))
        
    def get_datapts(self, func, c:int, n:int, seed=None):
        '''Returns an array with c columns and n rows, i.e. c points of dimension n.'''
        if isinstance(seed, int):
            set_seed(seed)
        datamatrix = np.ndarray((n,c))
        datamatrix[0] = np.linspace(self.XMIN, self.XMAX, c)
        datamatrix[1] = func(datamatrix[0])
        ynoise = np.fromiter((uniform(self.ERRMIN[i], self.ERRMAX[i]) for i in range(n-1) for _ in range (c)), float, count=c*(n-1)).reshape((n-1,c))
        datamatrix[1:,] += ynoise
        return datamatrix

    def measure_error(self, func, pts):
        xs, ys = pts
        func_ys = func(xs)
        error_data = ('text', 0.1, 4.9 , f"Regression Error: {sum((ys - func_ys)**2)}", {'c':(1, .3, 0)})
        self.entities.append(error_data)

    def show(self):
        for entity in self.entities:
            match entity[0]:
                case 'points':
                    xvals, yvals, args, kwargs = entity[1:]
                    plt.plot(xvals, yvals, *args, **kwargs)
                case 'func':
                    func, args, kwargs = entity[1:]
                    xvals = np.linspace(self.XMIN, self.XMAX, 300)
                    plt.plot(xvals, func(xvals), *args, **kwargs)
                case 'text':
                    plt.text(*entity[1:])
                case _:
                    raise ValueError("Unsupported type for drawing")
        plt.xlim(self.XMIN, self.XMAX)
        plt.ylim(self.YMIN, self.YMAX)
        plt.show()

    def reset(self):
        self.entities.clear()
