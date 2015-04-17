from distutils.core import setup
from distutils.extension import Extension
from Cython.Distutils import build_ext

ext_modules = [Extension("fs", ["fs.pyx"]),
               Extension("fst", ["fst.pyx"])]

setup(
  name = 'L3Morpho',
  cmdclass = {'build_ext': build_ext},
  ext_modules = ext_modules
)
