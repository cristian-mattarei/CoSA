from setuptools import setup

setup(name='CoSA',
      version='0.1',
      description='CoreIR Symbolic Analyzer',
      url='http://github.com/cristian-mattarei/CoSA',
      author='Cristian Mattarei',
      author_email='cristian.mattarei@gmail.com',
      license='BSD',
      packages=['cosa'],
      install_requires=["six","pyparsing","pysmt","coreir"],
      entry_points={
          'console_scripts': [
              'CoSA = cosa.shell:main'
          ],
      },
      zip_safe=True)
