from setuptools import setup, find_packages

setup(name='CoSA',
      version='0.2',
      description='CoreIR Symbolic Analyzer',
      url='http://github.com/cristian-mattarei/CoSA',
      author='Cristian Mattarei',
      author_email='cristian.mattarei@gmail.com',
      license='BSD',
      packages = find_packages(),
      include_package_data = True,
      install_requires=["six","pyparsing","pysmt","coreir"],
      entry_points={
          'console_scripts': [
              'CoSA = cosa.shell:main'
          ],
      },
      zip_safe=True)
