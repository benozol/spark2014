import os
from test_support import *

os.environ['GNATPROVE_RAC'] = 'yes'
os.environ['GNATPROVE_RAC_TRACE'] = 'yes'

prove_all (sort_output=False, check_counterexamples=True)
check_counterexamples()
