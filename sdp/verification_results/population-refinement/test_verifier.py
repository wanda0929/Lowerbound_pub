#!/usr/bin/env python3
"""Exact/validated verifier unit tests, distinct from full certificate replay."""
import json,sys,unittest
from fractions import Fraction as R
from math import comb
from flint import arb_mat,ctx
import verify_projected_slack as v
import verify_population_slack as p
ctx.prec=384
class VerificationTests(unittest.TestCase):
    def test_valid_projection_order(self):
        Q=arb_mat([[2,1],[1,2]]);E=arb_mat([[1],[0]])
        H=Q.solve(E,algorithm='precond')[0,0]
        S=arb_mat([[1]])
        v.posdef(S);v.posdef(S.inv()-arb_mat([[H]]))
    def test_invalid_projection_order_rejected(self):
        Q=arb_mat([[2,1],[1,2]]);H=Q.solve(arb_mat([[1],[0]]),algorithm='precond')[0,0]
        with self.assertRaises(ValueError):v.posdef(arb_mat([[v.ba(R(1,2))]])-arb_mat([[H]]))
    def test_singular_matrix_rejected(self):
        with self.assertRaises(ValueError):v.posdef(arb_mat([[1,1],[1,1]]))
    def test_negative_matrix_rejected(self):
        with self.assertRaises(ValueError):v.posdef(arb_mat([[1,2],[2,1]]))
    def test_nonzero_quadratic_field_sign(self):
        self.assertTrue(v.scalar('3 - 2*sqrt(2)')>0)
        self.assertTrue(v.scalar('2*sqrt(2) - 3')<0)
    def test_unsafe_scalar_rejected(self):
        with self.assertRaises(ValueError):v.scalar('__import__("os")')
    def test_interval_bound_nonconstant(self):
        self.assertEqual(v.min_bernstein([R(1),R(-2),R(1)],R(0),R(1,2)),R(1,4))
    def test_endpoint_negative_detected(self):
        self.assertLess(v.min_bernstein([R(1),R(-2)],R(0),R(1)),0)
    def test_population_identities_exhaustive_degree_five(self):
        D=5
        for g in range(D+1):
          for r in range(D+1-g):
           for h in range(D+1-g-r):
            for s in range(D+1-g-r-h):
             coefficients=p.pop_coeff([g,r,h,s],D)
             for x,y in [(R(0),R(1)),(R(1,3),R(2,5)),(R(1),R(0))]:
                actual=sum((coefficients[i*(D+1)+j]*comb(D,i)*x**i*(1-x)**(D-i)*comb(D,j)*y**j*(1-y)**(D-j) for i in range(D+1) for j in range(D+1)),R(0))
                self.assertEqual(actual,(1-x)**g*x**r*(1-y)**h*y**s)
    def test_cost_polynomial_identity(self):
        for D in [1,3,5,7]:
            x,y=R(2,7),R(5,9)
            z=sum(((R(i,2*D)+R(j,4*D))*comb(D,i)*x**i*(1-x)**(D-i)*comb(D,j)*y**j*(1-y)**(D-j) for i in range(D+1) for j in range(D+1)),R(0))
            self.assertEqual(z,x/2+y/4)
    def test_bernstein_partition_unity(self):
        for D in [1,5,13]:
            for t in [R(0),R(2,7),R(1)]:self.assertEqual(sum((R(comb(D,k))*t**k*(1-t)**(D-k) for k in range(D+1)),R(0)),1)
    def test_no_optimization_imports(self):
        self.assertNotIn('scipy',sys.modules)
        self.assertNotIn('certify_population_slack',sys.modules)
        self.assertNotIn('certify_projected_slack',sys.modules)
if __name__=='__main__':
    result=unittest.TextTestRunner(verbosity=2).run(unittest.defaultTestLoader.loadTestsFromTestCase(VerificationTests))
    print(json.dumps({'tests_run':result.testsRun,'failures':len(result.failures),'errors':len(result.errors),'status':'PASS' if result.wasSuccessful() else 'FAIL'}))
    sys.exit(not result.wasSuccessful())
