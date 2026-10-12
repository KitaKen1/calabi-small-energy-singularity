"""Recompute the finite interval certificate and close rational proof bounds.

Run with assertions enabled. This checks the computational inequalities used
in the accompanying analytic proof. It is not a formal proof checker for PDEs.
Requires the saved Newton 1 JSON only for rational choices; no floating-point
calculation is used to validate them. GMP is an optional integer accelerator.
"""
from pathlib import Path
from fractions import Fraction as F
import os,json,pickle
if not __debug__:
    raise RuntimeError('Assertions are required: do not use -O, -OO, or PYTHONOPTIMIZE.')
os.environ['CALABI_CERT_DEGREE']='58'
import calabi7_interval as q
from calabi7_tail import checks,exp_upper
from calabi7_ledger import run as ledger
P=Path(__file__).resolve().parent

def verify(recompute=True):
    assert __debug__, 'Do not use python -O.'
    record=json.loads((P/'calabi7_newton_1.json').read_text())
    q.k=q.decimal(record['input']['k']);q.d=q.decimal(record['input']['d'])
    q.ks=[q.I,q.O];q.ds=[q.O,q.I]
    if recompute:
        flows=q.makeflows()
        assert q.arithmetic_stats['max_state_width']*10**24<q.scale
        assert q.arithmetic_stats['max_matrix_entry_width']*10**24<q.scale
        widths={k:str(F(int(v),int(q.scale))) for k,v in q.arithmetic_stats.items()}
        with (P/'calabi7_flows_1.pickle').open('wb') as f:pickle.dump(flows,f)
        (P/'calabi7_widths_exact.json').write_text(json.dumps(widths,indent=2)+'\n')
    else:
        widths=json.loads((P/'calabi7_widths_exact.json').read_text())
        assert F(widths['max_state_width'])<F('1e-24') and F(widths['max_matrix_entry_width'])<F('1e-24')
    row=ledger(1);b={k:F(v) for k,v in row['exact_bounds'].items()};checks()
    assert b['product']<260000 and b['sum_products']<39000000 and b['weighted_sum']<127000000
    assert b['variation']<F('2.69') and b['origin_variation']<F('.00008')
    assert b['q_linear']<F('.079') and b['identity_error']<F('1e-6') and b['d_row']<F('.00007')
    R=F('1e-12');N=576;G=260000
    center_k=F(record['input']['k']);center_d=F(record['input']['d'])
    assert F('.13429')<center_d-F('.00007')*R<center_d+F('.00007')*R<F('.13430')
    assert center_k+F('.00007')*R<0 and abs(center_k)<F('.188364')
    transfer_error=G*((1+4*F('1e-24')*G)**N-1)
    assert transfer_error<F('1e-8')
    assert 39000000+N*transfer_error<40000000
    assert 127000000+55*transfer_error/F('.07')**3<130000000
    assert b['variation']+transfer_error*b['origin_variation']<F('2.69')
    # Origin truncation at r-degree 100, including two s derivatives.
    # For i>=101, i^2/3^i decreases with successive ratio <.34.
    origin_tail=F('.75')*F(9,4)*101**2/F(3)**101/(1-F('.34'))
    assert origin_tail<F('1e-42')
    assert q.origin()  # its finite interval widths are asserted in origin().
    parameter_sum=F('.00014')*R/F('.01')
    germ_nonlinear=2*parameter_sum**2/(1-parameter_sum)
    assert germ_nonlinear<F('.001')*R**2
    E0=F('1e-38')+F('.001')*R**2
    E=40000000*F('1e-24')+260001*E0+3*130000000*F('1.001')*(10*R)**2
    assert E<F('.04')*R
    assert F('.07')/(F('.07')-10*R)<F('1.001')
    assert 3*(F('2.69')*R+E)+3*F('1.001')*(10*R)**2/F('.07')**3<10*R
    assert b['jet_residual']<F('.03')*R and b['projected_residual']<F('.01')*R
    projection_error=F('3e-10')
    pa_error=F('.001')*F('.00007')*R
    remainder=E+transfer_error*b['origin_variation']*R+pa_error
    q_bound=b['projected_residual']+projection_error*b['jet_residual']+(F('.079')+projection_error*F('2.69'))*R+F('.94')*remainder
    xi_bound=b['projected_residual']+projection_error*b['jet_residual']+(F('1e-6')+projection_error*F('2.69'))*R+F('.66')*remainder
    assert q_bound<F('.15')*R and xi_bound<F('.04')*R
    # Tail: |q|<=.16R and source ball ||j||<=.1R, by exact checks().
    assert F('4e-22')+F('.23')*F('.16')*R+F('.39')*F('.1')*R<F('.1')*R
    assert F('.8')*F('.1')<F('.08')+F('1e-20')
    assert F('.04')+F('.08')<1  # Brouwer map sends square strictly inside itself.
    out=dict(all_rational_inequalities_pass=True,R=str(R),reference_positive_lower_bound='.07',
        exact_widths=widths,endpoint_error_over_R=float(E/R),q_bound_over_R=float(q_bound/R),
        unstable_matching_error_over_R=float(xi_bound/R),tail_unstable_bound_over_R=.08,
        brouwer_self_map_bound_over_R=.12,finite_blocks=576,taylor_degree=58,
        origin_series_degree=100,integer_scale_bits=384,
        statement='Computational components of the n=7 positive-profile proof passed. See PDF/calabi-small-energy.pdf in the repository.',
        lean_formalized=False,independent_review=False,annals_level_novelty_certified=False)
    (P/'calabi7_verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2),flush=True)

if __name__=='__main__':verify(recompute=True)
