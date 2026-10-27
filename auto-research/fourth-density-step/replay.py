"""Replay every exact scalar certificate and verify upstream source hashes."""
import pin_sources
import certify_fourth
import return_certify
import ablation

if __name__=='__main__':
    if not __debug__:raise SystemExit('Assertions required; do not use -O')
    pin_sources.main()
    certify_fourth.main()
    return_certify.main()
    ablation.main()
    print('PASS: exact scalar source, admission, geometry, and full return cover.')
    print('Conditional on the preprint seven-eighths theorem; Lean/analytic assembly pending.')
