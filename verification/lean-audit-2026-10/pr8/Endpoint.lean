import QRHAudit.Target
import Candidate.Main
set_option autoImplicit false
namespace QRHAudit
theorem pr8_endpoint : Target := fun χ hs hpole => Candidate.bound χ hs hpole
theorem pr8_zeta : ZetaTarget := by
  intro s hs hs1
  have h := pr8_endpoint (q := 1) (1 : DirichletCharacter ℂ 1) hs (by rintro ⟨-, rfl⟩; exact hs1 rfl)
  rwa [DirichletCharacter.LFunction_modOne_eq] at h
end QRHAudit
#print axioms QRHAudit.pr8_endpoint
#print axioms QRHAudit.pr8_zeta
#print axioms Candidate.bound
