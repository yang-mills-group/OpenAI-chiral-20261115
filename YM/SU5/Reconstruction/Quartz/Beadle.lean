import YM.SU5.Reconstruction.Quartz.Marginalia
/-!
# Express Prism commutation at a shared theory Actor. Lift & cut.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Quartz.Waltz
open Function Filter Set MeasureTheory Measure Metric Topology
open scoped Topology NNReal ENNReal Complex InnerProductSpace Interval ComplexOrder
open CrossedFrame Clasp Picket Lens Ravin BridgeClub Anvil ConePrice Sail Ship
variable {H E K:Hilbert}(C:Clasp K H E)(X:H.Op)(Y:E.Op)
local notation "Aa"=> C.look.conjStarAlgEquiv
lemma echoPowered (p:C.Pass X Y) : ∃ Z, Powered (C.Back) ((Aa) X) Y (max ‖X‖ ‖Y‖) Z := by
 obtain ⟨G,f⟩:= reflected C X Y p; let Z(z:ℂ):= (Aa) (G z)
 have h(u:ℝ)(g:H.Op):(Aa) (ascend u C g)=ascend (-u) C.Back ((Aa) g):= by rw [ascend,ascend,map_mul,map_mul,map_star, Clasp.carryBoost]
 refine ⟨Z,fun u=>?_,fun u=>?_, (fun z p=>(lift_budget ..).trans (f.cost z p.2)),fun x y=>?_,fun x y=>?_⟩
 · unfold Z; rw [f.at_rail u,h]
 · unfold Z; rw [f.at_other u,h, Ship.run_inv]
 · obtain ⟨x,rfl⟩:= C.look.surjective x; obtain ⟨y,rfl⟩:= C.look.surjective y; unfold Z; simp_rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.symm_apply_apply,LinearIsometryEquiv.inner_map_map]; exact (f.wot x y).mono (fun z p=> p.2)
 obtain ⟨x,rfl⟩:= C.look.surjective x; obtain ⟨y,rfl⟩:= C.look.surjective y; unfold Z; simp_rw [LinearIsometryEquiv.conjStarAlgEquiv_apply_apply,LinearIsometryEquiv.symm_apply_apply,LinearIsometryEquiv.inner_map_map]; exact (f.motions x y).mono (fun z p=> p.2)
variable {a b:Axis} (p:b≠a) (S:OS.Semigroup E a)
lemma sweepSky (x z:H.Op): (C.look).conjStarAlgEquiv (x*z)= Aa x*Aa z:=map_mul ..
lemma loomComm {d:ℝ≥0}(A:E.Op)(B:E.Op)(x:E.Op)(e:B=A*trans S (-((d:ℝ) • basis b)))(h:B* parcelUp S ((d:ℝ) • basis b) x=x*B) : Commute A x:= by
 let u:=(d:ℝ) • basis b; rw[e,parcelUp] at h
 have hx: B * trans S u= A:= by rw[e,mul_assoc,mail_inv,mul_one]
 rw[commute_iff_eq]; have he:trans S (-u)*trans S u=1:=mail_inv ..
 change A*trans S (-u)*(trans S u*x*trans S (-u))=x*(A*trans S (-u)) at h
 calc A*x = (A*trans S (-u)*(trans S u*x*trans S (-u)))*trans S u:= by simp only [mul_assoc,← mul_assoc (trans S (-u)) (trans S u),mail_inv,one_mul,mul_one]
      _ = x*A :=by rw[h]; simp only[mul_assoc,mail_inv,mul_one]
end YM.Quartz.Waltz
