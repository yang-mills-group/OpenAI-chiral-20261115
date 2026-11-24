import YM.CF.BProof.Double.Heal
/-! Uniform angle estimator from the occupied support hypotheses (outer Wick). -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Double
open Function Filter Fock Finset Branch Align Wick
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {I:Type*}[Fintype I][DecidableEq I][Nonempty I] {A P Q C:Op I}{c r D:ℝ} {x y:Book I} {u v y': Ket I}
lemma fuel {D:ℝ} (Y:Op I)(t:IsStarProjection Y)(q:acts Y y'=0)(g:‖u-y'‖≤D) : ‖acts Y u‖≤D:= by rw [← sub_zero (acts Y u),←q,←map_sub]; exact (funded t _).trans g -- need y' binder
-- gap tariff ≥1.
def β (c:ℝ):= 2*(1+c⁻¹)
def α (c r:ℝ):=(1-r)⁻¹*β c
def debt (c r:ℝ):= c⁻¹* (α c r+1) + c⁻¹*(β c+α c r+1)+1
lemma debt_one (p:0<c)(h:r<1) : 1≤ debt c r:=by unfold debt α β; have he:=sub_pos.mpr h; exact le_add_of_nonneg_left (by positivity)
namespace Deck
variable (p: Double.Deck A P Q C c r)(e:Enter x A) (g:Live y P Q C)(E: ‖x-y‖≤D)
include p e g E
theorem corrections : ∃ u v:Ket I, (acts A u=u∧acts P u=0 ∧ ‖rows x-u‖≤c⁻¹ * D ∧ ‖u-rows y‖≤ (1+c⁻¹)*D) ∧ (acts (cc A) v=0∧acts Q v=0 ∧ ‖cols x-v‖≤ c⁻¹*D∧‖v-cols y‖≤(1+c⁻¹)*D):=by
 let b:= p.cbP; let A':=cc A; have hu: acts (1-cc A) (cols x)=cols x:=by rw [act_sub,act_one,e.2,sub_zero]
 obtain ⟨u',A0,U0,H⟩:= treatment b e.1; obtain ⟨v',B0,V0,L⟩:= treatment p.switching hu; have he(s t x: Ket I)(k: ‖x-t‖≤D)(h:‖x-s‖≤ c⁻¹*D):‖s-t‖≤(1+c⁻¹)*D:= (norm_sub_le_norm_sub_add_norm_sub s x t).trans ((add_le_add ((norm_sub_rev ..).trans_le h) k).trans_eq (by ring))
 obtain ⟨f,a,b⟩:= g
 have hP : ‖rows x-rows y‖ ≤ D:=(bio_cost (x-y)).trans E; have hQ: ‖cols x-cols y‖ ≤ D:=(mead_cost (x-y)).trans E
 have hz:=p.cbP.nice; have hv:= H.trans (mul_le_mul_of_nonneg_left (fuel _ p.cbP.p f hP) (by positivity)); have hh:= L.trans (mul_le_mul_of_nonneg_left (fuel _ p.cbP.q a hQ) (by positivity))
 rw [act_sub,act_one] at B0; exact ⟨u',v',⟨A0,U0,hv,he u' (rows y) _ hP hv⟩,sub_eq_self.mp B0,V0, hh,he v' (cols y) _ hQ hh⟩
theorem curve: ‖x‖≤debt c r*D:=by
 obtain ⟨u,v,⟨A',P',U,Y⟩,B',Q',V,X⟩:= p.corrections e g E; let L:=space P Q; let w:=acts L v; let t:=acts L u; let T:=entryP A P Q; let f:= acts (cc C) t
 have hv: ‖w-f‖ ≤ β c *D:=by
    let W:=acts L (cols y); have he: acts L (cols y)=acts (cc C) (acts L (rows y)):= g.2.2; apply (norm_sub_le_norm_sub_add_norm_sub w W f).trans
    have hs: ‖w-W‖≤(1+c⁻¹)*D:=by unfold w W; rw [← map_sub]; exact (funded p.cbP.wall (v-cols y)).trans X
    have hg: ‖W-f‖≤(1+c⁻¹)*D:=by unfold W f t; rw [he,←map_sub,←map_sub (acts L),act_unit_norm (U:=⟨_,p.barUnit⟩)]; exact (funded p.cbP.wall _).trans ((norm_sub_rev ..).trans_le Y)
    exact (add_le_add hs hg).trans_eq (by unfold β; ring)
 have hp:acts T t=t:=(p.cbP.inPiH _).2 ⟨u,A',P',rfl⟩; have hu: ‖t‖≤ α c r*D:= by
    have he:= p.design hp; change _≤ ‖acts (cc T) f‖ at he; rw [← sub_zero (acts _ f),← show acts (cc T) w=0 from p.plant B' Q', ←map_sub] at he; have hz:= he.trans ((funded (ccProj p.cbP.PiHp) _).trans ((norm_sub_rev ..).trans_le hv)); unfold α; rw [mul_assoc,← div_eq_inv_mul (β c*D) (1-r), le_div_iff₀ (sub_pos.mpr p.safety.lid),mul_comm]; exact hz -- check div
 have hw : ‖w‖ ≤ (β c+α c r)*D:= by apply (norm_le_norm_sub_add w f).trans; rw [add_mul]; exact add_le_add hv ((act_unit_norm (U:=⟨_,p.barUnit⟩) t).trans_le hu) -- tune
 have hc:(0:ℝ)<c:= p.cbP.nice; have hg: ‖u‖≤ c⁻¹*(α c r*D):= by rw [← div_eq_inv_mul, le_div_iff₀ hc,mul_comm]; exact (woods p.cbP A' P').trans hu
 have hz: ‖v‖ ≤ c⁻¹*((β c+α c r)*D):=by rw [←div_eq_inv_mul,le_div_iff₀ hc,mul_comm]; exact (p.stepdown B' Q').trans hw
 have hd:0≤D:= (norm_nonneg _).trans E; refine (bag_cost x).trans ((add_le_add ((norm_le_norm_sub_add _ u).trans (add_le_add U hg)) ((norm_le_norm_sub_add _ v).trans (add_le_add V hz))).trans ?_); unfold debt; linarith only [hd] -- maybe ring_nf
end Deck
end YM.CF.BProof.Double
