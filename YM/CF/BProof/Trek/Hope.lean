import YM.CF.BProof.Trek.Crew
/-! Orientation and gap discrepancies. Hom desk. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Trek.Permit
open Function Cube Spin Extension Metric MeasureTheory Dial Lat Tulip Tenant Branch Fock SU Lattice Angular Circle Hero Dream Filter Mark Mapping Finset
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff Classical BigOperators
attribute [local instance] opCStarAlgebra
variable {s c:Side}{Y:Yard s}{u v:ℝ}{H:Herald u v}{t:ℕ}(C:Sized t H.whole){g:Ratio c s}{U:Bkg s}{B:Blocks Y c}{D:Script Y}{d:ℝ} (L:Pad Y H C g.count.val)(P:Permit D C U g B d) {i:Y.Index}{x:Site s}
-- boost close where needed
lemma booster (i:Fin 5)(x:E): cd group (x*Mag.center i) 1= cd group x (locus i):=by rw [← cd_mul_right group (locus i)]; group -- tune moved LHS both? careful
include L P
lemma Ticket (p:distant Y g B x 2)(m:x∈Y.band i)(h:¬Y.D i)(e:chip (Y.u i) Y.long x*10≤Y.long) : let a:=D.frame i x; let w:=D.code x; D.port C x= motion (a*Mag.center w) ∘ amend w (Script.ramp C i x) ∧ D.over x= scaledV a apex ∧ cd group a (locus w)≤d :=by
 intro a w; have he:= P.fieldN _ h x m e; refine ⟨?_,(D.over_band i x m).trans he.1,P.erm _ h x m e p⟩; by_cases f:Script.stand C i x; rw [D.port_band C i _ m,D.curvSet C i h _ f]; rfl; rw [exitR C f,D.port_band C i x m, Script.curv,if_neg (fun u=> f u.2),he.2]; ext1 t; exact (rosy_fuse ..).symm
lemma Promise (p:distant Y g B x 2)(m:x∈Y.band i)(h:¬Y.D i)(e:chip (Y.u i) Y.long x*10≤Y.long) (t:ℝ) : let i':= D.code x; let s:=Script.ramp C i x; ‖D.port C x t - amend i' s t‖≤ 2*xm*d ∧ Xd (D.over x) (scaledV (locus i') apex)≤ xm*d := by
 intro i' s; obtain ⟨p,v,w⟩:= P.Ticket C L p m h e; unfold i' s; rw [p,v]; let A:=D.frame i x; let U:= (A*Mag.center i'); refine ⟨?_,?_⟩
 · change ‖motion U (amend i' s t)-amend i' s t‖≤ _; let X:=amend i' s t; have he: ‖X‖≤1:=(CStarRing.norm_of_mem_unitary (amend_seal i' s t).norm).le; have hx:= seat_rate U 1 X he; rw [mul_one,show cd group U 1=_ from booster i' A,motion_one,id_eq] at hx; exact hx.trans (mul_le_mul_of_nonneg_left w (mul_nonneg zero_le_two xm_p.le))
 apply (Xd_rate ..).trans; exact mul_le_mul_of_nonneg_left w xm_p.le
lemma levelD (p:x∈Y.band i)(h:Y.D i): D.over x=apex ∧ D.port C x=BM 1:= ⟨(D.over_band _ _ p).trans (P.fieldD _ h x p).1, (D.port_band C _ _ p).trans ((D.curvD C i h x).trans (P.fieldD _ h x p).2)⟩
lemma porch (q:0<d)(p:x∈Y.gap i)(f:distant Y g B x 2)(a:ℝ) : let z:=D.code x; let t:=dial Y i x; Xd (D.over x) (XG z t) ≤ xm*d ∧ ‖D.port C x a-TG z t a‖≤ 2*xm*d:=by
 intro z T; have he:= xm_p; by_cases t':dark Y x; swap; · unfold Script.over Script.port; dsimp only; simp only [t',↓reduceIte]; rw [code_gap Y p]; change Xd (XG z T) (XG z T)≤_ ∧ ‖TG z T a-TG z T a‖≤_; simp only [Xd,sub_self,norm_zero]; constructor <;> positivity
 let j:= hr Y x; have hp: x∈Y.band j:= band_pick Y x t'; have hh:= finishD Y j i x hp p; by_cases v:Y.D j
 · obtain ⟨a₁,b₁⟩:=levelD C L P hp v; rw [if_pos v] at hh; unfold T; rw [a₁,b₁,hh,XG0,TG_d] -- TG_d argument order already any s? yes
   simp only [Xd,sub_self,norm_zero]; constructor <;> positivity
 obtain hv:= Promise C L P f hp v (by rw [meeting Y hp p]; omega) a; rw [show Script.ramp C j x=0 from entryR C (by rw [meeting Y hp p]; omega)] at hv; dsimp only at hv; rw [←TG_side] at hv; unfold T; rw [if_neg v] at hh; rw [hh,XG1]; exact And.symm hv
lemma closeSig(x:Site s)(i:Axis)(p:distant Y g B x 2)(h:distant Y g B (x+step i) 2)(t:tag Y x=tag Y (x+step i)): D.code x=D.code (x+step i):=by
 unfold distant at h; unfold Script.code; simp only [← t,space_add] at * -- t simp at * erases t but h rew?
 revert h; refine Fin.cases ?_ ?_ i
 · rw [space_step0, add_zero]; simp
 intro v h; exact P.coherent _ _ v p h
end YM.CF.BProof.Trek.Permit
