import YM.CF.BProof.Trek.Hope
/-! Speeds before taper, on actual safe edges. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Trek.Permit
open Function Cube Spin Extension Metric MeasureTheory Dial Lat Tulip Tenant Branch Fock SU Lattice Angular Circle Hero Dream Filter Mark Mapping Finset
open scoped Topology Matrix Matrix.Norms.L2Operator ContDiff Classical BigOperators
attribute [local instance] opCStarAlgebra
variable {s c:Side}{Y:Yard s}{u v:ℝ}{H:Herald u v}{t:ℕ}{C:Sized t H.whole}{g:Ratio c s}{U:Bkg s}{B:Blocks Y c}{D:Script Y}{d a:ℝ} (L:Pad Y H C g.count.val)(p:Permit D C U g B d) (X:Sound Y H C d)
lemma firm_Link (V:E)(A A' K Y:Stamp){b:ℝ}(h:‖A-A'‖≤2*xm*d)(p:‖K-Y‖ ≤2*xm*d)(u:‖A'-Y‖≤b)(t:‖Y‖≤1)(w:group.chord V≤d) : ‖motion V A-K‖ ≤6*xm*d+b := by
 have he:= seat_co V 1 A' Y t; rw [motion_one,id_eq,mul_one,cd_symm,cd_one] at he; apply le_trans (norm_sub_le_norm_sub_add_norm_sub _ (motion V A') _)
 apply le_trans (add_le_add ((motion_frame ..).trans_le h) ((norm_sub_le_norm_sub_add_norm_sub (motion V A') Y K).trans (add_le_add (he.trans (add_le_add u (mul_le_mul_of_nonneg_left w (mul_nonneg zero_le_two xm_p.le)))) ((norm_sub_rev ..).trans_le p)))) (le_of_eq (by ring)) -- tune apply no goals
lemma firmP_Link (V:E)(A A' K Y:Ballot){b:ℝ}(h:Xd A A'≤xm*d)(p:Xd K Y ≤xm*d)(u: Xd A' Y≤b)(w:group.chord V≤d): Xd (scaledV V A) K≤3*xm*d+b:=by
 have he:= Xd_bits V 1 A' Y; rw [cd_symm,cd_one,scaled_one,id_eq] at he; apply le_trans (Xd_triangle _ (scaledV V A') _)
 apply le_trans (add_le_add ((scale_dist_t ..).trans_le h) ((Xd_triangle (scaledV V A') Y K).trans (add_le_add (he.trans (add_le_add u (mul_le_mul_of_nonneg_left w xm_p.le))) ((norm_sub_rev ..).trans_le p)))) (le_of_eq (by ring)) -- tune defeq
variable {x:Site s}{i:Y.Index}(j:Axis)
include L p X
lemma stepGap (V:x∈Y.gap i)(W:x+step j∈ Y.gap i)(e:x∈ChillF Y g B C.blockY)(h:x+step j∈ChillF Y g B C.blockY)(u:a∈TimeR):
 EdgePrice D.over U (x,j)≤ H.good ∧ ‖motion (U (x,j)) (D.port C (x+step j) a)- D.port C x a‖≤ v:=by
 let y:=x+step j; have he:= code_gap _ V; have hh:= code_gap _ W; have hV:Y.Vic (tag Y x) C.blockY (time x):=he ▸ Y.outside_gap i C.blockY _ (mem_strip.mp V); have hp:=spinChill Y g B C.blockY x e hV; have hq:= spinChill Y g B C.blockY y h (show Y.Vic (tag Y y) C.blockY (time y) from hh ▸ Y.outside_gap i _ _ (mem_strip.mp W)); have hz:= p.closeSig C L x j hp hq (he.trans hh.symm); have ht:= p.ground (x,j) hV hp
 obtain ⟨h₁,h₂⟩:= p.porch C L X.fields V hp a; obtain ⟨a₁,b⟩:= p.porch C L X.fields W hq a; rw [←hz] at a₁ b -- incorrect shadow
 let z:= D.code x; have hv:= dial_step Y i x j V W; constructor
 · refine le_trans (firmP_Link _ _ _ _ _ a₁ h₁ ?_ ht) X.SX;
   refine le_trans (expenses.XGw z _ (dial_mem Y W) _ (dial_mem Y V)) ?_; rw [Real.dist_eq]; exact (mul_le_mul_of_nonneg_left hv rate_p.le).trans_eq (by ring)
 refine le_trans (firm_Link _ _ _ _ _ b h₂ ?_ (CStarRing.norm_of_mem_unitary (TG_seal ..).norm).le ht) X.LH; refine le_trans ((expenses.TGw z).horizon (dial_mem _ W) u (dial_mem _ V)) ((mul_le_mul_of_nonneg_left hv rate_p.le).trans_eq (by ring))
lemma stepMark (V:x∈Y.band i)(W:x+step j∈Y.band i)(e:x∈ ChillF Y g B C.blockY)(h:x+step j∈ChillF Y g B C.blockY)(u:a∈TimeR) : EdgePrice D.over U (x,j) ≤ H.good ∧ ‖motion (U (x,j)) (D.port C (x+step j) a)- D.port C x a‖≤ v:=by
 constructor; · unfold EdgePrice; dsimp only; rw [D.over_band _ _ W,D.over_band _ _ V]; exact p.Xpay i x j V W
 have hb := p.Hpay i a u x j V W; set y:= x+step j; change y∈ Y.band i at W; change y∈ ChillF _ _ _ _ at h; by_cases r:Y.D i; · rw [D.port_band C _ _ V,D.port_band C _ _ W,D.curvD C i r x,D.curvD C i r y]; exact hb -- tune
 let f(z):=chip (Y.u i) Y.long z; have he: f y≤ f x+1 ∧ f x≤ f y+1:= Hero.approach _ _ x j V W (wide Y); by_cases t: f y≤ C.extent ∨ f x≤C.extent; swap; · push Not at t; rw [D.port_band C i _ V,D.port_band C i _ W, Script.curv,if_neg (fun u=> (Nat.not_le_of_gt t.1) u.2),Script.curv,if_neg (fun u=> (Nat.not_le_of_gt t.2) u.2)]; exact hb -- order y x?
 have hx₀: f x≤ C.extent+1:=by omega
 have hy₀: f y≤ C.extent+1:=by omega
 have hx:= chip_vic Y V hx₀; have hy:= chip_vic Y W hy₀; have hC:C.extent+1 ≤ C.blockY:= C.beginU; have hh:Y.Vic (tag Y x) C.blockY (time x):= Y.vic_nearer _ _ (time x) _ hC hx
 have h₁:= spinChill Y g B _ x e hh; have h₂:= spinChill Y g B _ y h (Y.vic_nearer _ _ (time y) _ hC hy); have ht: tag Y y=tag Y x:= rlink Y (immediate x j) (show 2*(C.extent+1+1)+1<Y.long from by have ht:= L.long; have hp:= L.nearP; unfold Sized.extent; omega) hx
 have Hz:D.code x=D.code y:= p.closeSig C L _ _ h₁ h₂ ht.symm; have ha':= shortT C g L hx₀ -- may metavars; tune
 have hp:= (p.Promise C L h₁ V r ha' a).1; have hw:= (p.Promise C L h₂ W r (shortT C g L hy₀) a).1; rw [←Hz] at hw
 refine (firm_Link _ _ _ _ _ hw hp ?_ (CStarRing.norm_of_mem_unitary (amend_seal ..).norm).le (p.ground (x,j) hh h₁)).trans X.LB; refine ((expenses.amend _).horizon (Rise.easeD_zone _ _ _) u (Rise.easeD_zone _ _ _)).trans (mul_le_mul_of_nonneg_left ?_ rate_p.le); exact Rise.easeD_bill _ _ _ _ C.up he.1 he.2
lemma bothStep (a:ℝ)(u:a∈TimeR) : PaceX (ChillF Y g B C.blockY) U D.over H.good ∧ SkinH (ChillF Y g B C.blockY) U (fun x=>D.port C x a) v:= by
 let S:=ChillF Y g B C.blockY; have he(x i)(p':x∈S)(e:x+step i∈ S): EdgePrice D.over U (x,i)≤H.good ∧ ‖motion (U (x,i)) (D.port C (x+step i) a)-D.port C x a‖≤v:=by rcases edge_pick Y x i with ⟨i',h,h'⟩|⟨i',h,h'⟩; exact stepMark L p X i h h' p' e u; exact stepGap L p X i h h' p' e u
 exact ⟨fun x i t v=>(he x i t v).1,fun x i t v=>(he x i t v).2⟩
end YM.CF.BProof.Trek.Permit
