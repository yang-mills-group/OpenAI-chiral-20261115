import YM.CF.Reine.King
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Esti
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
variable {O:Stores S}{F: Forest S.ratio}{Y:LinkArray G (Frozen A x F)}{z:LogArray G (Active A x F)}{β Q γ D L M s:ℝ}{J:ChartRatio G}{P:Patch}
theorem vestaM(P:Teller G)(Q:Patch)(h:Q.Branches P.bind G) (n j l:ℕ)(hn:3 ≤ n)(hj:2 ≤ j)(hl:l ≤18)(W:Push.Uniform.Before G P.top.width P.top.paths P.j P.bind n)(W':Push.Uniform.Before G P.top.width P.top.paths P.j P.bind (n+2))(q:Chi)(S':ChartRatio G)(hp:LocalRatio S') (w width γ y':ℝ)(hw:0<w)(hy:0<width):∃ A B C D M L u m K s M1 D1:ℝ,0<A ∧0<B ∧1 ≤ C ∧0 ≤ D ∧1 ≤ M ∧0 ≤ L ∧0<u∧1 ≤ m ∧0≤K∧0< s∧1 ≤ M1 ∧ 1 ≤ D1 ∧∀ᶠ x in atTop, fiery G x Q.L ≤ s/2 ∧ (∀ {c f:Side}(S:StepData c f)(T:Tube G S),Cert Q P S T x→∀ Cx:ℝ,1 ≤ Cx→ Volo S n s D1 Cx (covetM G n Cx M1 D1)) ∧ Ticket P Q q S' n j l w width γ y' x A B C D M L u m K s :=by
 obtain ⟨A,B,hA,hB,H⟩:= wind P Q h n l W' q width hy (by omega) hl; obtain ⟨s,D,h',hd,hO⟩:= strut G n P Q W hn; obtain ⟨u',m,hv',hm,hr'⟩:=rene S' hp n
 let u:=min u' 1; have hu:0<u:=lt_min hv' zero_lt_one
 obtain ⟨ξ,hξ,hI⟩:=tock n; let C:=max ξ ‖(1:SU.group.Mat)‖; have hc:1 ≤ C:=hξ.trans (le_max_left ..)
 obtain ⟨b,M,hb,hM,hb'⟩:=bindsM G n s D h' hd Q
 let K:=covetM G n C M D; have hK:0 ≤ K:=by unfold K covetM Jet.composeCost dressM purM; have hh:= SU.group.colorScale_pos; positivity
 obtain ⟨G',hx,Hx⟩:= currencyT q n; let X:=purM G n*C*horse Q n C b G' K; obtain ⟨X',X''⟩:= Push.Uniform.paint_supply G n; obtain ⟨B',hp',Hs⟩:= scope_p P Q X' X C (by unfold X horse purM; have hg:= SU.group.colorScale_pos; have hd:1 ≤ max 1 (zest n * dam G n (b/2) G' C):=le_max_left ..; positivity) (le_max_right ..) n X''
 obtain ⟨a,ha,Hw⟩:= owns P Q q n width hy h
 let d:= u/(Push.Uniform.shade G*((n.factorial:ℝ)* (1+1:ℝ)^n)); let L:= a*(d+1); have hL:=Push.Uniform.shade_pos G; have ht:0<d:=by unfold d; positivity
 let C':= A+2*(2^n*A*B); have hk:0<C':=by unfold C'; positivity
 refine ⟨A,B,C,B',G',Jet.composeCost n L 1,u,m,K,b,M,D,hA,hB,hc,hp',hx,(by unfold Jet.composeCost L; positivity),hu,hm,hK,hb,hM,hd,?_⟩
 filter_upwards [H,Hw,order_r P Q,monitors G Q.L, (year G Q.L).eventually (eventually_gt_atTop 0), expM Q (hp:=lt_min (half_pos hb) zero_lt_one), expM Q (hp:=div_pos ht hk), Work.E01.radiusB_tendsto.eventually_ge_atTop (10*shovel Q+100)] with x hU Ht hP hy hy' hb hz hq
 refine ⟨hb.trans (min_le_left ..),?_,?_⟩
 · intro c f S T e Y hp
   let J:= hO S T e.got e.funds.1; have hS:= e.size; have hf: 2*(gun Q+1)< f.val:=by rw [S.sizes, e.got]; apply Nat.lt_of_lt_of_le _ (Nat.le_mul_of_pos_right _ Q.L.property); unfold shovel gun at *; omega
   constructor; intro φ e' E _ _ U y H h; exact hb' S e.got hf _ _ J (funds_branch e.funds.1) U y Y hp H h
 constructor; intro β h t Y d0; obtain ⟨h1,h2,h3,h4,h5⟩:=hU _ h
 refine ⟨h1,h2,h3,h4,@fun c f S T e O A' F V k hO' hE=>?_⟩ -- rename
 have he:=h5 S T e A' F V hO' hE k; refine ⟨he,fun hl t₁ W Y' z p E _ _ _ i hv hJ r hg=>?_⟩
 let J:= hO S T e.got e.funds.1; have hS:= e.size; have hf: 2*(gun Q+1)< f.val:=by rw [S.sizes, e.got]; apply Nat.lt_of_lt_of_le _ (Nat.le_mul_of_pos_right _ Q.L.property); unfold shovel gun at *; omega
 have hX : Volo S n b D C K := by constructor; intro φ e' E _ _ U y H h; exact hb' S e.got hf _ _ J (funds_branch e.funds.1) U y C hc H h -- tune
 have hh: S.patch.L=Q.L:=congrArg RG.Patch.L e.got
 have hY: fiery G x S.patch.L ≤ min (b/2) 1:=by rw [hh]; exact hb
 refine heat (ξ:=ξ) (δ:=d) (b:=D) hn (min_le_right ..) ⟨fun v x=> hr'.cost _ (x.trans (min_le_left ..))⟩ hx (fun E _ _ f x t d b=> Hx d b) hξ (fun U N M' Xq F u θ p hV hL=> Hs S T e.got e.funds.1 _ _ _ _ _ _ _ (by unfold X; rw [←e.got]; exact u) θ p hV hL _ _ ⟨by rw [hh]; exact h1.le,hY.trans (min_le_right ..)⟩ ⟨hy.1.le,hy.2.1⟩) (fun V z h=>⟨(hI (S:=S) _ _ hy.2.1 E z h).1,(fun Y U=> (hI (S:=S) _ _ hy.2.1 E z h).2 _ _ _ U)⟩) hK hp' (zero_lt_one.trans_le ha) (le_max_left ..) _ (by rw [hh]; exact he) _ hA.le _ hX (by unfold d0 t; rw [←hh]; exact Ht S T e _ _ V hE _) e hE W hl t₁ hw hj (by rw [e.got]; omega) (hP S T e.got.symm e.funds.1) (by unfold d0 t; rw [hh]) hy.1 (by rw [hh]; exact h1) (hY.trans (min_le_left ..)) i hv hJ _ p (by rw [hh]; exact h) h2 _ hg ?_ ?_ ?_
 · rw [hh,abs_of_pos (coupling_pos h2)]; have hg:= mul_le_mul_of_nonneg_right (compare_v G Q.L x h hy').1 (show 0≤ 2^n*A*Y by positivity); apply (add_le_add_right hg _).trans; unfold Y; rw [fi] at *; refine le_trans (le_of_eq ?_) ((le_div_iff₀ hk).mp hz); unfold C'; ring
 · unfold Jet.composeCost d; exact le_of_eq (by field_simp; ring)
 unfold L; gcongr; exact hY.trans (min_le_right ..)
end YM.CF.Esti
