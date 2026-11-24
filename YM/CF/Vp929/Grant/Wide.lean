import YM.CF.Stake.Pilot
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
theorem ticketVolume(P:Teller G)(Q:Patch)(h:Q.Branches P.bind G) (n j l:ℕ)(hn:3 ≤ n)(hj:2 ≤ j)(hl:l ≤18)(W:Push.Uniform.Before G P.top.width P.top.paths P.j P.bind n)(W':Push.Uniform.Before G P.top.width P.top.paths P.j P.bind (n+2))(q:Chi)(S':ChartRatio G)(hp:LocalRatio S') (w width γ y':ℝ)(hw:0<w)(hy:0<width):∃ A B C D M L u m K s M1 D1:ℝ,0<A ∧0<B ∧1 ≤ C ∧0 ≤ D ∧1 ≤ M ∧0 ≤ L ∧0<u∧1 ≤ m ∧0≤K∧0< s∧1 ≤ M1 ∧ 1 ≤ D1 ∧∀ᶠ x in atTop, fiery G x Q.L ≤ s/2 ∧ (∀ {c f:Side}(S:StepData c f)(T:Tube G S),Cert Q P S T x→∀ Cx:ℝ,1 ≤ Cx→ Volo S n s D1 Cx (covetM G n Cx M1 D1)) ∧ ∀ b, B≤b→ b≤16*B → Ticket P Q q S' n j l w width γ y' x A b C D M L u m K s :=by
 obtain ⟨A,B,hA,hB,H⟩:= wind P Q h n l W' q width hy (by omega) hl; obtain ⟨s,D,h',hd,hO⟩:= strut G n P Q W hn; obtain ⟨u',m,hv',hm,hr'⟩:=rene S' hp n
 let u:=min u' 1; have hu:0<u:=lt_min hv' zero_lt_one
 obtain ⟨ξ,hξ,hI⟩:=tock n; let C:=max ξ ‖(1:SU.group.Mat)‖; have hc:1 ≤ C:=hξ.trans (le_max_left ..)
 obtain ⟨b,M,hb,hM,hb'⟩:=bindsM G n s D h' hd Q
 let K:=covetM G n C M D; have hK:0 ≤ K:=by unfold K covetM Jet.composeCost dressM purM; have hh:= SU.group.colorScale_pos; positivity
 obtain ⟨G',hx,Hx⟩:= currencyT q n; let X:=purM G n*C*horse Q n C b G' K; obtain ⟨X',X''⟩:= Push.Uniform.paint_supply G n; obtain ⟨B',hp',Hs⟩:= scope_p P Q X' X C (by unfold X horse purM; have hg:= SU.group.colorScale_pos; have hd:1 ≤ max 1 (zest n * dam G n (b/2) G' C):=le_max_left ..; positivity) (le_max_right ..) n X''
 obtain ⟨a,ha,Hw⟩:= owns P Q q n width hy h
 let d:= u/(Push.Uniform.shade G*((n.factorial:ℝ)* (1+1:ℝ)^n)); let L:= a*(d+1); have hL:=Push.Uniform.shade_pos G; have ht:0<d:=by unfold d; positivity
 let C':= A+2*(2^n*A*(16*B)); have hk:0<C':=by unfold C'; positivity
 refine ⟨A,B,C,B',G',Jet.composeCost n L 1,u,m,K,b,M,D,hA,hB,hc,hp',hx,(by unfold Jet.composeCost L; positivity),hu,hm,hK,hb,hM,hd,?_⟩
 filter_upwards [H,Hw,order_r P Q,monitors G Q.L, (year G Q.L).eventually (eventually_gt_atTop 0), expM Q (hp:=lt_min (half_pos hb) zero_lt_one), expM Q (hp:=div_pos ht hk), Work.E01.radiusB_tendsto.eventually_ge_atTop (10*shovel Q+100)] with x hU Ht hP hy hy' hb hz hq
 refine ⟨hb.trans (min_le_left ..),?_,?_⟩
 · intro c f S T e Y hp
   let J:= hO S T e.got e.funds.1; have hS:= e.size; have hf: 2*(gun Q+1)< f.val:=by rw [S.sizes, e.got]; apply Nat.lt_of_lt_of_le _ (Nat.le_mul_of_pos_right _ Q.L.property); unfold shovel gun at *; omega
   constructor; intro φ e' E _ _ U y H h; exact hb' S e.got hf _ _ J (funds_branch e.funds.1) U y Y hp H h
 intro bb Hbb bbH
 constructor; intro β h t Y d0; obtain ⟨h1,h2,h3,h4,h5⟩:=hU _ h
 have hiY:B*Scales.p G Q.L x ≤ Y:=mul_le_mul_of_nonneg_right Hbb (Scales.pos G Q.L x).le
 refine ⟨h1,h2,h3.trans_le hiY,h4.trans hiY,@fun c f S T e O A' F V k hO' hE=>?_⟩
 have he:=h5 S T e A' F V hO' hE k; refine ⟨he,fun hl t₁ W Y' z p E _ _ _ i hv hJ r hg=>?_⟩
 let J:= hO S T e.got e.funds.1; have hS:= e.size; have hf: 2*(gun Q+1)< f.val:=by rw [S.sizes, e.got]; apply Nat.lt_of_lt_of_le _ (Nat.le_mul_of_pos_right _ Q.L.property); unfold shovel gun at *; omega
 have hX : Volo S n b D C K := by constructor; intro φ e' E _ _ U y H h; exact hb' S e.got hf _ _ J (funds_branch e.funds.1) U y C hc H h
 have hh: S.patch.L=Q.L:=congrArg RG.Patch.L e.got
 have hY: fiery G x S.patch.L ≤ min (b/2) 1:=by rw [hh]; exact hb
 refine heat (ξ:=ξ) (δ:=d) (b:=D) hn (min_le_right ..) ⟨fun v x=> hr'.cost _ (x.trans (min_le_left ..))⟩ hx (fun E _ _ f x t d b=> Hx d b) hξ (fun U N M' Xq F u θ p hV hL=> Hs S T e.got e.funds.1 _ _ _ _ _ _ _ (by unfold X; rw [←e.got]; exact u) θ p hV hL _ _ ⟨by rw [hh]; exact h1.le,hY.trans (min_le_right ..)⟩ ⟨hy.1.le,hy.2.1⟩) (fun V z h=>⟨(hI (S:=S) _ _ hy.2.1 E z h).1,(fun Y U=> (hI (S:=S) _ _ hy.2.1 E z h).2 _ _ _ U)⟩) hK hp' (zero_lt_one.trans_le ha) (le_max_left ..) _ (by rw [hh]; exact he) _ hA.le _ hX (by unfold d0 t; rw [←hh]; exact Ht S T e _ _ V hE _) e hE W hl t₁ hw hj (by rw [e.got]; omega) (hP S T e.got.symm e.funds.1) (by unfold d0 t; rw [hh]) hy.1 (by rw [hh]; exact h1) (hY.trans (min_le_left ..)) i hv hJ _ p (by rw [hh]; exact h) h2 _ hg ?_ ?_ ?_
 · rw [hh,abs_of_pos (coupling_pos h2)]; have Hy:Y>0:=h3.trans_le hiY; have hg:= mul_le_mul_of_nonneg_right (compare_v G Q.L x h hy').1 (show 0≤ 2^n*A*Y by positivity); apply (add_le_add_right hg _).trans; unfold Y; rw [fi] at *; refine le_trans ?_ ((le_div_iff₀ hk).mp hz); have H:=mul_le_mul_of_nonneg_left bbH (by have:=Scales.pos G Q.L x; have:=Scales.gauge G Q.L hy'; positivity : 0 ≤ (2*Scales.g G Q.L x) * (2^n*A*Scales.p G Q.L x)); unfold C'; linarith only [H]
 · unfold Jet.composeCost d; exact le_of_eq (by field_simp; ring)
 unfold L; gcongr; exact hY.trans (min_le_right ..)
end YM.CF.Esti
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Reine
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree Esti
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
open Forge
lemma melonVolume (P:Teller G)(Q:Patch)(h:Q.Branches P.bind G) (n j l:ℕ)(hn:3 ≤ n)(hj:4 ≤ j)(hl:l ≤18)(W:Push.Uniform.Before G P.top.width P.top.paths P.j P.bind n)(W':Push.Uniform.Before G P.top.width P.top.paths P.j P.bind (n+2))(q:Chi)(R:ChartRatio G)(hp:LocalRatio R)(w γ:ℝ)(hw:0<w)(hγ:0<γ):∃ N:ℝ,1≤N∧∀ width≥N,∃ A B s M M':ℝ,0<A ∧0<B∧0<s∧1≤M∧1 ≤ M' ∧ ∀ᶠ x:ℝ in atTop, ∀ b, B ≤ b → b ≤ 16*B → Erin P Q R n j l q w width γ x A b s M M' :=by
 obtain ⟨N,hN,Hn⟩:=help P Q h hp w γ hw hγ; refine ⟨N,hN,fun width vy=>?_⟩; have hi:0<width:=zero_lt_one.trans_le (hN.trans vy)
 obtain ⟨A,B,C,D,M,L,u,m,K,s,h₁,h₂,hA,hB,hC,hD,hM,hL,hu,hm,hK,hs,hp₁,hp₂,H⟩:= ticketVolume P Q h n j l hn (by omega) hl W W' q R hp w width γ 0 hw hi
 obtain ⟨D',hv',ht'⟩:= owns P Q q n width hi h
 refine ⟨A,B,s,h₁,h₂,hA,hB,hs,hp₁,hp₂,?_⟩; filter_upwards [H,Hn width vy 0 j n, payer Q n j w width C D M L u m K s hγ hD hL, capable P Q, ht', pauce R hp (γ/16) (by positivity) Q j,(Scales.peak G Q.L).eventually_ge_atTop (1/B), Work.E01.radiusB_tendsto.eventually_ge_atTop (shovel Q +100), eventually_gt_atTop (0:ℝ)] with x hx Hx hx' he ht hp' hv hq hz bm pmb bMP
 refine ⟨Hx,hx.2.1, fun β v=>?_⟩; intro t d Y L'; obtain ⟨h1,h2,h3,h4,h5⟩:=(hx.2.2 bm pmb bMP).wear _ v; have hY':=hp' Y (show 1 ≤ Y from (le_of_eq (by field_simp : (1:ℝ)=B*(1/B))).trans ((mul_le_mul_of_nonneg_left hv hB.le).trans (mul_le_mul_of_nonneg_right pmb (Scales.pos G Q.L x).le))) β v
 refine ⟨h1,hx.1,h2,h3,hY'.1,h4,@fun c f S T p A' F e=>?_⟩; have hW:=h5 S T p; refine ⟨(hW A'.key A'.key A'.park A'.V A'.k F e).1,fun p₁ p₂ ℓ κ r b=>?_⟩; intro a; have hs₀:=ht S T p A'.key A'.park A'.V e A'.k; dsimp only at hs₀; rw [p.got] at hs₀; have hh:t=fiery G x S.patch.L:=by rw [p.got]
 obtain ⟨u',x'⟩:= he _ _ p.got p.funds.1
 constructor
 · intro α; let X:=max 1 SU.group.colorScale; have hp:= hx.2.1 S T p X (le_max_left ..); exact plunge _ _ _ _ _ _ _ p₁ p₂ _ _ R w s L' r j α p (D:=X) (fun i=> (gan _).mono (le_max_right ..)) (by rw [p.got]; omega) hp (hh ▸ h1) (by rw [p.got]; exact hx.1) e hY'.1.ne' b (by unfold taxM Stores.till; have ht:=Nat.mul_le_mul_right (radiusB x) hj; omega) h2 (ℓ.trans hh) κ u' x' (Work.E09.temp_pos hz) (congrFun hs₀.1 _)
 intro Dp h i g E _ _ _ z hz hp; have hI:0 < i.val.shares:= (vase_d S i.val ▸ card_pos.mpr i.property.1)
 let R':=Real.exp (-γ/8*(Scales.p G Q.L x)^2*i.val.shares)
 have hy:Allows n (fun x':E=> (A'.atop (z x') x).pep x T s i.val q d l β w R j) 0 R':=by
    apply Allows.mono ((hW i.val A'.key A'.park A'.V A'.k F e).2 g Dp Hx (A'.bush x) (A'.bell x) ((pi_norm_le_iff_of_nonneg h3.le).mpr fun v=> (norm_le_pi_norm A'.z v.val.val).trans h) E z hz hp (latticeFieldEstimates i.val j x) (fun i=> by exact_mod_cast vault j)); exact hx' S p.got A'.key i.val hI A'.park β v
 let t':=trig ((j+100)*radiusB x) i.val; let Q':=t'*L'⁻¹^ Fintype.card (Frozen i.val x A'.park); apply Allows.mono ((hy.smul Q').germ ?_)
 swap
 · apply Eventually.of_forall; intro a; unfold treat; change Q'*_=(_*t')*L'⁻¹^ Fintype.card (Frozen i.val x A'.park); unfold Q'; ring
 exact (mul_le_mul_of_nonneg_right (hY'.2 S p.got A'.park i.val) (Real.exp_pos _).le).trans_eq (by rw [←Real.exp_add]; congr 1; ring)
end YM.CF.Reine
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Stake
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Hom Vale Vale.Grace Next.Free Thera Nacre Dial Fock
open Tye Lich
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L) (O:Acorn.Repair K.j){U:Grasp V.U B d}(W:GivenX V U)
local notation "G5"=>SU.group
abbrev Dilation:= Set.Icc (1/16:ℝ) 1
def Pilot.zoom (F:Pilot)(r:Dilation):Pilot:={F with large:=r.val*F.large,high:=mul_pos ((by norm_num:0<(1/16:ℝ)).trans_le r.property.1) F.high}
@[simp] lemma Pilot.zoom_one (F:Pilot): F.zoom ⟨1,by constructor<;>norm_num⟩=F:=by cases F; unfold zoom; simp only [one_mul]
structure WideFire (L:ChartRatio SU.group)(q:Chi)(D:Pilot)(R:Patch)(K:Teller SU.group)(l k j:ℕ)(x:ℝ):Prop where
 fire (a:Dilation): FireK L q (D.zoom a) R K l k j x
lemma WideFire.master {q:Chi}{F:Pilot}{x:ℝ}(h:WideFire L q F R K l k j x): FireK L q F R K l k j x:=by simpa using h.fire ⟨1,by constructor<;>norm_num⟩
lemma flyingVolume(K:Teller G5)(R:Patch)(p:R.Branches K.bind G5)(vu:∀ᶠ w:ℝ in atTop,∃ u:ℝ,0<u ∧ K.cash R.L w u)(Q:LocalRatio L)(k j l:ℕ)(h:4≤ j)(w:3≤ k)(p':l ≤18) (q:Chi):∃ D:Pilot,∀ᶠ x:ℝ in atTop, WideFire L q D R K l k j x:=by
 obtain ⟨i,y,a,b,f⟩:= Cloak.anchor K R p k l (by omega) p' q (before_t K _ (by omega)); obtain ⟨T,H⟩:= eventually_atTop.mp vu; let A:= max y T; have hh:0<A:= b.trans_le (le_max_left ..)
 obtain ⟨c,t,Y⟩:= H A (le_max_right ..); obtain ⟨N,v,N'⟩:=melonVolume K R p k j l w h p' (before_t K _ w) (before_t K _ (by omega)) q L Q A c hh t
 let U:= max i N; have hx:0<U:= a.trans_le (le_max_left ..)
 obtain ⟨J,M,s,D,D',hj,hM,hs,I,hD,Hy⟩:= N' U (le_max_right ..); obtain ⟨g,z,G⟩:=f J s hj hs; let g':= L.radius/8; have hz:= Q.patch; have h₁:0<g':= div_pos hz (by norm_num)
 obtain ⟨m',v',H'⟩:=turnsX (k+8) l U hx K R p (by omega) p' (before_t K _ (by omega)) q
 let P':Pilot:=⟨A,c,U,J,16*M,s,D,D',g,g',m',v',hh,t,v.trans (le_max_right ..),hj,mul_pos (by norm_num) hM,z,hs,h₁⟩; let x':=min g' (firstRadius G5/4); have ht:Tendsto (fun x=>U*fiery G5 x R.L) atTop (𝓝 0):=by have he:=(tally_g G5 R.L 0 1).const_mul U; rw [mul_zero] at he; apply he.congr; intro i; rw [fi]; ring
 have hu:x'<firstRadius G5:= lt_of_le_of_lt (min_le_right ..) (by linarith [first_pos G5]); have hv:4*g'<L.radius:=by unfold g'; linarith
 refine ⟨P',?_⟩; filter_upwards [Y.late, H', Hy, PatchReads.reserve K R,Reine.capable K R,(year G5 R.L).eventually_gt_atTop 0,G,ht.eventually (ge_mem_nhds (show 0<x' from lt_min h₁ (div_pos (first_pos _) (by norm_num)))),Work.E01.radiusB_tendsto.eventually_ge_atTop (shovel R+1000),eventually_gt_atTop (0:ℝ)] with x Hh hh hx₀ H R' v G k' hy hu'
 have hv':0<fiery G5 x R.L:=by rw [fi]; exact mul_pos (Scales.gauge _ _ v) (Scales.pos ..)
 have hl:U*fiery G5 x R.L ≤g':=k'.trans (min_le_left ..); have hy':U*fiery G5 x R.L ≤ firstRadius G5/4:= k'.trans (min_le_right ..)
 constructor; intro alp
 specialize hx₀ (alp.val*(16*M)) (by nlinarith [alp.property.1]) (by nlinarith [alp.property.2])
 refine ⟨hv',by omega,by omega, (mul_le_mul_of_nonneg_left hl (by norm_num : 0 ≤ (4:ℝ))).trans_lt hv,hl,hv,hu',show 2*(U*_)< _ from by linarith [first_pos G5], hx₀,?_⟩; intro N S B Z' T e; have hx:= e.funds.1
 obtain ⟨π,S'⟩:= R' Z' T e.got hx
 refine ⟨?_,H _ _ e.got e.size hx,π,S',fun M w h=> ⟨?_,?_⟩⟩
 · let hp:=congrArg RG.Patch.L e.got; intro I U V W Y p v; rw [hp]; exact Hh _ _ Z' hp e.size T hx _ _ _ _ _ p v
 · have he:=hh _ T e M.key M.park M.V w h M.k; rw [e.got] at he; exact he
 intro β v y'; obtain ⟨_,_,_,_,_,_,p⟩:= hx₀.heat β v; exact G _ T e U (le_max_left ..) A (le_max_left ..) M h w β v y' (p Z' T e M w h).1
end YM.CF.Stake
