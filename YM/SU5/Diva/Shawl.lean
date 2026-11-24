import YM.SU5.Diva.Transom
import YM.SU5.Velvet.Heather
import YM.SU5.Velvet.Viper
import YM.SU5.Velvet.Fronds
set_option autoImplicit false
set_option maxHeartbeats 320000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py
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
open Tye Lich Stake Pail Pail.Dew
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Nor
open Chaff Gloss Maize Tye RP RP.Str
open Brace
namespace Rate
open Pitching Focus CF.Mint
namespace LocalLimit
open Preparation
variable {P:Preparation}{l:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus l))
variable {h z:ℝ}
open Buffered
open CF.Pannier.Damask
open YM.CF.Velvet
open Pannier
namespace Preparation
structure Attic (P:Preparation) : Prop where
 cut : CutFrom P.R0 P.δ P.C P.J Chi.canonical P.h P.P P.N0 P.delay
 alt (x:ℝ):∃ (w:ℝ)(N0:ℕ) (V D C:ℝ→ℝ)(Y:Prescription P.R P.block) (u:ℝ), x ≤ w ∧ 1 ≤ w ∧ Service P.V P.U P.W P.J Chi.canonical w D C V Y N0 u ∧ CutFrom V D C P.J Chi.canonical w Y N0 u
end Preparation
open Preparation
namespace Papal
structure Loft (w:ℝ) (i s k:ℕ)(G:GramM (count Y s i)) (δ:ℝ) : Prop where
 clock : G.beta=(gram Y s i k).beta
 shape : G.p=(gram Y s i k).p
 path : G.path=(gram Y s i k).path
 funds : G.funds=(gram Y s i k).funds
 tune : G.J=(gram Y s i k).J
 age : Graph.Ledger w (dleaf P.R.L (hat P.R.L P.x s)) (dleaf P.R.L (hat P.R.L P.x s)) (levelQ P.W.C) (cashU P.W.C) G
 fare : ∀ x, Rue.FleetS G.p.threshold x.1→ denZ G P.U (room Y s i) x=denZ (gram Y s i k) P.U (room Y s i) x
 gown: |(gram Y s i k).v.re - G.v.re| ≤ δ*sites (count Y s i)
open Branch
lemma acrobat (p:P.Attic)(f δ:ℝ)(u:0<δ): ∃ w, f ≤ w ∧ 1 ≤ w ∧ ∀ᶠ s in atTop,∀ i k, s≤Y.uv k → ∃ G,Loft Y w i s k G δ:=by
 obtain ⟨w,N0,V,D,C,X,y,h,t,U,hY⟩:= p.alt f; refine ⟨w,h,t,?_⟩
 have he:= redeem_time (x:=P.x) (α:=0) p.cut hY U P.H
 filter_upwards [he,(turnover P).eventually (((dev_R P.R).1.low (k:=1) (by omega)).spine.eventually (ge_mem_nhds u))] with s ht hd i k hk
 let A:= Y.voyage i; let H:= (A.X (Y.uv k)); let S0:= A.CapeT; obtain ⟨b,hb,φ,β⟩:= (A.paths (Y.uv k)).issued; have ht':=(A.paths (Y.uv k)).paid; let R:= Actual Y.meter A.funds S0 (gaugeFreq P (Y.tile*P.M)) (Y.uv k); have hr: R.start=0:=by rfl
 have hR:= ht _ _ R b ht' hb hr hk; let L:= R.gram P.P b s; let M:= R.gram X b s; have he:L=gram Y s i k:=by exact (congrFun φ s).symm
 have hy:=redeem_v (uA:=hR) (s:=hb) ht' P.H hk (zero_le_one.trans P.height) (zero_le_one.trans t); let a:=dleaf P.R.L (hat P.R.L P.x s); have h0:0<a:=(ht'.clocks s).leaf; have H': Laurel M P.K.j w a a (P.R.L.val):= (hR.1.1.mono (by change a/1000 ≤ a; linarith)).laurel .. -- tune
 let aL : Graph.Ledger w a a (levelQ P.W.C) (cashU P.W.C) M:= frostQ (H'.lot_p le_rfl le_rfl) (zero_le_one.trans t) (R.last.sound s)
 have hw:=le_trans hy (mul_le_mul_of_nonneg_right (show 2*(a/1000) ≤ δ by change a ≤ δ at hd; linarith only [h0,hd]) (zero_le_one.trans (sites_pos _)))
 refine ⟨M,by rw [←he],by rw [←he],by rw [←he],by rw [←he],by rw [←he],aL,?_ ,?_⟩
 · rw [←he]; exact fun x y=> (hR.1.2 x y).symm
 rw [←he]; exact hw
 

open YM.Gleam
lemma gauge_ae (ε:ℝ)(hε:0<ε)(κ:ℝ) : ∀ᶠ s in atTop,∀ i k:ℕ,s≤ Y.uv k → let G:= gram Y s i k; let N:=count Y s i; ∀ (f:Orbit N→ℂ)(t:ℝ), Integrable f (city N) →
 (∀ᵐ x:Orbit N ∂city N, ‖f x‖ ≤ Real.exp (-(G.path.inChannels G.funds G.p G.beta x.1) + κ*Pannier.flakes G.p.threshold x.1 + t)) → (∫ x:Orbit N,‖f x‖∂city N)≤ Real.exp (Fineness.gaugedBase P.L G.beta (More N) (P.V.L.H (Y.uv k-s))+ ε*sites N+t):=by
 filter_upwards [pilot_clock Y κ ε hε] with s q i k ht G N f t h hu
 obtain ⟨g,W,e,_⟩:= prices_plot Y s i k ht
 let ℒ:=P.K.top.clip; let H:= Real.exp t; let F(U:Pane N):=angBill G.path ℒ G.p G.beta κ U*H
 let X:= prior SU.group (More N); have hf: Integrable F X:=by
    change G.path= _ at W; unfold F; rw [W]; exact ((env_ang (P.V.L.mood (Y.uv k-s))).integrable _).mul_const _
 let kP(x:Orbit N):= F x.1; have hL:Integrable kP (city N):= ((measurePreserving_fst (μ:=X) (ν:=depot N)).integrable_comp hf.aestronglyMeasurable).mpr hf
 apply le_trans (b:=∫ u,kP u ∂city N)
 · apply integral_mono_ae h.norm hL; filter_upwards [hu] with x t; apply t.trans; change G.funds=_ at e; rw [e,Real.exp_add]; exact le_rfl
 rw [CF.Window.usesPrior _ hf]; unfold F; rw [integral_mul_const,Real.exp_add]; exact mul_le_mul_of_nonneg_right (q i k ht) (Real.exp_pos _).le

open CF.Pannier.Chancel
lemma pristineUpper {a:ℕ}(s:ℝ)(Q:Procurement P.K.j a P.d) (c:0<z)(o:z≤1)(p:0<s)(hL:SizeCloud P.K.j s z) (hp:0≤h)(p':P.Attic)(t:Geometry P)(v:ℝ):∀ᶠ j:ℕ in atTop,∀ᶠ i:ℕ in atTop,∀ k:ℕ,(Y.voyage i).kick ≤ k → j ≤ Y.uv k → ∀ (F:Mark (count Y j i)) (C:ℝ),Envelope F → reservable Y j i k h z C v F → BrokenMark Y j i k F ≤ Real.exp ((9*s)*(sites (count Y j i)) + C) :=by
 -- combination: +4 mile +2 tilt +1 gauge +1 benchmark
 obtain ⟨κ,Hk,L⟩:= earns_renewal Y Q c o s p hL
 let X:= P.W.C; obtain ⟨μ,Hμ,R⟩:= VelvetC.wisps_goal (t:=P.d) (r:=P.J.n) hp (cash_v X) P.J.ht (level_p X) p
 obtain ⟨w,hw,hl,Hw⟩:=acrobat Y p' h s p; filter_upwards [Hw, benchmarks Y s p t,L, (turnover P).eventually R,gauge_ae Y s p (κ+v+μ), (turnover P).eventually (((dev_R P.R).1.low (k:=1) (by omega)).spine.eventually (ge_mem_nhds p))] with j hV q HC ⟨n,hBudget⟩ hX W
 filter_upwards [HC,(count_grows Y j).eventually_ge_atTop n] with i H n0 k pC pA F C pZ Hz
 let B:=gram Y j i k; let N:=count Y j i; let f:= fun (x:Orbit (count Y j i))=> letterRead (F (x.1,room Y j i x)) (Graph.recX P.U (gram Y j i k) (room Y j i) x); let g:=room Y j i; let A:= Graph.recX P.U B g; let V:= sites N; let D:=sod Y k j i; let T:= P.K
 let Hv:=Y.each_level i k j pC pA; have Hf: Integrable f (city N):=mark_integrable (roofage Y i j).bill pZ ((Marks.can_read _ _ _ _ Hv).smul (Complex.exp (-B.v)))
 let b:=angleFin B.J.M N T.j
 let Hκ:=b+7*s*V+C; obtain ⟨J,Tj⟩:=hV i k pA; have htY := (Y.voyage i).paths k; have Ht:= htY.paid.can.isle j; obtain ⟨hx,vB,gV,hH,h'⟩:=prices_plot Y j i k pA; have hJ:J.p.threshold=B.p.threshold:=congrArg _ Tj.shape;
 have hc:∀ᵐ x:Orbit N ∂city N, ‖f x‖≤ Real.exp (-(B.path.inChannels B.funds B.p B.beta x.1) + (κ+v+μ)*flakes B.p.threshold x.1+Hκ):= by
    filter_upwards [ae_fleet (n:=N) (show Rue.IsleB SU.group J.p.threshold from (by rw [Tj.shape,hx]; exact Ht))] with x HX; -- tune
    have heX:= speck Y j i k pA; let Z:= (v*flakes B.p.threshold x.1+C); let D':=trade (spar T.j B.J.M (g x)) (tickA N) z; let E:=Real.exp (D'+Z); let k':=flakes B.p.threshold x.1; let R':= (4*s)*V+μ*k'
    have hm:=hBudget (roofage Y i j) w _ _ P.K.j Tj.age hw n0 W W x (Tj.tune.symm ▸ (safety Y j i k x).1 : IsStarProjection (spar T.j J.J.M (g x))); rw [←heX] at hm; let f':=F (x.1,g x); let Y':= Graph.beam J P.U g x; let b':= mateK N; have hy': Yep h (acts (star f') b') (changeM P.U (g x) B.J.M) E:=by
       specialize Hz x; unfold E Z; rw [←add_assoc]; exact Hz
    have ht := Yep.val (show Yep h _ Y' (Real.exp R'*E) from hm.2 (acts (star f') b') (changeM P.U (g x) J.J.M) E (Real.exp_pos _).le (Tj.tune.symm ▸ hy'))
    have hy : D' ≤ b+2*s*V+κ*k':= H k pA x; let a:= Graph.past J x.1; let r:= J.v - B.v; have he: Graph.recX P.U B g x= Complex.exp r • Graph.recX P.U J g x:=by
       unfold Graph.recX; rw [Tj.fare x HX, smul_smul,← Complex.exp_add,show r + -J.v= -B.v by unfold r; ring]
    change ‖letterRead f' (Graph.recX P.U B g x)‖ ≤_; rw [he, Graph.porch, map_smul, (letterRead _).map_smul_of_tower,norm_smul,Complex.norm_exp,norm_smul, Real.norm_of_nonneg (r:=a) (Real.exp_pos _|>.le)]; change _*(a*‖inner ℂ b' (acts f' Y')‖) ≤ Real.exp _; rw [← act_inner]
    apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht (Real.exp_pos _|>.le)) (Real.exp_pos _|>.le)).trans; unfold E; rw [←Real.exp_add,← Real.exp_add,← Real.exp_add]; apply Real.exp_monotone
    have hs:r.re≤ s*V:= (show r.re ≤ |B.v.re-J.v.re| from (by dsimp [r]; simp_rw [abs_sub_comm B.v.re]; exact le_abs_self _)).trans Tj.gown
    rw [Tj.path,Tj.shape,Tj.clock,Tj.funds]; unfold Z R' Hκ; change r.re+(-(_ : ℝ)+(( (4*s)*V+μ*k')+(D'+(v*k'+C)))) ≤ - (_:ℝ) + (κ+v+μ)*k'+(b+7*s*V+C); linarith only [hy,hs]
 change (∫ i, ‖f i‖ ∂_)/_ ≤_;
 let μ':= Real.exp (D-s*V); let Z:= ‖vac0 P.U B g‖; let m:= Real.exp ((9*s)*V+C)
 have he: μ'≤Z:=q i k pC pA; have ha: Z>0:= (Real.exp_pos _).trans_le he; refine (div_le_iff₀ ha).2 ?_; refine (hX i k pA f Hκ Hf hc).trans ((mul_le_mul_of_nonneg_left he (Real.exp_pos ((9*s)*V+C)|>.le)).trans' ?_)
 apply le_of_eq; rw [←Real.exp_add]; let Hψ:= Fineness.gaugedBase P.L B.beta (More N) (P.V.L.H (Y.uv k-j)); change Real.exp (Hψ+s*V+ Hκ)=Real.exp _; rw [show D=Hψ+b from rfl]; unfold Hκ; congr 1; ring
end Papal
end LocalLimit
end Rate
end YM.CF.Py
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.acrobat
#print axioms YM.CF.Py.Rate.LocalLimit.Papal.pristineUpper
