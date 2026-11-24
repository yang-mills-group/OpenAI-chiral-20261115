import YM.Primitives.HAAR_LOG_JETS.Guard
import YM.CF.Tarn.Bars
set_option autoImplicit false
set_option maxHeartbeats 700000
noncomputable section
namespace YM.CF.Tarn
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch MeasureTheory NormedSpace Nacre Braid Font
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius InnerProductSpace Matrix Kronecker
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open Push.Uniform (curve Slope tint partSpace meetVar)
open AnalyticBridge.Annulus1AD AnalyticBridge.SectorAffine Oriented Esti Vol Bloch Exterior Jet
open RG Forge Cay Slate Rel
open Arena
local notation "G"=> SU.group
variable {c f:Side}{S:StepData c f}{T:Tube SU.group S}{F:Forest S.ratio}{q:Chi}{s:Signed}{l n:ℕ}{x d β C D σ m:ℝ}{P:Tab S}{V:Config SU.group c}
open Cube
variable {r:ℕ}{u v W a b w s':ℝ}{i:Site c}{F:Tab S}{K:Teller G}{P': Tab S}
-- post-L
variable {T:Tube G S}{K:Teller G}{s y:ℝ}
section
variable(T:Tube G S)(v ρ:ℝ)(q:Chi)(J:ChartRatio G)(u d α:ℝ)(l:ℕ)(P:Tab S)
open Stationary Push.Loops
lemma stamps (z:Mast G c)(hz:‖z‖<1)(hj:LocalRatio J)(ht:0<u)(hV:4*u< J.radius)(hk:Fire T v P.1 P.2 l ρ n C z)(hr:Fire T v P.1 P.2 l ρ n C 0)(H:∀ (i:P.1.Free)(u':Mast G c), ‖u'‖ <1→ ‖gown T v l P i (ρ • u')‖≤ 2*u) (m t f g w:ℝ)(ht':∀ z:Mast G c, ‖z‖<1→ Medal T v t m f g w n l ρ P.1 P.2 z)(hp:0 < m)(p:Ready T v)(Q:K.Funds S T)(h:1000 ≤radiusB v): let V:=satU G ρ z; let G':= Coin T v ρ q J u d α l; let K:= Souk.golden T P.1 P.2 J q d α v l
 ∑ i,G' P i V=((K (ρ • z)-K 0):ℝ):=by
 intro V G' K; have h0: ‖(0:Mast G c)‖<1:=by simp
 let U:= satU (c:=c) G ρ; have hk': U 0=1:=by simp [U,satU,facadeX]
 let F:= P.1
 let Z(y):= Souk.tallyX T v F P.2 q d l y; let W(y):= Souk.addH F J (Souk.flute F (sol S T P.2 v F l) 1 y)
 have ha:∑ i,MossZ T v q d l J u P i V=(W (ρ • z):ℂ)-(W 0:ℂ):=by
    have hv'(y:Mast G c)(hk:Fire T v F P.2 l ρ n C y)(ht':‖y‖<1):∑ i,HWork T v q d l J u (bunk S P (U y)) i=(W (ρ • y):ℂ):= truss T v q d l J u P ρ y hk (fun i=> H i y ht') ht hV hj
    unfold MossZ; rw [sum_sub_distrib,hv' _ hk hz, ← hk', hv' _ hr h0,smul_zero] -- tune
 have he:∑ i,neatQ T v ρ q d l P i V = (Z V:ℂ) - (Z 1:ℂ):=by
    simp_rw [show ∀ i:Site c, neatQ T v ρ q d l P i V=(zestQ T v q d l P i V:ℂ) from fun i=> fruitZ T v ρ q d l z hz (fun y hy=> (ht' y hy).gap) Q hp p h]; unfold zestQ; simp_rw [Complex.ofReal_sub,sum_sub_distrib,← Complex.ofReal_sum]; rw [tallZ T v q d l P ρ (s:=0) _ _ _ _ _ z (ht' z hz),← hk', tallZ T v q d l P ρ (s:=0) _ _ _ _ _ 0 (ht' 0 h0)]  -- tune includes hp hidden
 unfold G' Coin; simp only [Pi.sub_apply,sum_sub_distrib]; rw [ha,he,rug_s T v q d α l P _ _ hk hr]; unfold K Souk.golden; simp only [Complex.ofReal_sub]; unfold W Z; rw [show facadeX G (ρ • z)=V from rfl,show facadeX G (0:Mast G c)=1 from by simp [facadeX]]; unfold F; abel -- tune
lemma nibCost(r:ℝ)(p:0 ≤ r)(n:ℕ)(f:ℕ→ℝ)(h:nib f): nib (fun i=> composeCost n (f i) r):=by
 rw [show (fun i=>_)=_ from ?_]; exact h.mul (nib_const (Jet.composeCost n 1 r) (by unfold Jet.composeCost; positivity)); funext i; unfold Jet.composeCost; ring
end
open Stationary Push.Loops
variable {K:Pressure.Teller G}
open RG Precision Pressure
structure FreshT (T: Pressure.Tube G S)(v u:ℝ)(q:Chi)(J:ChartRatio G)(t α Λ:ℝ)(n l:ℕ)(k:Tab S)(C m:ℝ):Prop where
 bonds(d:ℝ)(i:Site c): let F:= Coin T v u q J t d α l k i; CakeF F i (Cay.horn v l) n u C ∧ cFoot 2 (satX F)
 growth(y:Mast G c)(hp:‖y‖<1): FreeResolvent.Gap (baseX T v (bareStores S) k.1 k.2 (satU G u y)) m
 pureT(y:Mast G c)(hp:‖y‖<1)(d:ℝ): let f:=Souk.golden T k.1 k.2 J q d α v l; ∑ i,Coin T v u q J t d α l k i (satU G u y)= ((f (u • y)-f 0):ℝ)
-- purchase stationary cap ≤Λ all constants, chi. s selects once AFTER W. t whimsical. Real path requires downstream schedules.
lemma sant (K: Pressure.Teller G)(P:Patch)(n l:ℕ)(p:P.Branches K.bind G)(hn:3 ≤ n)(hl:l ≤18)(W:Push.Uniform.Before G K.top.width K.top.paths K.j K.bind (n+2))(X:Push.Uniform.Before G K.top.width K.top.paths K.j K.bind (n+3))(q:Chi)(J:ChartRatio G)(hj:LocalRatio J)(r Λ B:ℝ)(hr:0<r)(hZ:4*r<J.radius)(hB:0 ≤ B):∃ u f m,0<u ∧u ≤ 1∧ nib f∧0 < m ∧∀ᶠ x:ℝ in atTop,∀ {c f':Side}(S:StepData c f')(T: Pressure.Tube G S),Cert P K S T x→ T.up.Bounds T.high K.top.width K.top.paths Λ → T.down.Bounds T.low K.below.width K.below.paths Λ →∀ k:Tab S,sizedP G P K S T k.1 →∀ α, |α| ≤ B→ FreshT T x u q J r α Λ n l k (f (radiusB x)) m:=by
 obtain ⟨C,m,b,v,Q',τ,hC,hm,hb,hv,hQ,hτ,H⟩:= spitM K P p (by omega) hl X W; obtain ⟨A,e,hA,he,H'⟩:= persp K P p n l (by omega) hl X W
 obtain ⟨C',V,u',hC',hV,hu',L'⟩:=Vol.lift_paid Thera.yet_one K P p n l (by omega) W; obtain ⟨T',J',hT',hJ',U⟩:=Vol.pling K p Thera.yet_one n l hn W Λ; obtain ⟨M,I,E,hM,hI,hE,D⟩:=Vol.commercial K Thera.yet_one P p l n hn W; obtain ⟨Y,N,hY,hN,hD⟩:= Esti.rene J hj n
 let B':=max T' (B*(I+(2^n*I*I+2^n*I*I))); let C₀:= C+Q'; let A':= (Push.Uniform.shade G)* C'; let I':= min Y (2*r); let e':= min (min (min e E) (min τ u')) (min J' 1); let u:= min (I'/A') e'
 have ha:0<A':= by unfold A'; have hv:= Push.Uniform.shade_pos G; positivity
 have hh:0< I':=lt_min hY (by positivity); have he':0<e':=lt_min (lt_min (lt_min he hE) (lt_min hτ hu')) (lt_min hJ' zero_lt_one); have hx:0<u:=lt_min (div_pos hh ha) he'; have hz:u ≤ e':= min_le_right ..; have hp:u ≤ 1:=(hz.trans (min_le_right ..)).trans (min_le_right ..)
 let C₂(i):= Gems P.L i n C₀; let A₂(i):=Jet.composeCost n (C₂ i+C₂ i) (1+u⁻¹)
 let F₃:= composeCost n B' 1; let T₃:ℝ:= about P.L 0*(F₃+ F₃); let X₃:ℝ:=(Fintype.card Axis*P.L.val^4*plot 1:ℕ)*(Jet.composeCost n (Jet.composeCost n N A') 1); let F(i):=T₃+(X₃+X₃)+ A₂ i; have hv':0 ≤ N:=zero_le_one.trans hN; have ht:0 ≤ F₃:=by unfold F₃ Jet.composeCost B'; positivity
 have hX : nib C₂:= jewels _ (by unfold C₀; positivity) _ _
 refine ⟨u,F,m,hx,hp,(nib_const _ (show 0≤ T₃+(X₃+X₃) from by unfold T₃ X₃ composeCost; unfold F₃ composeCost at ht; positivity)).add (nibCost _ (by positivity) _ _ (hX.add hX)),hm,?_⟩
 filter_upwards [H,H',U,L',D,Work.E01.radiusB_tendsto.eventually_ge_atTop 1000, lamp_s.eventually (ge_mem_nhds hx), (tip_s hb).eventually (ge_mem_nhds zero_lt_one),(tip_s hv).eventually (ge_mem_nhds zero_lt_one),PatchReads.reserve K P] with x hTx hX H hU hK hR hs hy hw hu c f S T Q hp' hp'' k hr' α hΛ
 let Y:=Cay.horn x l
 have hP':=hu S T Q.got Q.size Q.funds.1; obtain ⟨F',hF',hG,hq⟩:=hU S T k.1 Q hr'; let z:= sol S T k.2 x k.1 l
 have hl : u ≤ u':= ((hz.trans (min_le_left ..)).trans (min_le_right ..)).trans (min_le_right ..)
 have hf(i v)(h:‖v‖<u):Allows n (gown T x l k i) v A' := capP T x l k i v ((hq k.2 v (h.trans_le hl)).1)
 have hS(i v)(h:‖v‖<u): ‖gown T x l k i v‖ ≤ I':=by
    have hv := miles (x:=v) (show 1 ≤ n by omega) (hf i) hx h; rw [flex (v:=0), (hq k.2 0 (by simpa only [norm_zero])).2.1, map_zero,Pi.zero_apply,sub_zero] at hv; exact hv.trans ((mul_comm ..).trans_le ((le_div_iff₀ ha).mp (h.le.trans (min_le_left ..)))) -- tune namespace
 have hz'(y)(hy:‖y‖<1):= hX.2.2.2 S T k.1 Q hr' k.2 u hs (((hz.trans (min_le_left ..)).trans (min_le_left ..)).trans (min_le_left ..)) y hy
 have hx'(y)(hy:‖y‖<1):= hTx.2 S T k.1 Q hr' k.2 u hs (((hz.trans (min_le_left ..)).trans (min_le_right ..)).trans (min_le_left ..)) y hy
 refine ⟨fun d i=> ?_,fun y p=>(hx' y p).gap,fun y p d=> stamps T x u q J r d α l k y p hj hr hZ (hz' y p) (hz' 0 (by simp)) ?_ _ _ _ _ _ hx' hm hP' Q.funds.1 hR⟩
 swap
 · intro j v h; refine (hS j (u • v) ?_).trans (min_le_right ..); rw [norm_smul_of_nonneg hx.le]; exact mul_lt_of_lt_one_right hx h
 intro F

 let X':=(hK S T k.1 Q hr' k.2)
 have hK'(s i):CakeF (tilT T x q d α l k s i) (herald S s i) Y n u (F₃+F₃):= by
    refine ⟨til_g T x q d α l Q.funds.1 _ _ _ hP' hR, priced_v T x l n α s k u hx hp i B' ?_ A hz' q d⟩
    intro y hv; obtain ⟨hV,hP⟩:= H S T k.1 Q hr' hp' hp'' k.2 s y (hv.trans_le ((hz.trans (min_le_right ..)).trans (min_le_left ..))) -- note H parameter order
    exact priced_q T x ((X' s).ears y (hv.trans_le (((hz.trans (min_le_left ..)).trans (min_le_left ..)).trans (min_le_right ..)))) hV hP α hΛ hT'.le hI.le _
 obtain ⟨h',hG'⟩:=rug_p T x q d α l k i u _ (add_nonneg ht ht) hx (by omega) (fun i s=> hK' s i)
 have ht:C ≤ C₀:=le_add_of_nonneg_right hQ.le
 have hK' : Kind S k k (pavilion Y i):= ⟨fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl,fun _ _=>rfl⟩
 have hpX: Y= Cay.horn x l:=rfl; have hZ: CakeF (MossZ T x q d l J r k i) i Y n u (X₃+X₃):=by
    refine ⟨⟨fun V g=> flash T x q d l J r hr hZ hj Q.funds.1 g k i V,fun V W h'=> paidz T x q d l J r i ?_ V W ?_ hP' hR⟩,?_⟩ -- argument radius l+76 too large? paidz radius exactly.
    · exact hK'
    · exact h'
    unfold X₃; rw [←Q.got]; exact cedar T x q d l J r k u u A' N hx le_rfl hp hr hx (fun j v hv=> ⟨hf j v hv,(hS j v hv).trans (min_le_right ..),hD.cost _ ((hS j v hv).trans (min_le_left ..))⟩) hz' ha.le hv' i
 have hY':CakeF (neatQ T x u q d l k i) i Y n u (A₂ (radiusB x)):=by
    unfold A₂ C₂; rw [← Q.got]; exact (fret T x u q d l i hx le_rfl (hC.le.trans ht) ((mul_le_of_le_one_right hC.le hw).trans ht) ht hy hw ((mul_le_of_le_one_right hQ.le hp).trans (le_add_of_nonneg_left hC.le)) hC.le hP' Q.funds.1 hR hm hx').under le_rfl (Nat.mul_le_mul_right _ (by omega)) le_rfl
 rw [Q.got] at h'; have hs:= (h'.less hZ).less hY'; refine ⟨hs,kleur F _ hs.toAtom (by omega) ?_ (hs.ledger 0 (by simpa using hx)).smooth Thera.yet_one⟩
 have hv: MossZ T x q d l J r k i 1=0:= sub_self _; have hh: satU G u (0:Mast G c)=1:=by simp [satU,facadeX]
 have hl: neatQ T x u q d l k i 1=0:=by
    rw [←hh, fruitZ T x u q d l 0 (by simp) (fun y hy=> (hx' y hy).gap) Q.funds.1 hm hP' hR]; simp only [hh,zestQ,sub_self,Complex.ofReal_zero] -- tune
 have hG : rugG T x q d α l k i 1=0:=by unfold rugG Arena.aria; simp [tilT]
 unfold F Coin; simp only [Pi.sub_apply,hG,hv,hl,sub_self] -- tune
end YM.CF.Tarn
