import YM.CF.DPress.Yarn.Table
import YM.CF.DPress.Calendar.Elm
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 1600000
noncomputable section
namespace YM.CF.Py.Kay
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
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Siete PhysicalNext.JointLoad.Heir Vow
open AnalyticBridge.VerifiedReset
open DPress DPress.Fees Finance Rosy
open scoped YM.CF.Mew
open Oise Larch  Bake
open Sour Tap Heath Tutor Docket Resident Campus Flight Moral Rosy
open Act Harvester WagesC Urban
namespace FitD
variable {B:Side}{K:Teller SU.group}{R:Patch}{L:ChartRatio SU.group} {d:ℝ} {V:Grace K R L} {U:Grasp V.U B d}{W:GivenX V U}
 {M':Side} {J:Robes M' V W}{C:Tew W}{P_:Campus C}
 {x:ℝ}{A:Harvester P_}
variable {M:Side}{n i j k:ℕ}{Δ :ΛFit P_ x}{Λ:Thrift A}
open Chaff Gloss Maize Tye RP RP.Str Brace
-- keep auxiliaries cert $before h$.
structure TheScroll (B:Side)(d:ℝ) where
 θ : ℝ
 α : ℝ
 β : ℝ
 pθ: 0<θ
 pA: 0<α
 pB: 0<β
 budget: Budget B d θ
 F:(m:Side)→ Scroll m B (Brace.northZ m B)
 H(m):ScaleK α β (F m)
abbrev Consigns (S:Source P_ J)(b:ℕ)(T:TheScroll B d):Prop:= S.b=b∧ S.F0=T.F ∧ S.θFp=T.θ∧ S.a0=T.α∧ S.t=T.β
structure Harbor (C:Tew W) (P_: Campus C) (A: Harvester P_) (S: Source P_ J)(b:ℕ)(T:TheScroll B d) (h w:ℝ) (p k:ℕ) (q:Chi)(μ:ℕ)(CP CD:ℝ):Prop where
 co : Consigns S b T
 aMu : A.μ=μ
 wR : C.w=w
 hR : C.h=h
 pR : C.p=p
 kR : C.i=k
 qR : C.q'=q
 an : Align C J
 CP_offer : Coffer (p:=p) (k:=k) V U W q w J.d J.n CP (Ntop P_) J.k J.roomX h
 CD_price : A.C_D=CD
 CP_r : CP/(R.L.val:ℝ)≤1/4
 size_l : 20*μ < R.L.val
 η : ηD (A:=A)≤1/4
private lemma spaciousD (μ:ℕ)(a b:ℝ):∃ N:ℕ,∀ R:Side,N≤ R.val→ a/(R.val:ℝ)≤1/4 ∧ b*(R.val:ℝ)⁻¹≤1/4∧ 20*μ < R.val:=by
 obtain ⟨n,h⟩:= exists_nat_gt (4*a); obtain ⟨k,p⟩:= exists_nat_gt (4*b); refine ⟨n+k+20*μ+1,fun R t=>?_⟩; have hw:0<(R.val:ℝ):=by positivity
 refine ⟨?_,?_,by omega⟩; · rw [div_le_iff₀ hw]; have he:=(h.trans_le (Nat.cast_le.mpr (show n ≤R.val from by omega))); linarith
 rw [← div_eq_mul_inv,div_le_iff₀ hw]; have he:=(p.trans_le (Nat.cast_le.mpr (show k≤R.val from by omega))); linarith
abbrev liftH(x:ℝ):= 32*Cad.rent*x
lemma liftH_u{p x h:ℝ}{P:BudgetPoint}(t:0<p)(v:lobe (liftH p) h x P) : lobe p h x P:= by
 refine v.trans ?_; have he:=desire P t; have hz: tiltB p P ≤ tiltB (liftH p) P:=by
    rw [show tiltB (liftH p) P=32*Cad.rent*tiltB p P from (by unfold tiltB liftH; ring)]; exact le_mul_of_one_le_left he.le (by linarith [Cad.rent_p])
 apply div_le_div_of_nonneg_left (by positivity) (mul_pos (by norm_num) he) (mul_le_mul_of_nonneg_left hz (by positivity)) -- tune
-- argument d-Gate `Lease≤ before cap` caller chooses after `λ` and `B`, `BPress.MaskTime` obtains. `z` prior issue.
lemma market_H (j k p μ:ℕ)(w:ℝ)(ht:6≤k)(hp:2≤p)(hb:4≤j)(u:Even j)(ha:0<w):
  ∃ (K:Teller SU.group)(L:ChartRatio SU.group),K.j=j ∧ LocalRatio L ∧ K.top.clip.direct≤1 ∧ (∀ P:Patch,P.Branches K.bind SU.group) ∧∃ (C C_D:ℝ)(N:ℕ),∀ (P:Patch),N ≤ P.L.val → P.J=j→ ∃ (V:Grace K P L)(T:Acorn.Repair K.j)(l:ℕ),0< l ∧∀ B:ℕ,l ≤ B → ∃ e yP:ℝ,0<yP∧0<e ∧∀ q:Chi,∀ d:ℝ,0<d→ d ≤ e →∃ (U:Grasp V.U (P.L^B) d)(W:GivenX V U)(M:Side)(J:Robes M V W),W.pearl.q=yP ∧ U.baseline ≤ T.d ∧ J.k≤ J.roomX ∧ Embark J ∧ ∃ T:TheScroll (P.L^B) d,∀ᶠ h:ℝ in atTop,∃ (X:Tew W)(P_:Campus X)(Φ:Harvester P_)(S:Source P_ J),Harbor X P_ Φ S B T h w p k q μ C C_D :=by
 obtain ⟨K,L,ζq,P0,hK,Br,C,Z,A,κ,N,Y⟩:= elm_D j k p w ht hp hb u ha
 have hu: Even K.j:= ζq.symm ▸ u; let Q:= Classical.choice (waver K.j p (by omega) hp hu)
 obtain ⟨Aχ,uA,Dχ⟩:= Taxi.ori_u k; obtain ⟨Γχ,hQ,DG⟩:= Taxi.psalmB k
 obtain ⟨Wk,tW,wT⟩:= Haro.nova; let Yv:= pond_X k p w ht hp ha; let CE:=Beau.tax_E Yv K.below.clip K.below.width K.below.paths Aχ Γχ; let Cu:=(CE + 1)*νC Yv Wk*ray_T p k Z w Q.C 1
 -- price.C across h,λ.
 let κΩ:= 1+(1+3*|ρtax Γχ μ Yv|+|Blend.ζP Yv Γχ μ|)*‖Complex.reCLM‖
 let Xc:= Tew.Prep k p w Z Q.C; let Dℝ:= max 1 ((CE+1+1)*κΩ * (4*(Xc+1)*(2+16*tiltB Wk Yv*Tutor.Sp Yv))); obtain ⟨M,hM⟩:= spaciousD μ Cu Dℝ
 obtain ⟨Br',hr⟩:= Chaff.coat_H k p (by omega); refine ⟨K,L,ζq,P0,hK,Br,Cu,Dℝ,M+N,fun L tX hL=>?_⟩
 obtain ⟨uτ,hτ,vτ⟩:= hM L.L (by omega); obtain ⟨V,T,i,tQ⟩:=Y L (by omega) hL; refine ⟨V,T,i+Br'+1,(by omega),fun b v=>?_⟩
 have hp2:= V.tallX; obtain ⟨e1,e2,Pt⟩:=hr (L.L^b) (le_trans (show Br' ≤ b from by omega) (Vale.huge _ (by omega) _)); obtain ⟨e,y,hp',u,P⟩:= tQ b (by omega); have jk:1≤K.j:=by omega
 obtain ⟨d,a',b0,c0,hδ,ht',hz,hW,n2,M⟩:=ores V Yv (liftH Wk) jk (by unfold liftH; have h:=Cad.pos; positivity)
 refine ⟨min e (min d e1),y,hp',lt_min u (lt_min hδ e2),fun q e' t lE=>?_⟩
 obtain ⟨U,W,M',J,Uφ,p_,WQ,x,l⟩:=P q e' t (lE.trans (min_le_left ..))
 obtain ⟨qX,κ0,Jp,hU⟩:=l; obtain ⟨Y0,a0,t0,u0,zP,g,WZ,F0,hζ,pZ⟩:=Pt e' t (lE.trans ((min_le_right ..).trans (min_le_right ..))) L K _ V U W.pearl V.note jk hK; let T_:TheScroll (L.L^b) e':=⟨Y0,a0,t0,u0,zP,g,WZ,F0,hζ⟩; have hp3:J.roomX≤ d:= (J.hr.le.trans (lE.trans ((min_le_right ..).trans (min_le_left ..))))
 refine ⟨U,W,M',J,Uφ,p_,x,WQ,T_,?_⟩; filter_upwards [hU 3,eventually_ge_atTop (1:ℝ),hW] with H h t wH
 obtain ⟨F,Z',n,Vv,ηp,Aq,ε⟩:=h; have h0:=ore_M V U W q q J.k w J.roomX J.d J.hr J.ht x J.n qX C κ Jp F Z' n H t 3 Z Vv ε
 have htX:=ore_B V U W q q J.k w J.roomX J.d J.hr J.ht x J.n qX C κ Jp F Z' n H t 3 Z Vv ε
 let X:Tew W:=⟨p,k,105,5,C,J.k,J.roomX,J.d,H,w,A,Vv,Z,κ0,J.n,n,q,q,Z',F,Q,qX,κ,Jp,ηp,Aq,x,J.hr,J.ht,t,P0,h0⟩; let P':Campus X:=⟨ht,hp,ha,Wk,a',b0,c0,d,n2,tW,wT,ht',hz,hp3,jk,M,wH⟩; let Tφ:Harvester P':=⟨hK,μ,Γχ,Aχ,hQ,uA,Dχ,DG⟩
 have wK:= liftH_u tW wH; have hv:= tree_PS (U:=U) V U W P0 q q J.k w J.roomX J.d Aq ha ht hp J.hr J.ht x J.n qX C κ Jp F Z' n H t 3 Z Vv hK Q Aχ Γχ Dχ DG uA hQ Wk a' b0 c0 d n2 hp3 jk tW wT M ht' hz wK ηp (by omega) h0
 have hm:=tree_BP (U:=U) V U W P0 q q J.k w J.roomX J.d Aq ha ht hp J.hr J.ht x J.n qX C κ Jp F Z' n H t 3 Z Vv hK Q Aχ Γχ Dχ DG uA hQ Wk a' b0 c0 d n2 hp3 jk tW wT M ht' hz wK ηp (by omega) htX; have he:=tree_L (U:=U) V U W P0 q q J.k w J.roomX J.d J.hr J.ht x J.n qX C κ Jp F Z' n H t 3 Z Vv htX
 obtain ⟨ZK,pK,TK⟩:= pZ w H t; have hu:SunK V w p k J H ZK F0:=by refine ⟨?_⟩; filter_upwards [TK] with x p c T R hx ht u t b' B; exact p c T R J.k J.roomX J.n ht u hx t b' J.hr B
 let S':Source P' J:=⟨b,_,Y0,a0,t0,u0,zP,g,WZ,rfl,(by omega),F0,hζ,ZK,hu,pK,he,hm⟩
 exact ⟨X,P',Tφ,S',⟨⟨rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl,rfl,rfl,rfl,rfl,⟨rfl,rfl,rfl,rfl⟩,hv,rfl,uτ,vτ,hτ⟩⟩
end FitD
end YM.CF.Py.Kay
