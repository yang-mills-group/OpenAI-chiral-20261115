import YM.SU5.LitCurrent.Puff
import YM.SU5.Exchange.Pace.Cult
import YM.SU5.Selected.Nord.Regime
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 24000
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
open YM.CF.BPress (PL NPL)
variable {F G:ℝ→ℝ}
open Vow Sour Swell Ione
namespace Rate
namespace LocalLimit
open Jet
namespace Preparation
open FullBill Window Marks
open Pitching Focus QuadClock
variable {P:Preparation}{F:(s:Side)→Scree.Loom s→Prop}(Y:Course P F)
local notation "tape" i:max=> (Y.voyage i)
local notation "Coord" i:max k:max=> (tape i).X (Y.uv k)
variable {Pay ξC Γϕ:ℝ}{n u:ℕ}{Tξ:Hove.Grant P.K.j 2}
variable (flag:∀ i k, ((Y.voyage i).X k).Prepared P.P P.delay)
local notation "xt" => hat P.R.L P.x
local notation "Aκ" v:max=> Y.meter.a v
local notation "Rt" i:max k:max s:max => (RootBook Y i k s)
local notation "Ω" i:max k:max=> cell (Y.ir i) P.block P.R.L k
open LitCurrent
private lemma foreHand (P:Preparation) (N:Side)(Q:GramM (mid N P.block))(u:InterestX P.W.C _ Q.J)(p:P.U.roundZ ≤ (mid N P.block).val): Permission (funde P.K.j Q.J.M _) (Moire.bloom Q.J.P) P.d:=by
 refine ⟨((rosterly P _ Q u p).projection), ?_,?_⟩ -- tune proof
 · intro s V h; let U:=spinU s.charge s.s; let he:= spinZ s.charge s.s
   let f:=P.V.note.fields_one (mid N P.block) (P.U.needed.trans p)
   exact funde_f _ _ _ he _ _ (hOne P) _ _ f (h.shrink P.U.gem)
 intro s V h; let he:= Levier.prism_x s.charge (castX s) Q.J.P u.leanJ.1 u.ready V (spinU s.charge s.s) (show JetS (castX s).s s.charge (detX s.s) (spinU s.charge s.s) from spinZ s.charge s.s); exact he
-- Reach includes all periods, can use in x evol. B/10 enough.
local notation "gr" i:max k:max s:max=> (Rt i k s)
local notation "loom" i:max s:max=> (tape i).CapeT s
local notation "ΩB" i:max k:max s:max=> (Rt i k s).p
local notation "pro" i:max k:max s:max=> funde P.K.j (Rt i k s).J.M (Ω i s)
local notation "link" i:max k:max s:max=> Moire.bloom (Rt i k s).J.P
variable {r i k s:ℕ}{a b c v w:ℝ}
-- Actual contexts required even after selecting Y. NO slip reset.
structure MaskPoint (r s i k:ℕ)(a b:ℝ):Prop where
 ppm : Tulip.Solo (100*(4*a)) b (pro i k s) P.d
 term : Tulip.Solo (100*(4*a)) b (link i k s) P.d
 permit : Permission (pro i k s) (link i k s) P.d
 C : Checked (ΩB i k s) (loom i s) P.J.k P.d a ((ΩB i k s).B/10) P.J.n
 pulse : DockPulse (ΩB i k s) (loom i s) P.J.k P.d a P.h 32 24 P.J.n
 hK : P.U.roundZ ≤ (Ω i s).val
 reach: (ΩB i k s).B+2*r+12 ≤ 24*(ΩB i k s).B
 escap: 8*r≤ (ΩB i k s).B
 slip: (Rt i k s).slip=0
 B0: (ΩB i k s).B=radiusB (xt s)
 V0: (ΩB i k s).order=6
 V1: (ΩB i k s).threshold=temp (xt s)
 spend : Sectoral (ΩB i k s) P.J.n (scald (ΩB i k s) (head_L (Rt i k s).F)) P.h (rScale (ΩB i k s)+((ΩB i k s).B:ℝ)⁻¹) (RΓK (ΩB i k s) P.R.L (xt s))
include flag
private lemma grantGrowth (s i k:ℕ)(h:s < Y.uv k): (ΩB i k s).threshold ≤ P.J.k ∧ (Rt i k s).slip=0:=by
 let M:= Y.ir i; let Y':= Y.voyage i; let e:=Coord i k; let X:= Actual Y.meter Y'.funds Y'.CapeT (gaugeFreq P (Y.tile*P.M)) (Y.uv k)
 obtain ⟨p,b,hb,g⟩:= flag i (Y.uv k); have hl:X.active P.P b s=X.gram P.P b s:= p.success P.H hb.toRealQ s h (p.paysStep P.H hb s h)
 unfold RootBook; rw [g.gramZ,← hl]; exact ⟨(p.request s h).pole,rfl⟩
lemma leaseFrame (H:RateStamp Y)(W:Solstitial P)(r:ℕ) : ∃ a b:ℝ,0 < a ∧ 0 < b ∧ ∀ᶠ s:ℕ in atTop,∀ i k:ℕ,s<Y.uv k→ MaskPoint Y r s i k a b:=by
 obtain ⟨c,b,hc,hb,P'⟩:= W.season; obtain ⟨K,q⟩:= P'.exists
 let a:= c/400; have ha:0<a:=by unfold a; positivity
 have tE:100*(4*a)=c:=by unfold a; ring
 obtain ⟨u,T,H'⟩:= Rill.cozy 6 P.dpos
 have hF:Tendsto (fun s=> (radiusB (xt s):ℝ)) atTop atTop:=tendsto_natCast_atTop_atTop.comp (Work.E01.radiusB_tendsto.comp (turnover P)); have hL: Tendsto (radiusB ∘ (hat P.R.L P.x)) atTop atTop:=Work.E01.radiusB_tendsto.comp (turnover P)
 refine ⟨a,b,ha,hb,?_⟩
 filter_upwards [age_above Y K,seatReceipt Y H,hL.eventually_ge_atTop (P.J.n*2+32+8*r+12), (hF.const_mul_atTop ha).eventually_ge_atTop (2*32*↑(Fief.tileN 24)),(turnover P).eventually ((show Tendsto temp atTop (𝓝 0) by simpa using Work.E09.radiusB_temp 0).eventually (ge_mem_nhds H'.peta))] with s t e ht hx hr i k hk
 let N:=age Y i s; let G:= RootBook Y i k s; have hG:= orbitalInterest Y flag s i k hk
 let M:= Y.voyage i; let W0:= (M.ownership s).paid
 obtain ⟨hu,hW⟩:= q N (t i)
 have hp:= heightRoom Y i s
 obtain ⟨v1,vp⟩:=grantGrowth Y flag s i k hk
 have he:G.p=Y.meter.a s:= (((Y.voyage i).X (Y.uv k)).pull.owns s hk.le).width.symm
 have hP : G.p.B=radiusB (xt s):= he.symm ▸ (Y.meter.boot s).2.1
 have h0:G.p.order=6:= he.symm ▸ (Y.meter.boot s).2.2.2.2
 have hh:G.p.threshold=temp (xt s):= he.symm ▸ (Y.meter.boot s).1
 have hs:P.J.n*2+32+8*r+12 ≤ G.p.B:= hP.symm ▸ ht
 have ht:Roof (Ω i s) P.J.k P.d P.J.n _:= {W0 with paid:= fun i=>(W0.paid i).shrink P.J.hr.le}
 refine ⟨tE.symm ▸ hu G.J.M,tE.symm ▸ hW G.J hG,foreHand P _ _ hG hp,⟨ht,P.dpos,v1,ha,?_⟩,⟨ha,P.height,P.dpos,ht,v1,(by norm_num),⟨T,u, h0.symm ▸ H',hh.symm ▸ hr⟩,?_ ,?_ ,?_,hP.symm ▸ hx⟩,hp,?_ ,?_,vp,hP,h0,hh,e i k hk⟩
 · change G.p.B /10 + _+_ ≤ G.p.B; omega
 · change P.J.n+10 ≤ 24*G.p.B; omega
 · change 3≤ G.p.B; omega
 · change 2*P.J.n+32 ≤ 5*G.p.B; omega
 · change G.p.B+2*r +12 ≤24*G.p.B; omega
 change 8*r ≤ G.p.B; omega
omit flag
lemma requestW (E: MaskPoint Y r s i k a b)(x:Site (Ω i s))(F:Pattern (pro i k s) (link i k s) r P.d a v)(w:ℝ) : let Q:= (ΩB i k s); let g:= E.C; let d:=Q.B/10
 let t:= wholeTail 24 Q 32 P.h a b w r*(Real.exp (-a*(d:ℝ))*LitCurrent.expiry (4*a) v); let Z:=seaFront 24 Q 32 P.h a b r+t+dropout 24 Q 32 P.h a b w v r; let A:=fun v:Orbit (Ω i s)=> surrogate (loom i s) Q d w x F (v.1,(loom i s) v); ∃ M:Sour.Bag (Ω i s), Nest P.U (Rt i k s) (loom i s) P.J.n 24 (node x) P.h (rScale Q) A M (Z+τΓK Q P.R.L (xt s) Z) (t+τΓK Q P.R.L (xt s) Z):=by
 intro p g d t Z A'; have hB:0 ≤ rScale p:=by unfold rScale; positivity
 let D:= (p.B:ℝ)⁻¹; have h':0<D:=by unfold D; have hp:=p.B_pos; positivity
 have hp:a≤100*(4*a):=by have hv:=g.hint; linarith
 have ht:=local_fence w E.C x F E.pulse E.permit (E.ppm.drop hp) (E.term.drop hp) (le_trans (by omega) E.reach)
 obtain ⟨W,X⟩:= knock P.U _ _ E.pulse.roof E.hK E.slip hB h' (downFence (m:=0) ht (rateEx p)) E.spend -- tune
 refine ⟨W,?_⟩; unfold D at X; simp only [inv_inv] at X; exact X
end Preparation
end LocalLimit
end Rate
end YM.CF.Py
