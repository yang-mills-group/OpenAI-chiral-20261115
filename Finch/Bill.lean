import Finch.Opening
import Finch.Jet

set_option autoImplicit false
set_option maxHeartbeats 1100000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate
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
open Ione Beau Haro Cascade Fief
open scoped Mew

open Wray Oath Feu Feu.Corset Nor Yaw Pig Oise Jade Plume Push.AbsoluteSums
open Trees Lich.Muster Jet
set_option linter.flexible false
open Chaff Gloss Maize Tye RP RP.Str Oise
namespace LocalLimit

namespace Preparation
open FullBill Window Marks
open Swell
open Vow.TreasuryFog Sour
open _root_.Zephyr.Chern
open YM.CF.BPress (NPL)
open Buffered.Afterglow.Tower.VacuumSelection (Spine)

variable {P:Preparation}{F:(s:Side)→Scree.Loom s→Prop}(Y: Course P F)
local notation "Ng" i:max s:max => (P.Ctor (Y.ir i) s)
local notation "A" i:max s:max => (Y.voyage i).CapeT s
local notation "S" i:max k:max s:max=> RootBook Y i k s
local notation "xt" => hat P.R.L P.x

-- normalization x,tau,w0 convention for all. spell (128) and weight in (129).
abbrev feeSize (P:Preparation)(s:ℕ):ℝ:= pinpr P.R.L (hat P.R.L P.x s)/(temp (hat P.R.L P.x s))^2
abbrev normRoot (P:Preparation) (s:ℕ) : ℝ:= hueW P.R.L (hat P.R.L P.x s)

def InHand (i k s m:ℕ)(O:Site (Ng i s))(X:SOp (Ng i s))(J:Axis→SOp (Ng i s)): Evaluation (Ng i s):=
 (feeSize P s:ℂ) • finchWardMark (A i s) (S i k s).p O J X m

def Ramp (i k s m:ℕ)(O:Site (Ng i s))(X:SOp (Ng i s))(J:Axis→SOp (Ng i s)): Evaluation (Ng i s):=
 (stemS (hat P.R.L P.x s):ℂ) • InHand Y i k s m O X J
lemma heatSize (P:Preparation)(s:ℕ): feeSize P s*stemS (hat P.R.L P.x s)=normRoot P s:= rfl
lemma ramp_eq (i k s m:ℕ)(O:Site (Ng i s))(X:SOp (Ng i s))(J:Axis→SOp (Ng i s)): Ramp Y i k s m O X J=(normRoot P s:ℂ) • finchWardMark (A i s) (S i k s).p O J X m:=by rw [Ramp,InHand,smul_smul,mul_comm,←Complex.ofReal_mul, heatSize]

structure SingleRootAccount (a c:ℝ)(i k s m:ℕ)(q g:ℝ)(O:Site (Ng i s))(J:Axis→SOp (Ng i s)) (X:SOp (Ng i s)) (L:Bag (Ng i s)):Prop where
   funding : let R:= S i k s; let M:=funde P.K.j R.J.M (Ng i s); let W:=Moire.bloom R.J.P; let B:=R.p.B; let B':=B/10; let t:=Real.exp (-a*(B':ℕ))*c;
     (∀ j, Trunk (node O) (J j) B' a c P.d) ∧ Trunk (node O) X B' a c P.d ∧ ∃ (T:Axis→ SOp (Ng i s))(Z:SOp (Ng i s)), (∀ j,Soak (node O) (T j) a t P.d)∧ Soak (node O) Z a t P.d∧(∀ j,∀ x:Openc (More (Ng i s)) P.d,spur (millIntro M W) O j m x.val=J j x.val + T j x.val)∧∀ x:Openc (More (Ng i s)) P.d,(M x.val-tickA _)*windmill O m=X x.val+ Z x.val
   actual128 : FullInsertion Y i k s O q (g * pinpr P.R.L (xt s))
      (‖(normRoot P s:ℂ)‖*wardValue c) (wardZone (S i k s).p O m)
      (Ramp Y i k s m O X J) ((normRoot P s:ℂ) • puffLine (A i s) (S i k s).p O J X m) L
   guardOk : (S i k s).p.threshold ≤ P.J.k
   space : (S i k s).p.B/10 + P.J.n ≤ (S i k s).p.B

variable (t :∀ i k, ((Y.voyage i).X k).Prepared P.P P.delay)(v:RateStamp Y) (w:Compass_sol Y)
include t v w
lemma fundRoot (m:ℕ): ∃ a c:ℝ, ∃ q g:ℝ→ℝ, 0<a ∧0<c∧ NPL q ∧ NPL g ∧ ∀ᶠ s in atTop,∀ᶠ i in atTop,∀ k,s<Y.uv k→∀ O:Site (Ng i s),∃ (J:Axis→SOp (Ng i s)) (X:SOp (Ng i s))(L:Sour.Bag (Ng i s)), SingleRootAccount Y a c i k s m (q (xt s)) (g (xt s)) O J X L:=by
 obtain ⟨a,c,F,D,ha,hc,hF,hD,g⟩:= factorium Y t w v m -- order #
 obtain ⟨p1,q1,u,m1,-,-,-,-,Ψ⟩:= w.pays
 refine ⟨a,c,F,D,ha,hc,hF,hD,?_⟩
 filter_upwards [g,Ψ, (Work.E01.radiusB_tendsto.comp (turnover P)).eventually_ge_atTop (2*P.J.n)] with s u Q l
 filter_upwards [u,Q] with i f g k w O
 obtain ⟨J,T,X,Z,q,t',x,z,y,Y',L,e⟩:=f k w O
 let R:=S i k s; let p:=R.p; have he: p=Y.meter.a s:=(((Y.voyage i).X (Y.uv k)).pull.owns s w.le).width.symm
 obtain ⟨_,_,W,_,u,_⟩:=g k w
 have Γ: Roof (Ng i s) P.J.k P.d P.J.n (A i s):= { W with paid:=fun i=>(W.paid i).shrink P.J.hr.le}
 have ℓ:p.B/10 + P.J.n≤p.B:=by
    rw [he,(Y.meter.boot s).2.1]; change 2*P.J.n ≤ radiusB _ at l; omega
 let V:ℂ:= (normRoot P s:ℂ)
 refine ⟨J,X,L,⟨q,x,T,Z,t',z,y,Y'⟩,?_,u,ℓ⟩
 rw [ramp_eq]; refine ⟨(ticket_ward Γ P.dpos x ℓ u ha.le J q m).smul V,e,fun i=>(puff_uses Γ P.dpos x u ℓ J q m i).2.scale V,fun i=>?_⟩
 simp only [Pi.smul_apply,star_smul,act_smul]; rw [(puff_uses Γ P.dpos x u ℓ J q m i).1]

omit v t w
-- quadratic (centered lift) test
lemma concordance (D:Buffered.Afterglow.Tower.VacuumSelection.Spine)(f:SprigFee D)(a c:ℝ)(p:0<a)(x:Cover)(m:ℕ)(e:0 < m):∃ β> (0:ℝ), ∀ᶠ s:ℕ in atTop,∀ i k,s<D.run.uv k→∀ (J:Axis→ SOp (age D.run i s)) (X:SOp (age D.run i s))(L:Sour.Bag (age D.run i s))(q g:ℝ), SingleRootAccount D.run a c i k s m q g (wrap _ x) J X L→ let N:=age D.run i s; let Z:= inkCost ((D.run.voyage i).CapeT s) (RootBook D.run i k s).p (wrap _ x) X; Bud (Z ∘ petals (stream N)) ∧ β < (bud (Z ∘ petals (stream N)) 2).re:=by
 obtain ⟨β,v,w⟩:= jetLots D f x m e (List.ofFn (id:Axis→Axis))
 obtain ⟨o,⟨W⟩⟩:= oily p D.par.dpos (breadth x)
 let F(n:ℕ):= o*(Real.exp (-a*(n:ℝ))*c); have ht:Tendsto F atTop (𝓝 0):=by
    have h:=(Real.tendsto_exp_neg_atTop_nhds_zero.comp (Tendsto.const_mul_atTop p tendsto_natCast_atTop_atTop)).mul_const c |>.const_mul o
    simpa only [zero_mul,mul_zero,Function.comp_def,neg_mul,F] using h
 obtain ⟨l,h⟩:= eventually_atTop.mp (ht.eventually (gt_mem_nhds (half_pos v)))
 refine ⟨β/2,half_pos v,?_⟩; filter_upwards [w,(Work.E01.radiusB_tendsto.comp (turnover D.par)).eventually_ge_atTop (10*l)] with s w y i k t J X L q g u
 obtain ⟨_,K,T,Z,tX,tZ,_,f⟩:= u.funding
 let N:=age D.run i s; let A':=(D.run.voyage i).CapeT s; let R:=RootBook D.run i k s; let P:= (R.p); let kT:=P.B/10; let θj:= inkCost A' P (wrap N x) X ∘ petals (stream N)
 let B:= (D.run.voyage i).ownership s; have Γ: Roof N D.par.J.k D.par.d D.par.J.n A':={ B.paid with paid:=fun i=>(B.paid.paid i).shrink D.par.J.hr.le}
 have he:= actualJet (W:=fun z=> (funde D.par.K.j R.J.M N z-tickA N)*windmill (wrap N x) m) (stream N) W Γ K.pay tZ (deep_grace x) u.guardOk f
 refine ⟨he.1,?_⟩; let U:=jetAt N (funde D.par.K.j R.J.M N) (stream N) (wrap N x) m (List.ofFn (id:Axis→Axis)); have H : (bud U 2-bud θj 2).re ≤ F kT:=(Complex.re_le_norm ..).trans (he.2.2 2)
 rw [Complex.sub_re] at H; have he: (RootBook D.run i k s).p=D.run.meter.a s:=(((D.run.voyage i).X (D.run.uv k)).pull.owns s t.le).width.symm; have hw: P.B=radiusB (hat D.par.R.L D.par.x s):= (congrArg BudgetPoint.B he).trans (D.run.meter.boot s).2.1
 have hz:l ≤ kT:=by change 10*l≤ radiusB (hat D.par.R.L D.par.x s) at y; unfold kT; omega
 have u:β< (bud U 2).re:=(w i k).2; change β/2 < (bud θj 2).re; linarith [h kT hz]
end Preparation
end LocalLimit
end YM.CF.Py.Rate
