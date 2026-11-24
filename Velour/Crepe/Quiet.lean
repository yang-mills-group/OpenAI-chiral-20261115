import SatinThinReport
import Velour.Board.Birth
import SatinThinRoman
/-! More modest price at scalar leaf level s. 
 Pay signed law variation first (cf. SatinThinWarp, SatinThinReport), 
 then pointwise sup of replicated scalar Mark. -/
set_option maxHeartbeats 1050000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars true
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Rate.LocalLimit.Preparation
open Neon
open Py
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
open Ione Moto Taxi Hove Haro Vow Bake Lilt Prism Rue Larch Push.AbsoluteSums.Trees Salt Jet
open scoped YM.CF.Mew

set_option autoImplicit false
open Mew QuadClock Roots Rive Oise


open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
open QuadClock FullBill Pitching Focus Buffered Afterglow Journey
variable {P:Preparation}{ℓ:ℕ}(Y:Course P (VolumeCape.Dream.Nimbus ℓ))
attribute [-instance] instDecidableEqLex
namespace Yoke
open Tapestry Advance Papyrus Papyrus.Franc
variable {n:Side}
open Py.Rate.Pannier CF.Pannier Chancel Rous Pressure Worth Worth.Pays Graph
open Regis.Head.Etch
variable (s i k:ℕ){f r v d:ℕ}{a c:ℝ}
local notation "L"=> P.R.L
local notation "Δ"=> P.block
local notation "Ω" j:max=> side Y i j
local notation "Gξ" j:max=> Vale.apt (Y.ir i) P.block P.R.L j
open Again Buffered.Afterglow.Tower.SlabMark

open VelourBoard
def Quiet (U:ℝ) (W:Mark n) :=
   ∀ x,∃ z:ℂ, ‖z‖≤U ∧ W x=z • 1
lemma Quiet.mul {W W':Mark n}{U V:ℝ}(h:Quiet U W)(g:Quiet V W'):Quiet (U*V) (W*W'):=by
 intro x; obtain ⟨z,t,v⟩:=h x; obtain ⟨w,p,r⟩:=g x
 refine ⟨z*w,norm_mul_le_of_le t p,?_⟩
 rw [Pi.mul_apply,v,r,Algebra.smul_mul_assoc,one_mul,mul_smul]
lemma Quiet.refl {W:Mark n}{U:ℝ}(h:Quiet U W)(i:Axis)(d:ℤ):Quiet U (reflMark i d W):=by
 intro x; obtain ⟨z,t,v⟩:=h (reflFields i d x)
 unfold reflMark; rw [v,theta_smul,theta_one]; exact ⟨star z,(by simpa using t),rfl⟩

variable {W:Mark (side Y i s)}{U:ℝ}
local notation "ε"=> meterC (hat L P.x s)
local notation "N"=> side Y i s
variable {w:ℝ}(V:ShelterCost w Y s i k)


include V
lemma quietMark (p:(Y.voyage i).kick ≤ k)
    (h:Quiet U W)(r:Envelope W) (u:0≤U):
 ‖Journey.compass Y i k s W‖≤ U*Real.exp (14*ε * sites N):=by
 let Z:= RootBook Y i k s; let B':= U
 let F':=fun (x: Orbit N)=> letterRead (W (x.1,(Y.voyage i).CapeT s x)) (denZ Z P.U ((Y.voyage i).CapeT s) x)
 let g:=glowRise Y 0 s i k 0
 let D':=shadeY Y s i k 0 (gateC (hat P.R.L P.x s))
 have t:Integrable F' (city N):=mark_integrable (Papal.roofage Y i s).bill r (Marks.can_read _ _ _ _ (Y.each_level i k s p V.load.paid))
 have gF (x: Orbit N) : ‖F' x‖ ≤ U*(Real.exp g*D' x):=by
    obtain ⟨z,v,X⟩:=h (x.1,(Y.voyage i).CapeT s x)
    unfold F'; rw [X,(mark_linear 1 0 _ _).2,norm_mul,←beam_nil]; exact mul_le_mul v (market_price Y V x) (norm_nonneg _) u

 let Q:=‖coined Y i k s‖; let d:= Papal.gBaseR Y s i k
 let Ψ:= Cascade.angleFin Z.J.M (side Y i s) P.K.j; let ε':= Z.v.re
 let K:=sites (side Y i s)
 let v:= Scales.merit P.R.L (hat L P.x s)
 let h:= ε
 let C':ℝ:= d+7*h*K
 change ‖(∫x,F' x ∂city _) / _‖ ≤ _
 have hD:=V.load.vast; simp only [VLine,compensated,norm_mul,Complex.norm_exp,Complex.neg_re] at hD; change Real.exp (d+Ψ-v*K)≤ Real.exp (-ε') * Q at hD
 have hx: 0<Q:= by by_contra! hv; exact (Real.exp_pos _|>.not_ge) (hD.trans (mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _|>.le) hv))
 obtain ⟨hz,he⟩:= shade_prior Y V.load V.load.ready V.load.willing
 rw [norm_div,div_le_iff₀ hx]; have hB': 0≤B':=u
 apply le_trans (norm_integral_le_integral_norm F'); apply le_trans (integral_mono (μ:=city (side Y i s)) t.norm ((hz.const_mul _).const_mul _) gF)
 rw [integral_const_mul,integral_const_mul]; refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (Real.exp_pos _|>.le)) hB') ?_
 let wk:=14*h*K; change B'*(Real.exp g*Real.exp C')≤ B'*Real.exp wk*Q; rw [mul_assoc]; apply mul_le_mul_of_nonneg_left _ hB'
 rw [show wk=(wk+ε')+(-ε') from (by ring), Real.exp_add (wk+_ ), mul_assoc]; refine le_trans ?_ (mul_le_mul_of_nonneg_left hD (Real.exp_pos _|>.le)); rw [←Real.exp_add,←Real.exp_add]; apply Real.exp_monotone; have hv:v≤h:=V.load.health.1; change 4*(0:ℝ)*↑(0:ℕ)+6*h*K+Ψ+ε'+ C' ≤ _; unfold C' wk; rw [Nat.cast_zero]; nlinarith only [mul_le_mul_of_nonneg_right hv (show 0≤K from zero_le_one.trans (sites_pos _))]

omit V

variable (H:Real.exp 1≤ P.x)
local notation "K"=>tent Y H
local notation "μ"=>momentm Y i s
local notation "ξ"=>exhibit Y H s i
variable {o:VelourBoard.Cell}{B:ℕ}{F:Buffered.Family (tent Y H)}
 {l:List (VelourBoard.Tile (tent Y H))}{a₁ a₂:VelourBoard.Cell}{S:Finset Cover}
 (Q:Quiet U (exhibit Y H s i F))
include Q
lemma rolling_quiet
    {x:VelourBoard.Tile K} (h:Transit B o F x):
 Quiet U ((ξ) x.leaf):=by
 induction h with
 | here => exact Q
 | turn h j d ih=>
    rw [renderTumble]; exact Quiet.refl ih j (PaneCut _ _ _ _ _)
lemma rolled_array
    (h:Paved B o F l a₁ a₂):
 Quiet (U^l.length) ((ξ) (VelourBoard.Representation l)):=by
 induction l with
 | nil=> rw [List.length_nil, pow_zero]; rw [show VelourBoard.Representation ([]:List (VelourBoard.Tile K)) = 1 from rfl, actual_one]
         exact fun _=> ⟨1,by simp,by simp⟩
 | cons x l ih=>
    have t:= rolling_quiet Y s i H Q (h.homes x List.mem_cons_self)
    change Quiet _ ((ξ) (x.leaf*VelourBoard.Representation l))
    rw [actual_product,List.length_cons,pow_succ']
    exact Quiet.mul t (ih ⟨fun y r=>h.homes _ (List.mem_cons_of_mem _ r),
        (List.pairwise_cons.mp h.sorted).2,fun y r=>h.places _ (List.mem_cons_of_mem _ r)⟩)
include V

lemma quiet_board
 (p:(Y.voyage i).kick ≤ k)
 (u:0 ≤ U)
 (t:InTest (K) true S false F) (a:VelourBoard.Parcel K B o 0 S)
 (fee:14*ε*((↑(2*pitch (K) B :ℕ):ℝ)^4)≤1)
 (h:Deck μ B o F l a₁ a₂):
  ‖Journey.sharp Y H s i k (VelourBoard.Representation l)‖ ≤
     (U * Real.exp 1)^l.length:=by
 obtain ⟨_,b,_⟩:= pavingReservation t a h.paved
 have z:=quietMark Y s i k V p (rolled_array Y s i H Q h.paved) (exhibited Y H s i _ b).env (by positivity)
 rw [actualRead,mul_pow]
 refine z.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
 rw [←Real.exp_nat_mul,mul_one]


 obtain ⟨_,_,p',m',_⟩:= V.load.health
 have hp:=h.fill; rw [show (K).c μ=N from terrain Y H (Y.ir i) s] at hp
 have hi : sites (N) ≤ (2*pitch (K) B:ℕ)^4 * (l.length:ℝ):=by
   unfold sites; have hm:=hp.1
   exact_mod_cast (
     show (More (N)).val^4 ≤ (2*pitch (K) B:ℕ)^4 * l.length from by
       change ((N).val*2)^4 ≤ _
       linarith only [Nat.mul_le_mul_left 16 hm])
 have hs: 14*ε*sites (N) ≤ l.length:=by
    have ht:0≤ ε := p'.le.trans m'
    nlinarith only [mul_le_mul_of_nonneg_left hi (show 0≤14*ε by linarith),
      mul_le_mul_of_nonneg_right fee (Nat.cast_nonneg (α:=ℝ) l.length)]
 exact Real.exp_le_exp_of_le hs
end Yoke
end YM.CF.Py.Rate.LocalLimit.Preparation
#print axioms YM.CF.Py.Rate.LocalLimit.Preparation.Yoke.quiet_board

