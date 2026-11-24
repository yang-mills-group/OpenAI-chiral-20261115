import YM.CF.Muse.Gates
set_option autoImplicit false
set_option maxHeartbeats 390000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Oath
open Nor
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
variable{N P B:Side}{S:StepData (Domain N B) (Domain P B)}{T: Tube SU.group S}{K:Teller SU.group}{G:Ratio (mid N B) (mid P B)}{R:Patch}{L:ChartRatio SU.group}
variable {d e η t z g b c A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Lich.Muster Push.AbsoluteSums
open Iva Eire
open Wray Prism Font
open Eire.Dress Yaw PetalP Feu Feu.Corset Haro
variable {r K0:ℕ}{ι:Type}[Fintype ι][DecidableEq ι]{f c:Type}[Fintype f][LinearOrder f][Fintype c][LinearOrder c]
local notation "κ"=> (Scree.mid P B)
local notation "Kx"=> (Scree.mid N B)
local notation "hT"=> (LeanV f)
local notation "Zx"=> LeanV c
local notation "BF"=> (Eire.Ride S)
local notation "Fm"=> (LeanV (Single κ))
local notation "CM"=> (LeanV (Single Kx))
-- Exact resolve PH.Wick all shares.SupportX both senses. 
variable (p q: Single (mid P B))(Tg:Rill.Arch G t)(W: Meter TailB G t)(Y:Meter Grave G t)(g_: Odd G.count.val)(t':0<t)(kR:ℕ)
local notation "ρ"=> Support (Domain P B)
local notation "PX" b:max a:max=> (twigExt (b,a))
local notation "β"=> bring t' Tg
local notation "Xm"=> cala G S g_ t t' W Y Tg kR
-- reindex independent True Tilt.Axis. Metric after PE.Z.W. EACH (p,q) coarse independent shape.ALL order consensus
variable (F':RegBudget (mid P B))(DΦ:Finset (Scree.Hub (mid P B)))
local notation "Xρ"=> (γl x (Domain P B))
local notation "KΩ"=> (Finset (Support (Domain P B)))
local notation "SX"=> (StackL F' DΦ)
-- stack includes all.Slip combined separately. ANY charges.
local notation "ρk"=> (inbool (Domain P B) x)
variable (X: Finset (Support (Domain P B)))(U:Pane (mid N B))
local notation "Fv"=> (pulled G (bring t' Tg) W SX X)
local notation "tU"=> (bring t' Tg)
local notation "LI"=> (frame_w Fv)
variable (u:∀ i∈ DΦ,∀ (W':Pane (mid P B)), Flour (camp i.val.2) ((F' i W').val))
-- localized docks for reanchor tariff exactly first endpoint. Edge h. support.C. Without revolution. 
variable (i:Scree.Hub (mid P B))(p₁ p₂:Rock (mid P B))(q₁ q₂:Rock (mid N B))(Y Z:Support (Domain P B))
local notation "Θ"=> lyric G t' W (F' i) Y Z p₁ p₂ q₁ q₂ 1 Tg
local notation "oQ"=> (S.ratio.parent i.val.1)
variable(Qx:TailB→Support (Domain P B)→Toll (Iota G))(pR:∀ i B,Suite (badge _) (pinH G t true) (pinH G t false) B (Qx i B) (W i B))
variable {u0:ℝ}(h: Prism.Rock (mid P B))
local notation "vZ"=> (hatY S)
variable (hv:S.ratio=ratio G)
open PhysicalNext.JointLoad PhysicalNext.JointLoad.Heir Siete
variable (hiZ:Cube.node p₁.1∈ i.val.2)(hj:Cube.node p₂.1∈ i.val.2)(hY:Y∈inbool (Domain P B) x)(hZ:Z∈inbool (Domain P B) x)
variable (S':BudgetPoint)(hy:Heir.Short S S' i.val.2)(hΩ:S'.B≤ 2*radiusB x)
local notation "L₃"=> Haro.taxi
local notation "L₂"=> (fun V=>lineY q₁ q₂ (Haro.taxi V q₁ q₂ Θ))
structure Shrine (N:Side)(X: Finset (Seat N))(F:Pane N→FC (Dwell N)):Prop where
 warm : LocalOn X F
 tax(U:Pane N): Flour (camp X) (F U)
 glow: Continuous F
 rotor (g:Seat N→ SU.E)(U:Pane N): (lotY false false (tradew N g)) (F U)= F (gauge g U)
namespace Shrine
lemma emptyT(n:Side)(X:Support (More n)):Shrine n X (fun _=>0):= ⟨fun _ _ _=>rfl,fun _=> Flour.trivial, continuous_const,fun _ _=>map_zero _⟩
lemma yearT{J:Type*}(X:Finset J)(V:Support (More N))(F:J→Pane N→FC (Dwell N))(t:∀ i∈X,Shrine N V (F i)): Shrine N V (fun p=> ∑ i∈X,F i p):= ⟨fun x y h=> sum_congr rfl (fun i g=>(t i g).warm x y h),fun i=> Flour.sum X (fun j k=>(t j k).tax i),continuous_finsetSum _ (fun j k=>(t j k).glow),fun x y=> (map_sum _ _ _).trans (sum_congr rfl fun j v=>(t j v).rotor x y)⟩
lemma raiseY{X Y:Support (More N)}{F:Pane N→FC (Dwell N)}(p:Shrine N X F)(h:X⊆Y):Shrine N Y F:=⟨fun x y k=>p.warm _ _ (fun i v g=> k _ (h v) (h g)),fun i=> (p.tax i).lift (fun i g=> mem_filter.mpr ⟨mem_univ _,h (mem_filter.mp g).2⟩),p.glow,p.rotor⟩ -- tune
end Shrine
variable (U0:Support (Domain N B))(hU0:Lattice.halo (45*(1+radiusB x)) {S.ratio.parent i.val.1} ⊆ U0)
variable {a:ℝ}(Vq:PressB S' i (F' i) a b) -- a binder a? 
lemma sharesY(a b:Rock (mid N B))(P:Op SU.Slot)(F:Support (Domain N B))(h:node a.1∈F)(p:node b.1∈F): Flour (camp F) (lineY a b P):= Flour.sum _ (fun i _=>Flour.sum _ fun j _=>(Flour.putPut (camp F) (show (true,(a,i))∈camp F from mem_filter.mpr ⟨mem_univ _,h⟩) (show (false,(b,j))∈camp F from mem_filter.mpr ⟨mem_univ _,p⟩)).smul (P i j))
lemma taxi_c (a b:Rock (mid N B))(P:Op SU.Slot): Continuous (fun U:Pane (mid N B)=> Haro.taxi U a b P):=by
 have he:Continuous (fun U:Pane (mid N B)=> travel U (posG a) (shiftH (posG a) (posG b))) := travel_cont .. -- tune
 have hp:Continuous (fun x:SU.E=> mater x):=SU.matter_cont
 exact (show Continuous (fun _:Pane (mid N B)=>P) from continuous_const).mul (hp.comp he)
lemma lines_c (a b:Rock (mid N B))(P:Op SU.Slot): Continuous (fun U:Pane (mid N B)=> lineY a b (Haro.taxi U a b P)):=continuous_finsetSum _ (fun i _=>continuous_finsetSum _ fun j _=>((taxi_c a b P).matrix_elem i j).smul (continuous_const (y:=gateY (a,i) (b,j))))
include hY hZ hiZ hj t' pR hU0 hΩ g_ hv hy Vq
lemma domeK(H:Tg.val=1): Shrine (mid N B) U0 L₂ :=by
 by_cases h:Θ=0; · simp_rw [h,Haro.taxi, zero_mul,lineY,Matrix.zero_apply,zero_smul,sum_const_zero]; exact Shrine.emptyT _ _
 obtain ⟨h,t,E,R⟩:= path_Y Tg W g_ t' F' i p₁ p₂ q₁ q₂ Y Z Qx pR hv hiZ hj hY hZ S' hy hΩ h
 let v:=posG q₁; let w:=posG q₂; have hp(p:Rock (mid N B))(h:separation oQ (posG p)≤ cirQ x): node p.1∈ U0:= hU0 (halo_spec.mpr ⟨_,mem_singleton_self _,h.trans (by unfold cirQ; omega)⟩)
 refine ⟨fun x y p=>?_,fun U=>sharesY q₁ q₂ (Haro.taxi U q₁ q₂ Θ) U0 (hp q₁ h) (hp q₂ t), lines_c q₁ q₂ Θ,fun f x=>?_⟩
 · unfold Haro.taxi; have he:travel x v (shiftH v w)= travel y v (shiftH v w):=travel_local _ _ x y (fun i u k=> p i (hU0 (R (List.mem_toFinset.mpr u))) (hU0 (R (List.mem_toFinset.mpr k))))
   exact congr_arg (fun t=> lineY q₁ q₂ (Θ * mater t)) he
 rw [rite_G,Haro.care q₁ q₂ x Θ (fun l=>Haro.taxing G t' W i (F' i) Vq Y Z p₁ p₂ q₁ q₂ Tg _ _ (pR ..) (pR ..) l H)] -- tune
local notation "CΩ"=> (radiusB x)
variable (O O₁:Ride S)(h0:Lattice.halo (45*(1+radiusB x)) {S.ratio.parent i.val.1} ⊆ Stilo.bay O)
omit hU0 hiZ hj hY hZ
local notation "BQ" a:max b:max => (fun V'=> bornY (S:=S) (γl x (Domain P B)) (F' i) W t' a b kR O Tg V' O₁)
local notation "vΦ"=> hue_I i.val.2
-- all terms transfer. support at ANY ride O₁. need noncarrier‐invariant when bAe.Comp.All.
include h0
lemma heroQ(H:Tg.val=1):let Y(U:Pane (mid N B)):= ∑ i∈ vΦ,∑ j∈ vΦ,(BQ i j) U; Shrine (mid N B) (Stilo.bay O₁) Y ∧ (¬O ≤ O₁→Y=0):=by
 let Yv(p q:Rock (mid P B))(Y Z:Support (Domain P B))(V:Pane (mid N B)):= curbY (primeY (S:=S) kR Y Z O) (fun r s=>dawnX G t' W (F' i) Y Z p q r s V Tg) O₁ -- implicit target V? check!
 let X0(U:Pane (mid N B)):= ∑ p∈ hue_I i.val.2,∑ q∈hue_I i.val.2,∑ t∈ γl x (Domain P B),Yv p q t.1 t.2 U
 intro Y_; have he:Y_= X0:=by funext v; unfold Y_ bornY; simp_rw [Finset.sum_apply]; rfl
 have hf(p q z y U)(h:primeY (S:=S) kR z y O≠ O₁): Yv p q z y U=0:= by unfold Yv curbY; exact Pi.single_eq_of_ne (Ne.symm h) _
 have hh(z y): O≤ primeY (S:=S) kR z y O:= (le_sup_left (a:=O) (b:=_)).trans le_sup_left
 rw [he]; refine ⟨?_,fun v=>funext (fun i'=> sum_eq_zero fun p _=>sum_eq_zero fun q _=>sum_eq_zero fun t _=> hf _ _ _ _ _ (fun h=>v (h ▸ hh _ _)))⟩ -- gauge
 apply Shrine.yearT _ _ _; intro p q; apply Shrine.yearT _ _ _; intro j g; apply Shrine.yearT _ _ _; intro y h; by_cases v:primeY (S:=S) kR y.1 y.2 O = O₁; swap; · rw [show Yv p j y.1 y.2 =(fun _=>0) from funext fun U=> hf _ _ _ _ _ v]; exact Shrine.emptyT _ _
 let U:= Stilo.bay O; let Q(s t:Rock (mid N B))(K:Pane (mid N B)):= lineY s t (dawnX G t' W (F' i) y.1 y.2 p j s t K Tg)
 have hp(s t): Shrine (mid N B) U (Q s t):= domeK Tg W g_ t' F' i p j s t _ _ Qx pR hv (mem_filter.mp q).2 (mem_filter.mp g).2 ((mem_product.mp h).1) ((mem_product.mp h).2) S' hy hΩ U h0 Vq H
 -- prime support carriers includes host.B & old vertices. values.localOn smaller U iff footprint touched.Host yes
 rw [show Yv p j y.1 y.2 =fun V=>∑ p:Rock (mid N B),∑ j: Rock (mid N B),Q p j V from funext fun x=>by unfold Yv curbY; rw [v, Pi.single_eq_same]] -- tune ambiguity
 refine Shrine.raiseY (Shrine.yearT _ _ _ fun p _=> Shrine.yearT _ _ _ fun j _=> hp p j) ?_
 exact Stilo.bay_m (v ▸ hh _ _) -- tune
end YM.CF.Oath
