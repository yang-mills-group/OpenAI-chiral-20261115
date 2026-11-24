import YM.CF.Ups.Stone
import YM.CF.Ups.Cosy
import YM.CF.Continuum.PastureCoe
/-!
# Adjustable physical volumes through UV trajectory

Some structures following can be used without regard to the stopping box size.
A main requirement is uniform-in-depth lower bound on norm of the relative
partition, explicitly isolated as `ℓ` and the receipt on Hertz prices. Volumes
allowed by the `meter` for unnormalized trajectories and budgets may then admit
*normalized* towers. We are NOT asserting this for unbounded physical volumes at
fixed x. The main aim is to use the SAME normalization and limit procedures as
FiniteGaugeData for all adjustable boxes. On the anchor box these specialize (see translation
lemmas below and other files). Scripts rework/vary proofs in
`YM/CF/Ups` carefully; quantities are to be read with their authorizations.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Py.Period
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
variable {d e η z g A B':ℝ} {j k k' m n l:ℕ}
variable (V:Grace K R L)
open Lich.Muster Lor
open Jet Vol Rel
local notation "G5"=>SU.group
variable {x y0 β:ℝ}(pp:BudgetPoint){t₀ v v₁ p11 p22 p3 p4:ℝ}
local notation "SN"=> Site (Domain N B)
open Cascade
open Fief
open Yaw Pig
open Wray
open Lich.Muster Push.AbsoluteSums
open Iva Eire
local notation "ζ"=> (radiusB x)
open Trees Footprint Iva Eire
open Jade
open Oath Feu Feu.Corset Ione Nor Haro Beau Salt Vow
set_option maxHeartbeats 800000
variable {U:Grasp V.U B d}{W:GivenX V U}
variable (a:ℝ)(p i N0 k₀:ℕ)
variable {N':Side}(J:Robes N' V W)(q:Chi)(h:ℝ)(R0 δ:ℝ→ℝ)
local notation "Lr"=>dleaf R.L
open CF.Mint MeasureTheory
open CF.Window
open Graph 
structure Session (x:ℝ)(Ns:Side)(l:ℕ) where
 val:Month x a i p N0 V W
 tip: val.q ≤ Ns.val
 main:ℕ→ℝ
 E:Vestal Ns B R.L
 Y:Cape Ns B R.L
 Q:ℕ→Haro.SpaceM
 tilt:ℕ→ℝ
 scale:Brioche V a p i N0 val _ tip l main J q h R0 δ E Y Q tilt

def from_span{x:ℝ}{l:ℕ}(P : SpanPS V a p i N0 J q h R0 δ x l) : Session V a p i N0 J q h R0 δ x (oYY V N0 J x) l:=
  ⟨P.val,P.tip,P.main,P.E,P.Y,P.Q,P.tilt,P.scale⟩
variable(X:Month x a i p N0 V W) (H:MeterQ V a p i N0 J q h R0 δ x X)
variable (Moι:Side)
local notation "Mo"=> Moι
local notation "Zo" j:max=>cell Mo B R.L j
variable {ℓ:ℝ}(hp:1≤h)(ht:0 <ℓ)(hx:0 < x)

variable (QK:∀ l:ℕ,∀ X:Session V a p i N0 J q h R0 δ x Moι l,ℓ ≤ ‖Complex.exp (-(X.E 0).v)*partitionZ (X.E 0) U (X.Y 0)‖)
structure Chain (S:∀ l:ℕ,Session V a p i N0 J q h R0 δ x Moι l)(R':Cape Moι B R.L): Prop where
 tale(i:ℕ): (S i).Y= R'
 tip(i:ℕ): (S i).val=X
 guide(k l:ℕ)(p:k≤l): partitionZ ((S l).E k) U (R' k)≠0
 stain(j:ℕ): ∃ K:ℝ,∀ l:ℕ,j≤l →∀ V, ‖ω_den U ((S l).E j) (R' j) V‖≤ K
 port(j l:ℕ)(p:j≤l): RG.Envelope (ω_den U ((S l).E j) (R' j))
local notation "hatQ"=> hat R.L x
include H QK hp ht hx
set_option maxHeartbeats 1100000 in
lemma fullChain (y':X.q ≤ Moι.val)(sized :
 ∃ (W0:Cape Moι B R.L)(ρ:ℕ→ℝ), (∀ j,0 <ρ j) ∧ (∀ j:ℕ,RocketV V (mesh Moι R.L j) (mesh Moι R.L (j+1)) U W J (W0 j) (apt Moι B R.L j) q) ∧ ∀ l:ℕ,∃ (B0:ℕ→ℝ) (Z:Vestal Moι B R.L)(Q:ℕ→Haro.SpaceM)(Ω:ℕ→ℝ), Due V a p i N0 X Moι y' l B0 ∧ (∀ j<l,‖Complex.exp (Z (j+1)).v‖*ρ j≤ ‖Complex.exp (Z j).v‖) ∧ Pull_P V a p i N0 X Moι y' l B0 J q h R0 δ W0 Z Q Ω ∧(∀ j:ℕ,j≤l→matchedX (hat R.L x j) (Z j).beta) ∧∀ j:ℕ,j≤l→partitionZ (Z j) U (W0 j)=partitionZ (Z l) U (W0 l)) :∃ (S:∀ l:ℕ,Session V a p i N0 J q h R0 δ x Moι l)(R':Cape Moι B R.L), Chain V a p i N0 J q h R0 δ X Moι S R':=by
 obtain ⟨U0,Ψ,θ,r,HB⟩:= sized
 choose X' Z C Zc D γ pB s Vt using HB; let S(i':ℕ):= (show Session V a p i N0 J q h R0 δ x Moι i' from ⟨X,y',X' i',Z i',U0,C i',Zc i',pB i',D i',H.tint,H.pole,s i',r,Vt i'⟩)
 let Dβ(k l:ℕ):= partitionZ (Z l k) U (U0 k); let Lr'(k l:ℕ):= Complex.exp (Z l k).v
 have htK: ∀ k:ℕ, ∃ B:ℝ,0<B∧∀ l:ℕ,k≤l→B≤ ‖(Lr' k l)⁻¹*Dβ k l‖:=by
    intro k; induction k with
    |zero=> refine ⟨ℓ,ht,fun l p=>?_⟩; have hz:=QK l (S l); rw [Complex.exp_neg] at hz; exact hz
    |succ k ih=>
       obtain ⟨d,v,t⟩:=ih; have he:= θ k; refine ⟨d*Ψ k, mul_pos v he, fun l p=>?_⟩; have hz:= t l (by omega); have hv:Dβ k l=Dβ l l:=Vt l k (by omega); have hf:Dβ (k+1) l=Dβ l l:=Vt l (k+1) p; rw [norm_mul,norm_inv,hv] at hz; rw [norm_mul,norm_inv,hf]; have hk:= norm_pos_iff.mpr (show Lr' k l ≠0 from Complex.exp_ne_zero _); have hj:= norm_pos_iff.mpr (show Lr' (k+1) l ≠0 from Complex.exp_ne_zero _)
       apply (le_inv_mul_iff₀ hj).mpr; rw [show ‖Lr' (k+1) l‖*(d*Ψ k)=(‖Lr' (k+1) l‖*Ψ k)*d from by ring]; exact (mul_le_mul_of_nonneg_right (γ l _ p) v.le).trans ((le_inv_mul_iff₀ hk).mp hz)
 choose Zb z u using htK; refine ⟨S,U0,fun i=>rfl,fun i=>rfl,?_ ,?_,?_⟩
 · intro k l p; exact right_ne_zero_of_mul ((norm_pos_iff.mp ((z k).trans_le (u k l p))))
 · intro j; let ε:= Lr (hatQ j); let β:=X.a j; have hh:0 ≤ K.top.paths:=by obtain ⟨t,h,q⟩:= (V.L.mood 0).rows (⟨(0,1), by decide⟩); exact le_trans (tsum_nonneg t) q
   let m:=Zo j; let c:= V.W.bar; let B' := Real.exp (taxY (More m) (2*hatQ j) β.threshold K.top.paths c)*Real.exp (Window.flagBill m ε ε (cashU W.C)); let f(l):=ω_den U (Z l j) (U0 j); let L:= U0 j; let T:= (r j).paid; let T':Roof _ J.k d J.n L:={T with paid:=fun i=>(T.paid i).shrink J.hr.le}
   refine ⟨(Zb j)⁻¹ * B',fun l p y=>?_⟩; let Xs:=Z l j; let H':=(S l).scale; have he:= (H'.note.owns j p); have hU:= H'.close _ p; let H₁:= (S l).E j; have hr:InterestX W.C _ (Xs.J):= he.taste ▸ ((W.arm ..).sound j)
   let v:Orbit m:=y; let F:= recX U Xs L v; let A:=(Lr' j l)⁻¹ * Dβ j l; have hxF: ω_den U H₁ L v=A⁻¹ • F:=by unfold ω_den A Lr' Dβ F recX Xs; rw [Complex.exp_neg,mul_inv_rev,inv_inv,smul_smul,←smul_smul,smul_smul,mul_assoc,(mul_inv_cancel₀ (show Complex.exp (Z l j).v≠0 from Complex.exp_ne_zero _)),mul_one] -- associativity comm orientation.tune
   rw [hxF,norm_smul,norm_inv]; apply mul_le_mul (inv_anti₀ (z j) (u j l p)) _ (norm_nonneg _) (inv_nonneg.mpr ((z _).le)); let Ω:=(H'.note.note j p).lot_p le_rfl le_rfl; have hu:Xs.beta≤ 2*hatQ j:=hU.2; have hxz: Xs.p=β:=he.width.symm; refine (Window.extensive_price Xs L T' U (J.gran.trans (r j).size) (frostQ Ω (zero_le_one.trans hp) hr) (?_: Xs.path.Bounds Xs.funds K.top.width K.top.paths c) ((level_p _).le) hp (cash_v _) (le_trans (by have h:=Vale.crown R.L x j; linarith: 0 ≤ hatQ j /2) hU.1) y).trans ?_
   · rw [← (show _=Xs.funds from he.fund), ←(show _=Xs.path from he.path)]; exact V.L.mood _ -- tune K
   unfold B'; rw [show H₁.p =β from hxz] -- expected Ω thresholds
   refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le; unfold taxY; apply add_le_add_left; exact mul_le_mul_of_nonneg_right hu (by have he:=β.threshold_pos; positivity)
 intro j l p; have H':=(S l).scale; let T:= (r j).paid; let T':Roof _ J.k d J.n (U0 j):={T with paid:=fun i=>(T.paid i).shrink J.hr.le}; let v:= (S l).E j; have he:= (H'.note.owns j p); have hg:v.path.Bounds v.funds K.top.width K.top.paths V.W.bar:=by rw [←(show _=v.path from he.path),←(show _=v.funds from he.fund)]; exact V.L.mood _
 exact Girt.pole_w (denZ v U (U0 j)) (fun x: Phys (Zo j)=> (partitionZ v U (U0 j))⁻¹ • x) (continuous_const_smul _) (Girt.sailW v (ward_m hg ((H'.note.note j p).lot_p le_rfl le_rfl)) W.pearl V.note W.health (by have he:=V.L.lobby; have hx:=R.order_cut; omega) J.n _ T' (J.gran.trans (r j).size)) -- continuous
end YM.CF.Py.Period
