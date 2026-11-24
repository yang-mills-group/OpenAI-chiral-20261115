import YM.CF.Moto.Pin
import YM.CF.Moto.Blade
import YM.CF.Chaff.Hub
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Moto
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
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k' m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset Vow Rue
open Ione Beau
local notation "N"=> P.order
local notation "Xo"=>Skye.Seat n
open Hove Hope Taxi Haro
variable {ρ:Type}[Fintype ρ][LinearOrder ρ]
local notation "Tq"=> Finset ρ
variable (i j:Finset ρ)(p q: ℂ)(A B:Dough ρ)
lemma mute_p(v:Tq)(u:v.card=2)(g:Even i.card)(h:Even j.card):crumb (poke i*poke j) v=crumb (poke i) v*Pastry.mast (poke j)+crumb (poke j) v*Pastry.mast (poke i):=by
 have hx:v≠∅:=fun t=>by rw [t,card_empty] at u; omega
 have ht:(poke ∅)=(1:FC ρ):=Poly.tag_void _
 by_cases a:i=∅; · subst i; rw [ht,one_mul,←ht,Pastry.mast,Pastry.mast,Pastry.chip ∅ v, Pastry.chip ∅ ∅]; simp [hx]
 by_cases b:j=∅; · subst j; rw [ht,mul_one,←ht,Pastry.mast,Pastry.mast,Pastry.chip ∅ v,Pastry.chip ∅ ∅]; simp [hx]
 have hy: i.card+j.card>2:=by obtain ⟨l,lh⟩:=g; obtain ⟨s,sh⟩:=h; have hl:= card_pos.mpr (nonempty_iff_ne_empty.mpr a); have hs:=card_pos.mpr (nonempty_iff_ne_empty.mpr b); omega
 rw [Pastry.mast,Pastry.mast,Pastry.chip j ∅,Pastry.chip i ∅,if_neg (Ne.symm a),if_neg (Ne.symm b),mul_zero,mul_zero,zero_add]
 rw [poke,poke,Poly.tag_mul]; split; rename_i hz; swap; exact rfl
 rw [crumb_scale,show crumb ((cane ρ).tag _) v=_ from (Pastry.chip (i∪j) v),if_neg (fun p=>by apply not_lt_of_ge _ hy; rw [←card_union_of_disjoint hz, ←p,u]),mul_zero]
lemma pupa(v:Tq)(u:v.card=2): crumb (A*B).val v= crumb A.val v *Pastry.pane B+Pastry.pane A* crumb B.val v:=by
 change crumb (A.val*B.val) v=_; let f(i:Tq):= crumb A.val i • poke i; let g(i:Tq):= crumb B.val i • poke i
 let S:Tq:= univ; let Q:= Wheat S; have ht:A.val=∑ i∈Q,f i:=(fineShape A).pin; have hx:B.val=∑ i∈Q,g i:=(fineShape B).pin
 change crumb (A.val*B.val) _= crumb A.val v*crumb B.val ∅+crumb A.val ∅*crumb B.val v; rw [ht,hx,sum_mul]; simp_rw [crumb_sum,sum_mul, mul_sum, crumb_sum]; rw [←sum_add_distrib]; apply sum_congr rfl; intro i p; rw [←sum_add_distrib]; apply sum_congr rfl; intro j h; unfold f g; rw [Algebra.mul_smul_comm,Algebra.smul_mul_assoc]; simp_rw [crumb_scale]; rw [mute_p i j v u (mem_filter.mp p).2 (mem_filter.mp h).2]; unfold Pastry.mast; ring -- tune
lemma ion_P(v:Tq)(u:v.card=2)(p:Pastry.pane A=0): crumb (exp A).val v=crumb A.val v:=by
 let L:Dough ρ→L[ℝ]ℂ:= LinearMap.toContinuousLinearMap {toFun:=fun i=>crumb i.val v,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl}
 let V(n:ℕ):=(n.factorial:ℝ)⁻¹ • A^n; change L (exp A)= _; have hp :Summable V:= expSeries_summable' (𝕂:=ℝ) A
 rw [show exp A= _ from (show exp A=∑' i,V i from congrFun (exp_eq_tsum ℝ) A), L.map_tsum hp,tsum_eq_single 1]; swap
 · intro i t; unfold V; rw [map_smul,show L (A^i)=0 from ?_,smul_zero]; obtain _|(_|i):=i
   · rw [pow_zero]; exact Matrix.one_apply_ne' (fun h=>by rw [←h,card_empty] at u; omega) -- tune
   · simp at t
   change crumb (A^(i+1+1)).val v=0; rw [pow_succ,pupa _ _ _ u,p,show Pastry.pane _=0 from (by change panHom ρ (A^(i+1))=0; rw [map_pow,show panHom ρ A=0 from p]; exact zero_pow (by omega)),zero_mul,mul_zero,zero_add]
 unfold V; simp only [Nat.factorial_one,Nat.cast_one,inv_one,pow_one,one_smul]; rfl
variable (p₀ q₀:Single n)(X₀:Scree.Hub n){F G:InkD n}
local notation "Rra"=> LeanV (Single n)
local notation "H"=> X₀.val.2
local notation "LΣ"=> X₀.val.1
local notation "Θ"=> Haro.tray p₀ q₀
variable (K L: Cipher n)
lemma peak_l (p: Pastry.pane K=0): orbitPH (exp K-1)=orbitPH K:=by
 ext i j
 let v:Finset Rra:=Haro.tray i j; have he:v.card=2:=by simp [v,Haro.tray ]
 unfold Haro.orbitPH; simp only [Matrix.of_apply,Prism.port_eq]; split; rfl
 apply congrArg; change crumb (exp K).val v- (1:FC Rra) v ∅ = _; rw [ion_P K v he p, show (1:FC Rra) v ∅=0 from ?_,sub_zero]; simp [v,Haro.tray] -- tune
lemma pay_U (p:Pastry.pane K=0): orbitPH (K*L)=Pastry.pane L • orbitPH K:=by
 ext i j; let T:Finset Rra:= Haro.tray i j; have he:T.card=2:=by simp [T,Haro.tray ]
 unfold Haro.orbitPH; simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply,Prism.port_eq]; split; rw [mul_zero]
 next p'=> rw [pupa K L T he,p,zero_mul,add_zero]; ring
end YM.CF.Moto
