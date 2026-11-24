import YM.CF.DPress.Yarn.White
import YM.CF.DPress.Yarn.Star
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
set_option maxHeartbeats 400000
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
open Thrift RoomF
variable {F: RoomF J Λ M Δ}(D:Crib F n)
namespace Crib
open Silo
local notation "jS" j:max=> Dh V M B (n-1-j) j
local notation "jA" j:max=> cell M B R.L j
local notation "jO" j:max=> Λ.O (hat R.L x j)
local notation "jC" j:max=> Tew.tiny R (hat R.L x j)
local notation "Xt" j:max=> venue D j
open Cap
variable (Z: Lore M B R A.μ)
structure Coast {I:Type}[TopologicalSpace I]{d:Side}(u:I→ LogH d):Prop where
 f: LampF (fun i=>(u i).fuel.1)
 k: ∀ (j:Force d)(v:Orbit d),Continuous (fun i=>(u i).fuel.2 j v)
 sig: Continuous fun i=>(u i).r
 β :Continuous fun i=>(u i).δ
local notation "TK"=>Thrift.σ
local notation "u@" j:max=> Tew.tiny R (hat R.L x j)
local notation "ht@" j:max=> hat R.L x j
section
variable {I:Type}[TopologicalSpace I][FirstCountableTopology I][Nonempty I]
lemma coast_const {d:Side}(f:LogH d):Coast (fun _:I=> f):=⟨fun _ _=>continuous_const,fun _ _=>continuous_const,continuous_const,continuous_const⟩
set_option maxRecDepth 4096 in
lemma practice (g:i<n){f:I→ LogH (cell M B R.L (i+1))}{b:I→ℝ}(c:Continuous b)(Y:Coast f)(t:∀ j:I,matchedX (hat R.L x (i+1)) (b j))(v:∀ j:I,D.stipend_h (i+1) (f j) (Tew.tiny R (hat R.L x (i+1))) none): ∃ w:I→ LogH (cell M B R.L i), Coast w ∧ ∀ z:I,Spell D Z i (b z) 0 (f z) (w z):=by
 let U'(z):= D.lowX g (t z) (f z) (v z); let S:= D.σp i g; let p₀(z):HonestL (U' z):= D.litX (v z) g (t z); let T:= (Z i); let K:Silo.Can (D.locale i g) P_ (jO i).δ 0:= base0 (jO i).pos; let y(z):= postH D (b z) (U' z) T 0 (p₀ z) K
 have hp: Families b U':= ⟨c,fun i j _=> Y.f i j,fun i j _=> Y.k i j⟩; obtain ⟨m,u,v⟩:= S.returns (z:=fun _=>0) T hp p₀ continuous_const (fun j=>K); refine ⟨y,⟨u,v,(Urban.workshop S.p S.u hp p₀).1,m⟩,fun i=>Spell.via g (U' i) (p₀ i) K rfl rfl rfl⟩
end
-- trial betas
abbrev θ₁ (R:Patch)(v:StarPS n) := Cap.wake (fun _ => Thrift.σ R) v
abbrev b_T (c:StarPS n)(j:ℕ) := D.β j + ∑ i∈Finset.range j, θ₁ R c i
lemma curveB(i:ℕ) : Continuous fun c:StarPS n=> D.b_T c i:= by unfold b_T; exact continuous_const.add (continuous_finsetSum _ fun j _=> Cap.wakeC (fun _=>TK R))
lemma δT (b:StarPS n)(i:ℕ) : |D.b_T b i-D.β i| ≤ (i:ℝ)* Thrift.σ R:=by rw [b_T,add_sub_cancel_left]; exact (Finset.abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun j _=> Cap.wakeB (fun _=>TK R) b (Thrift.σpos (V:=V)).le).trans_eq (by simp))
lemma βnarrow(h:i≤ n) : 3/4*hat R.L x i ≤ D.β i∧D.β i≤ (3/2:ℝ)*hat R.L x i:= narrow_β V C.w C.p C.i (Ntop P_) Δ M F.legal n D.β D.head i F.bloom.census.hp0 F.bloom.census.fax h
include D in
lemma wage : (i:ℝ)*Thrift.σ R ≤ hat R.L x i/16:=by unfold Thrift.σ hat; linarith [F.bloom.census.hp0]
lemma variant(b:StarPS n) (g:i≤n) : matchedX (hat R.L x i) (D.b_T b i):=by obtain ⟨a,h⟩:= D.βnarrow g; unfold matchedX; rcases abs_le.mp ((δT D b i).trans (D.wage)) with ⟨u,v⟩; constructor<;> linarith [F.now i]
lemma τ_T(b:StarPS n)(i:ℕ): D.b_T b (i+1)+D.toll i=D.b_T b i+θ₁ R b i:=by unfold b_T toll; rw [sum_range_succ]; ring -- no λC
local instance :Nonempty (StarPS n):= ⟨⟨0,by rw [norm_zero]; exact zero_le_one⟩⟩
lemma officeT : ∃ (Y:∀ i,StarPS n→ LogH (cell M B R.L i)),Y n=(fun _=>0) ∧ (∀ i,i ≤ n→ Coast (Y i) ∧ ∀ c:StarPS n,D.stipend_h i (Y i c) (Tew.tiny R (hat R.L x i)) none) ∧∀ i, i<n →∀ c,Spell D Z i (D.b_T c (i+1)) 0 (Y (i+1) c) (Y i c) :=by
 let P(i:ℕ)(Y:StarPS n→LogH (cell M B R.L i)):Prop:= Coast Y∧∀ c:StarPS n,D.stipend_h i (Y c) (Tew.tiny R (hat R.L x i)) none
 let V(i:ℕ)(T:StarPS n→LogH (cell M B R.L (i+1)))(u:StarPS n→LogH (cell M B R.L i)): Prop:=∀ c,Spell D Z i (D.b_T c (i+1)) 0 (T c) (u c)
 let w:StarPS n→LogH (cell M B R.L n):=fun _=>0; have hp:P n w:= ⟨coast_const (I:=StarPS n) _,fun v=> (D.rank_none _ _).1 ⟨(Léon.zero C.uB).more C.uB (F.epoch n).tax.Dust0.tiny.le,SecureD.zero⟩⟩
 obtain ⟨y,t,v,g⟩:= LogH.book _ 0 n (by omega) P V w hp fun i _ p T (g:P (i+1) T)=> show ∃ y,P i y∧V i T y from (by obtain ⟨y,v',q⟩:= practice D Z p (curveB D (i+1)) g.1 (fun t=>D.variant t p) g.2; exact ⟨y,⟨v',fun t=>((q t).core D Z (g.2 t)).1⟩,q⟩)
 refine ⟨y,t,fun i p=>v i (by omega) p, fun i p=>g i (by omega) p⟩
end Crib
end FitD
end YM.CF.Py.Kay
