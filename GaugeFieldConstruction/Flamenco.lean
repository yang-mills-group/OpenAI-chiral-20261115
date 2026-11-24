import GaugeFieldConstruction.Froyo
set_option autoImplicit false
set_option maxHeartbeats 48000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden.MastTin.ArtCart
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
open Buffered Lifted Girt Skye Window Vale
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {G H:Paper n}{p:BudgetPoint}{c v h:ℝ}(M: Male){o:Seat n}
open Spectrix Simmer Next.Rank.Spindle
open Gleam Gleam.Guide Fock.Flux
open Py.Rate.LocalLimit.Papal Py.Rate.LocalLimit.Papal.FrameP
open AnalyticBridge VerifiedReset
open Gleam.Guide.Pitcher Coins Fock.Flux Fock.Flux.Pacts
open YM.GaugeFieldConstruction.Wick.Yacht YM.GaugeFieldConstruction.Wick.Yacht.Vesper Violets
-- Epoch hull as quadratures. standard cost coupons
open scoped Kronecker
open YM.GaugeFieldConstruction
variable (x:Cover)(w:300<n.val)
namespace BluffV
open Cauchy
local instance : AddCommGroup ↥P14:= PackP.G.toAddCommGroup
local instance : AddCommGroup ↥P25:= PackM.G.toAddCommGroup
local instance : Module ℂ ↥P14:= PackP.S.toModule
local instance : Module ℂ ↥P25:= PackM.S.toModule
open TableF.Lenten.Loden Phys
variable {b:Bool}
lemma murphy (p:Spin)(i:SU.Slot)(b:Bool): ∑ k:Axis, ∑ a:Spin,coeffCR b k p a • Phys.stride b k (primeF (a,i))=0:= by -- may not import Tissue or convention. prove
 let R:=atop (α:=FIndex) i
 have he: ∑ k:Axis,∑ a:Spin,coeffCR b k p a • Cder b k (C a 0)=0:=by
    apply Row.skin b; intro w; rw [LinearMap.mem_ker]; let q:= w.val.fermi b; change q.read _=0; rw [map_sum]; simp_rw [map_sum,map_smul,smul_eq_mul]; refine Eq.trans ?_ (q.chiral p); apply sum_congr rfl; intro j _; apply sum_congr rfl; intro a _; rw [←LinearMap.comp_apply q.read,q.frequency,LinearMap.smul_apply, Weyl.read_C]; simp only [power, Prod.snd_zero,Prod.fst_zero,pow_zero, one_mul,mul_one,smul_eq_mul]; ring
 have hx(a:Spin)(k:Axis): Phys.stride b k (primeF (a,i))=R (Cder b k (C a 0)):= (Phys.here ..).symm -- primF=atop T
 rw [← show R (0: Cauchy.CJet)=0 from map_zero R]; rw [← he,map_sum]; simp_rw [map_sum,map_smul,hx]
-- push Γ: ∑ X Pin.X. skip commute.
abbrev pelΦ(u:GaugeFieldConstruction.Cauchy.Spin×SU.Slot):=u
private lemma sheetΓ(i:Axis)(b c: Tagφ):skim_L false true (ΓV i) b c= if b.2=c.2 then Hij i b.1 c.1 else 0:=by
 rw [ΓS]; rcases b with ⟨u,x⟩; rcases c with ⟨c,v⟩; change (cliff i ⊗ₖ _ ) _ _=_; simp [Matrix.one_apply,cliff] -- tune
lemma LoomL (u:Fees true)(i:Tagφ)(j:Tagφ)(k:Axis): (skim_L false true (wedgeJ k u).val) i j=∑ a:Spin,Hij k i.1 a*(skim_L true true u.val) (a,i.2) j:=by
 rw [show skim_L false true (wedgeJ k u).val=_ from (packageV (Γχ k) (show salvo true true u.val from u.property.1)).2]; rw [Matrix.mul_apply,Fintype.sum_prod_type]; apply sum_congr rfl; intro a _; rw [sum_eq_single i.2]
 · rw [sheetΓ]; rw [if_pos rfl]
 · intro t _ e; rw [sheetΓ,if_neg (Ne.symm e),zero_mul]
 simp
lemma LoomR(u:Fees false)(i j:Tagφ)(k:Axis): (skim_L false true (wedgeJ k u).val) i j =∑ a:Spin,(skim_L false false u.val) i (a,j.2)*Hij k a j.1:=by
 rw [show skim_L false true (wedgeJ k u).val=_ from (packageV (show salvo false false u.val from u.property.1) (Γχ k)).2]; rw [Matrix.mul_apply,Fintype.sum_prod_type]; refine sum_congr rfl fun a _=>?_; rw [sum_eq_single j.2]
 · rw [sheetΓ,if_pos rfl]
 · intro t _ e; rw [sheetΓ,if_neg e,mul_zero]
 simp
lemma zipY(u:P03)(X:FactIx): sunX X (heelY u)=∑ i:Tagφ,∑ j:Tagφ,(skim_L false true u.val i j) • (rayK X.1 X.2 (wedgeCR i j)):=by
 let V:= rayK X.1 X.2; have ht: sunX X  (heelY u)= V (∑ i:Tagφ,∑ j:Tagφ,u.val (fisc false i) (fisc true j) • wedgeCR i j):=by unfold sunX heelY goldΦ; rw [LinearMap.comp_apply]; congr 1 --
 rw [ht]; simp_rw [map_sum,map_smul]; exact sum_congr rfl fun i _=>sum_congr rfl fun j _=>rfl
lemma kataL (u:Fees true): ∑ k:Axis, sunX (TipO true k) (heelY (wedgeJ k u))=0:=by
 let X:= skim_L true true u.val
 let Stick(k:Axis)(i:Tagφ)(j: Tagφ):J Phys.Spair:= rayK false k (wedgeCR i j); let A(k:Axis)(a:Spin)(j l: Tagφ):= Hij k a j.1 • (X j l • Stick k (a,j.2) l)
 have he(k:Axis): sunX (TipO true k) (heelY (wedgeJ k u))=∑ a:Spin,∑ j:Tagφ,∑ l:Tagφ,A k a j l:=by
    rw [zipY,Fintype.sum_prod_type]; apply sum_congr rfl; intro a _; conv_rhs=> rw [Fintype.sum_prod_type,sum_comm]
    apply sum_congr rfl; intro i _; rw [sum_comm (s:= (univ:Finset Spin))]; refine sum_congr rfl fun j _=>?_; rw [LoomL,Finset.sum_smul]; exact sum_congr rfl fun m _=> by rw [mul_smul]; try rfl
 have hp (j l:Tagφ) :∑ k:Axis,∑ a:Spin,A k a j l=0:=by
    let R:J Mode→ₗ[ℂ]J Spair:=Cauchy.times'.flip (primeF l); have hv(k:Axis)(a:Spin):A k a j l=X j l • R (coeffCR false k j.1 a • Phys.stride false k (primeF (a,j.2))):=by unfold A; rw [map_smul,smul_comm (Hij k a j.1),show ∀ a d, Stick k a d=Cauchy.times' (Phys.stride false k (primeF a)) (primeF d) from fun _ _=>sold_L ..]; try rfl -- tune smul
    simp_rw [hv,← Finset.smul_sum,←map_sum R]; rw [murphy,map_zero,smul_zero]
 simp_rw [he]; simp_rw [Finset.sum_comm (s:=(univ:Finset Spin)) (t:=(univ:Finset Tagφ)), Finset.sum_comm (s:=(univ:Finset Axis)) (t:=(univ:Finset Tagφ)),hp,sum_const_zero]
lemma kataR(u:Fees false):∑ k:Axis,sunX (TipO false k) (heelY (wedgeJ k u))=0:=by
 let X:= skim_L false false u.val; let S(k:Axis)(j l:Tagφ):= rayK true k (wedgeCR j l); let A(k:Axis)(a:Spin)(i j:Tagφ):= X j i • (Hij k i.1 a • S k j (a,i.2))
 have he(k:Axis): sunX (TipO false k) (heelY (wedgeJ k u))=∑ a:Spin,∑ j:Tagφ,∑ l:Tagφ,A k a j l:=by
    rw [zipY,sum_comm, Fintype.sum_prod_type]; apply sum_congr rfl; intro a _; conv_rhs=> rw [Fintype.sum_prod_type,sum_comm]
    apply sum_congr rfl; intro i _; rw [sum_comm (s:=(univ:Finset Spin))]; refine sum_congr rfl fun j _=>?_; rw [LoomR,Finset.sum_smul]; exact sum_congr rfl fun m _=> by rw [mul_smul]; try rfl
 have hp(j l:Tagφ): ∑ k:Axis,∑ a:Spin,A k a j l=0:=by
    let R:J Mode→ₗ[ℂ] J Spair:= times' (primeF l); have hv(k:Axis)(a:Spin): A k a j l=X l j • R (coeffCR true k j.1 a • Phys.stride true k (primeF (a,j.2))):=by unfold A; rw [map_smul,show ∀ a d,S k a d=Cauchy.times' (primeF a) (Phys.stride true k (primeF d)) from fun _ _=>sold_R ..]; try rfl
    simp_rw [hv,← Finset.smul_sum,←map_sum R]; rw [murphy,map_zero,smul_zero]
 simp_rw [he, Finset.sum_comm (s:=(univ:Finset Spin)) (t:=(univ:Finset Tagφ)), Finset.sum_comm (s:=(univ:Finset Axis)) (t:=(univ:Finset Tagφ)),hp,sum_const_zero]
lemma kataP0(u:Fees b): ∑ i:Axis,sunX (TipO b i) (heelY (wedgeJ i u))=0:=by cases b; exact kataR u; exact kataL u
lemma kataP (u:Fees b): μPhi4 (taxW u)=0:=by rw [taxW, map_sum]; simp_rw [scaleG,kataP0]
lemma kataT (v:FactIx)(u:Fees b): μPhi5 (taxΘ v u)=0:=by rw [taxΘ,map_sum]; simp_rw [scaleK, ←map_sum (sunX v), kataP0,map_zero]
-- all PH15 with off-lattice.Y sole charges
lemma αPeak {b}(v:Waves)(Q:PalOne)(q:Oneκ b Q)(e:PH15 b v Q):∃ A:Fees b, bV1 v=taxW A ∧∃ S: FactIx → Fees b,bV2 v= ∑ i, taxΘ i (S i):=by -- tune holder A
 let A: Fees b:= ⟨Q.1,SootΘC q.β⟩ -- name
 let V(i): Fees b:= ⟨Q.2.1 (tipΘ i),SootΘC (q.hr _)⟩
 let H(i:FactIx) : Fees b:= heelC i • V i; have ht(p): Q.2.1 p=∑ i:FactIx,(((tipK i p:ℂ)*(heelC i)⁻¹) • (H i).val):=by
    conv_lhs=> rw [shellΦ p,map_sum]; -- tune multiple.V
    apply sum_congr rfl; intro i _; rw [map_smul,mul_smul]; change _=(tipK i p:ℂ) • ((heelC i)⁻¹ • (heelC i • Q.2.1 _)); rw [inv_smul_smul₀ (heel_v i),Complex.coe_smul]
 have hp(x:Views):=e.landing x
 refine ⟨A,?_,H,?_⟩
 · apply Subtype.ext; apply ContinuousLinearMap.ext; intro p; cases b; rw [ascentR]; exact (hp p).2.1; rw [ascentL]; exact (hp p).2.1
 let X:=∑ i:FactIx,taxΘ i (H i); let Y:Duo Views Pal:=⟨X.val, fun i j=>(X.property i j).2⟩; let P:=chartF v; suffices g: P.2.2=Y from Subtype.ext (congrArg (fun V:Duo Views Pal=>V.val) g); apply dual_uni; intro i; change P.2.2.val i i=X.val i i; unfold X; rw [Submodule.coe_sum, ContinuousLinearMap.sum_apply, ContinuousLinearMap.sum_apply]
 cases b; · rw [(show P.2.2.val i i=_ from (hp i).2.2), ht]; simp_rw [Matrix.sum_mul, sprint_R1,sum_add_distrib]; try rfl
 rw [show P.2.2.val i i= _ from (hp i).2.2, ht]; simp_rw [Matrix.mul_sum, sprint_L1,sum_add_distrib]; try rfl
end BluffV
end YM.CF.XGarden.MastTin.ArtCart
end
