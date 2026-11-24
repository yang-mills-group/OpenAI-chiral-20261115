import GaugeFieldConstruction.Alcyon
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
open Phys
local notation "Jφ" => Cauchy.J Phys.Spair
variable (P:Op (Single n))(h₁:ℝ)
abbrev WaC(x:Cover):= ArcK x × ArcK x
def rayK(b:Bool)(d:Axis):Module.End ℂ Jφ:=if b then Cauchy.onSecond (stride true d) else Cauchy.onFirst (stride false d)
lemma sold_R(i j:Tagφ)(d:Axis):rayK true d (wedgeCR i j)=Cauchy.times' (primeF i) (stride true d (primeF j)):= by rw [rayK,if_pos rfl]; exact Cauchy.second ..
lemma sold_L(i j:Tagφ)(d:Axis): rayK false d (wedgeCR i j)= Cauchy.times' (stride false d (primeF i)) (primeF j):=by rw [rayK,if_neg Bool.false_ne_true]; exact Cauchy.first ..
abbrev Palm (u:WaC x):= wedgeCR u.1.2 u.2.2
def SAP(x:Cover)(f:WaC x→ℂ):Jφ:=∑ i,f i • Palm x i
def Ox (x:Cover)(s: WaC x→ℂ): (WaC x→ℂ) →ₗ[ℂ] Jφ where
 toFun t:= SAP x (t*s)
 map_add' a b:=by unfold SAP; simp_rw [add_mul,Pi.add_apply,add_smul]; rw [sum_add_distrib]
 map_smul' a b:=by unfold SAP; simp_rw [Pi.mul_apply]; simp only [Pi.smul_apply,RingHom.id_apply,smul_sum, smul_eq_mul,smul_smul,mul_assoc]
-- `$mom m≤2` economy.
abbrev Php (b:Bool)(p:Axis): WaC x→ℂ:=fun i=> ↑(wing x (if b then i.2 else i.1) p)
abbrev Marlox : WaC x→ ℂ:=Function.uncurry (Skor h₁ x P)
abbrev PHale (x:Cover)(φ:WaC x→ℂ)(m k:ℕ):Jφ:= ∑ u:WaC x,φ u • Cauchy.times' (Rift x false m u.1) (Rift x true k u.2)
variable (H':Dialat x P)
include H' w
lemma Soilt : Ox x (Marlox x P h₁) (1:WaC x→ℂ)= goldΦ (markJet (Θk n x) P h₁).1:=by
 change SAP x _=_; unfold SAP; simp_rw [one_mul]; rw [Fintype.sum_prod_type]; exact Ph0 h₁ x w P H' -- tune
lemma Lui (b:Bool)(p:Axis): Ox x (Marlox x P h₁) (Php x b p) = axisCost b • goldΦ ((markJet (Θk n x) P h₁).2.1 (Twing b p)):=by
 let V:=Twing b p; rw [← Ph1 h₁ x w P H']; change SAP x _= axisCost b • ∑ i, ∑ j, _; unfold SAP; rw [Fintype.sum_prod_type,smul_sum]; apply sum_congr rfl; intro i _; rw [smul_sum]; refine sum_congr rfl fun j _=>?_ ; have he:=dockP x w i j b p; let X:=KnotΛ (n:=n) x i j; let Z:=Skor h₁ x P i j; change (Php x b p (i,j)*Z) • wedgeCR i.2 j.2=axisCost b •(((Complex.I*↑(X V))*Z) • _)
 rw [smul_smul]; apply congrArg (fun u:ℂ=>u • wedgeCR i.2 j.2); rw [← mul_assoc (axisCost b),show Php x b p (i,j)=axisCost b * (Complex.I*↑(X V)) from (by cases b <;> exact he.symm)]
lemma Lille (b c:Bool)(p q:Axis): Ox x (Marlox x P h₁) (Php x b p*Php x c q)= (axisCost b* axisCost c) • goldΦ ((markJet (Θk n x) P h₁).2.2.val (Twing b p) (Twing c q)):=by
 rw [← Ph2 h₁ x w P H']; let A:=axisCost b; let B:=axisCost c; change SAP x _=(A*B) • ∑ i,∑ j,_; unfold SAP; rw [Fintype.sum_prod_type,smul_sum]; apply sum_congr rfl; intro i _; rw [smul_sum]; refine sum_congr rfl fun j _=>?_
 let U(k:Views):= Complex.I*(KnotΛ (n:=n) x i j k:ℂ); let Z:=Skor h₁ x P i j; change ( (Php x b p (i,j)* Php x c q (i,j))*Z) • _=(A*B) • ((U _*U _)*Z) • _
 have he(b:Bool)(p): Php x b p (i,j)=axisCost b*U (Twing b p):=by cases b; exact (dockP x w i j false p).symm; exact (dockP x w i j true p).symm
 rw [he,he,smul_smul]; apply congrArg (fun x:ℂ=>x • _); unfold A B; ring -- tune
omit w H'
variable (ρ:WaC x→ℂ)
abbrev Coneφ (x:Cover)(b:Bool)(p:Axis): WaC x→ℂ:=Php x b p + μCloud p • 1
def Ρphi (x:Cover)(b:Bool)(p q: Axis):WaC x→ℂ:= (1/2:ℂ) • (Php x b p * Php x b q + (μCloud q • Php x b p+ μCloud p • Php x b q) + pool p q • 1)
lemma cone_L (x:Cover)(p) (i j:ArcK x):Coneφ x false p (i,j)=(wing x i p:ℂ)+ μCloud p:=by change (wing x i p:ℂ)+μCloud p*1=_; rw [mul_one]
lemma cone_R (x:Cover)(p) (i j:ArcK x): Coneφ x true p (i,j)= (wing x j p:ℂ)+ μCloud p:=by change (wing x j p:ℂ)+μCloud p*1=_; rw [mul_one]
lemma phi_L (x:Cover)(p q) (i j:ArcK x): Ρphi x false p q (i,j)=ρQ x i p q:=by unfold Ρphi ρQ; let P:=Php x false; change ((1:ℂ)/2)*(↑(wing x i p)*↑(wing x i q)+ (μCloud q*↑(wing x i p)+μCloud p*↑(wing x i q))+pool p q*1)= _; ring
lemma phi_R (x:Cover)(p q) (i j:ArcK x): Ρphi x true p q (i,j)=ρQ x j p q:=by unfold Ρphi ρQ; change ((1:ℂ)/2)*(↑(wing x j p)*↑(wing x j q)+ (μCloud q*↑(wing x j p)+μCloud p*↑(wing x j q))+pool p q*1)= _; ring
-- stitch algebra
lemma Ω_n (k:WaC x→ℂ) : Ox x ρ k= ∑ i,k i • ρ i • Palm x i:=by change SAP x _=_; unfold SAP; exact sum_congr rfl fun i _=>mul_smul ..
lemma Ω_0: PHale x ρ 0 0= Ox x ρ 1:=by unfold PHale; rw [Ω_n]; exact sum_congr rfl (fun u _=>by change _=(1:ℂ) • (ρ u • Palm x u); rw [one_smul,Rift_0,Rift_0]; try rfl)
lemma Ω_L1: PHale x ρ 1 0= ∑ p:Axis, rayK false p (Ox x ρ (Coneφ x false p)):=by
 simp_rw [Ω_n,map_sum,map_smul]; rw [sum_comm]; refine sum_congr rfl fun i _=>?_ ; rw [Rift_1,Rift_0,map_sum (_:Cauchy.J Mode→ₗ[ℂ] Cauchy.J Mode →ₗ[ℂ] Jφ),LinearMap.sum_apply,smul_sum]; refine sum_congr rfl fun p _=>?_; rcases i with ⟨i,j⟩; unfold Palm; rw [map_smul,LinearMap.smul_apply, cone_L,sold_L]; exact smul_comm .. -- tune unfolding
lemma Ω_R1: PHale x ρ 0 1= ∑ p:Axis, rayK true p (Ox x ρ (Coneφ x true p)):=by
 simp_rw [Ω_n,map_sum,map_smul]; rw [sum_comm]; apply sum_congr rfl; intro i _; rw [Rift_1,Rift_0,map_sum,smul_sum]; apply sum_congr rfl; intro p _; rcases i with ⟨i,j⟩; unfold Palm; rw [map_smul, cone_R, sold_R]; exact smul_comm ..
lemma Ω_LL: PHale x ρ 2 0=∑ p:Axis,∑ q:Axis, rayK false p (rayK false q (Ox x ρ (Ρphi x false p q))):=by
 simp_rw [Ω_n,map_sum,map_smul, sum_comm (s:=(univ:Finset Axis)) (t:=(univ:Finset (WaC x)))]; apply sum_congr rfl; intro i _; rw [Rift_2,Rift_0,map_sum Cauchy.times',LinearMap.sum_apply,smul_sum]; apply sum_congr rfl; intro p _; rw [map_sum,LinearMap.sum_apply,smul_sum]; apply sum_congr rfl; intro q _; rcases i with ⟨a,b⟩; unfold Palm; rw [map_smul,LinearMap.smul_apply,sold_L,phi_L, show ∀ i x y,rayK false i (Cauchy.times' x y)= Cauchy.times' ((stride false i) x) y from (fun _ _ _=> Cauchy.first ..)]; exact smul_comm ..
lemma Ω_RR: PHale x ρ 0 2=∑ p:Axis,∑ q:Axis, rayK true p (rayK true q (Ox x ρ (Ρphi x true p q))):=by
 simp_rw [Ω_n,map_sum,map_smul,sum_comm (s:=(univ:Finset Axis)) (t:=(univ:Finset (WaC x)))]; apply sum_congr rfl; intro i _; rw [Rift_2,Rift_0,map_sum,smul_sum]; apply sum_congr rfl; intro p _; rw [map_sum,smul_sum]; apply sum_congr rfl; intro q _; rcases i with ⟨a,b⟩; unfold Palm; rw [map_smul,sold_R,phi_R, show ∀ i x y,rayK true i (Cauchy.times' x y)= Cauchy.times' x ((stride true i) y) from (fun _ _ _=> Cauchy.second ..)]; exact smul_comm ..
lemma Ω_LR: PHale x ρ 1 1=∑ p:Axis,∑ q:Axis, rayK false p (rayK true q (Ox x ρ (Coneφ x false p*Coneφ x true q))):=by
 simp_rw [Ω_n,map_sum,map_smul,sum_comm (s:=(univ:Finset Axis)) (t:=(univ:Finset (WaC x)))]; apply sum_congr rfl; intro i _; rw [Rift_1,Rift_1,map_sum Cauchy.times',LinearMap.sum_apply,smul_sum]; apply sum_congr rfl; intro p _; rw [map_sum, smul_sum]; apply sum_congr rfl; intro q _; rcases i with ⟨a,b⟩; unfold Palm; rw [map_smul (Cauchy.times'), map_smul,LinearMap.smul_apply,sold_R,Pi.mul_apply,cone_L,cone_R, show ∀ i x y,rayK false i (Cauchy.times' x y)= Cauchy.times' ((stride false i) x) y from (fun _ _ _=> Cauchy.first ..)]; simp only [smul_smul]; congr 1; ring
-- Lead.Free.M dims. sew Shipment
abbrev FacV (b:Bool)(d:Axis)(X:OneF Views Pal): Jφ:=axisCost b • rayK b d (goldΦ (X (Twing b d)))
abbrev InPhi (b:Bool)(X:OneF Views Pal): Jφ:=∑ p:Axis,FacV b p X
def R2Θ (p q:Axis)(b v:Bool)(X:TwoF Views Pal) := rayK b p (rayK v q ((axisCost b*axisCost v) • goldΦ (X (Twing b p) (Twing v q)))) -- tune
abbrev InPowΦ (b:Bool)(X: TwoF Views Pal): Jφ:= ∑ p:Axis,∑ q:Axis,(1/2:ℂ) • R2Θ p q b b X
abbrev InSugar (X: TwoF Views Pal): Jφ:= ∑ p:Axis,∑ q:Axis,R2Θ p q false true X
local notation "ZX" => Marlox x P h₁
include H' w
lemma φState: let U:= winJ (Θk n x) M h₁ P; PHale x (Marlox x P h₁) 0 0=goldΦ U.1 ∧ (U.1=0→ PHale x (Marlox x P h₁) 1 0=InPhi false U.2.1 ∧ PHale x (Marlox x P h₁) 0 1= InPhi true U.2.1) ∧ (U.1=0→ U.2.1=0→ PHale x (Marlox x P h₁) 2 0=InPowΦ false U.2.2.val ∧ PHale x (Marlox x P h₁) 0 2= InPowΦ true U.2.2.val ∧ PHale x (Marlox x P h₁) 1 1= InSugar U.2.2.val):=by
 intro U; let Z:=markJet (Θk n x) P h₁; have he:= Servers M x w P H' h₁; let F:=Ox x (Marlox x P h₁); have hp:F 1=goldΦ U.1:= (Soilt x w P h₁ H').trans (congrArg goldΦ he.1.symm); refine ⟨(Ω_0 ..).trans hp,?_,?_⟩
 · intro e; have v:= he.2.1 e; have hx(b:Bool)(p:Axis):rayK b p (F (Coneφ x b p))=FacV b p U.2.1:=by
      unfold Coneφ; rw [map_add,map_smul,hp,e,map_zero,smul_zero,add_zero,show F _= axisCost b • goldΦ _ from Lui x w P h₁ H' b p,map_smul]; unfold FacV; rw [v]
   rw [Ω_L1,Ω_R1]; exact ⟨sum_congr rfl fun p _=>hx false p,sum_congr rfl fun p _=>hx true p⟩
 intro e h; have v:= he.2.2 e h; have hz: F 1=0:=by rw [hp,e,map_zero]
 have hy (b:Bool)(p:Axis): F (Php x b p)=0:=by rw [show F _=axisCost b • goldΦ _ from Lui x w P h₁ H' b p,← (show U.2.1=Z.2.1 from he.2.1 e),h,show (0:OneF Views Pal) _=0 from rfl,map_zero,smul_zero]
 have hP (p q:Axis)(b v':Bool): rayK b p (rayK v' q (F (Php x b p*Php x v' q)))= R2Θ p q b v' U.2.2.val:=by rw [show F _= _ from Lille x w P h₁ H' b v' p q, R2Θ, v]
 have hw(p q:Axis)(b:Bool): rayK b p (rayK b q (F (Ρphi x b p q)))=(1/2:ℂ) • R2Θ p q b b U.2.2.val:=by
    unfold Ρphi; simp only [map_smul F,map_add F,hy,hz, smul_zero,add_zero]; rw [map_smul,map_smul,hP]
 let c(p:Axis):=Coneφ x true p
 rw [Ω_LL,Ω_RR,Ω_LR]; refine ⟨sum_congr rfl fun i _=>sum_congr rfl fun p _=>hw i p false,sum_congr rfl fun i _=>sum_congr rfl fun p _=>hw i p true, sum_congr rfl fun i _=> sum_congr rfl fun j _=>?_⟩
 have hx:F (Coneφ x false i*c j)=F (Php x false i*Php x true j):=by
    unfold c Coneφ; simp only [add_mul,mul_add,mul_smul_comm, Algebra.smul_mul_assoc,one_mul,mul_one,map_add F, map_smul F,hy,hz,smul_zero,add_zero]
 change rayK _ i (rayK _ _ (F (Coneφ _ _ _ * c j)))=_; rw [hx,hP] -- tune
end YM.CF.XGarden.MastTin.ArtCart
end
