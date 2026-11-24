import GaugeFieldConstruction.Fender
set_option autoImplicit false
set_option quotPrecheck false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 340000
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Scree.Ing
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree
open Skye Scree Vow Hake Jet Fock
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open Cube Lat Tulip Peaks
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
open scoped YM.CF.Mew
open BasisI Roots GJ Mew Lattice.Corona.Hive
open Py.Rate.Pitching.Focus.CoeffArc
open Pastry Grotto
namespace Rio
variable {n:Side}{I:Type}[Fintype I][LinearOrder I]
-- cumulative receipts. Blank includes i's column zero.
def pureX (V:Rio I n):=V.X+V.Y
section
variable {α β J δ E:Type}[Fintype α][Fintype β][Fintype J][Fintype δ]
variable (σ:I→Seat n){S:α→Support (More n)}{z:β→Force n} (Γ:J→ Grotto I S z)(P:BudgetPoint)(U:Orbit n)(v:Rue.FleetS P.threshold U.1)(M:Key I→ β→ Cipher n)(hM:∀ i,River (fun z=>M z i))
local notation "Ω"=> flags P.threshold U.1
local notation "aK"=>payment σ Γ
def quotaΔ (V:Force n→ Cipher n)(f:RegBudget n)(K:ForceBudget n):= exponentL P f U.1 * hum Ω id V + sparkJet Ω V (fun i=>K i U)
lemma aug_sum (f g: RegBudget n)(V:Force n→Cipher n) (K H: ForceBudget n) : quotaΔ P U V (f+g) (K+H)=quotaΔ P U V f K+quotaΔ P U V g H:=by
 have h:exponentL P (f+g) U.1=exponentL P f U.1+exponentL P g U.1:=by unfold exponentL; rw [←sum_add_distrib]; apply Finset.sum_congr rfl; intro i _; unfold numbE; by_cases y:pingS P.threshold i.val.2 U.1 <;> simp[Set.indicator,y]
 unfold quotaΔ; rw [h, add_mul,show (fun i=>(K+H) i U)= (fun i=>K i U)+(fun i=>H i U) from rfl,map_add]; abel
private lemma AugJ (f:δ→ RegBudget n)(g:δ→ForceBudget n)(V:Force n→Cipher n) (S:Finset δ): quotaΔ P U V (∑ i∈S,f i) (∑ i∈S,g i) =∑ i∈S,quotaΔ P U V (f i) (g i):=by
 induction S using Finset.induction with
 | empty=> simp only [sum_empty,quotaΔ,Vale.still_Footprint,zero_mul]; change 0+sparkJet _ _ 0=_; rw[map_zero,zero_add]
 | insert i S h ih=> rw[sum_insert h,sum_insert h,sum_insert h,aug_sum,ih]
lemma κpClip: pureX (aK)=∑ i:J,(Γ i).Rinc σ:=by
 unfold pureX payment Grotto.white Grotto.gray; rw[sum_filter,sum_filter,←sum_add_distrib]; apply sum_congr rfl
 intro i _; split_ifs with h h' h' <;> first|omega|simp
include v hM in
lemma ParameterRise : Kin σ (fun x:Key I=>quotaΔ P U (PourUp z (M x)) (Canz σ _ (pureX (payment σ Γ)) x) (Canz σ _ (payment σ Γ).B x)) (fun x=>∑ i:J,(Γ i).cashVector P x (M x) U) :=by
 change Kin σ (fun x=> quotaΔ P U _ _ (Canz σ _ (∑ i:J,(Γ i).Kinc σ) x)) _
 simp_rw [κpClip,can_pour,AugJ]; exact loft_bank _ _ (fun j _=>turnoverPack σ _ _ _ M hM v)
-- Use µ reader.E Kin.Std.Level.Prior chooses integrands exact.
variable (k:I) (A B: RegBudget n) (E K:Key I→ ForceBudget n) (W:Key I→RegBudget n)
def KidValid (i:I) (x:Grotto I S z) :Prop:=(∀ j:Heart x.anchor S x.needs,i∈ x.fromR j ∨ x.termR j=0∨ x.flag=true) ∧∀ (j:Heart x.anchor S x.needs) (q:Base z (Legist x.anchor S x.needs j) x.flag),i∈ x.fromB j q.val∨ x.termB j q.val=0
lemma Kins (e:∀ j,KidValid k (Γ j)) (x:Key I)(u:x k=0) : Canz σ _ (pureX aK) x=0∧ Canz σ _ (aK).B x=0:=by
 have he {M:Type}[AddCommMonoid M][Module ℂ M]{δ:Type}[Fintype δ][DecidableEq δ](i:δ)(t:List I)(F:M)(h:k∈t∨F=0): Canz σ _ (clipK σ i t F) x=0:=by
    funext b; rw[can_single]; split; swap; · rfl
    rcases h with h|h; · rw [show carR x t=0 from List.prod_eq_zero (List.mem_map.mpr ⟨k,h,u⟩),zero_smul]; rfl
    rw[h,smul_zero]; rfl
 constructor
 · rw[κpClip,can_pour]; refine sum_eq_zero fun i _=>?_; unfold Rinc; rw[can_pour]; refine sum_eq_zero fun j _=>he _ _ _ ((e i).1 j|>.imp_right (fun h=>?_)); rcases h with h|h <;> simp[h]
 change Canz σ _ (∑ j:J, Kinc σ (Γ j)) x=0; rw[can_pour]; refine sum_eq_zero fun i _=>?_ ; unfold Kinc; simp_rw [can_pour]; refine sum_eq_zero fun j _ => sum_eq_zero fun x _=>he _ _ _ ((e i).2 _ _)
private lemma Op_Can (f:XE I (InkD n) n):River (fun x=> exponentL P (Canz σ _ f x) U.1):=by
 unfold exponentL; refine (tip_bank _ _ ?_).1; intro i _; by_cases h:pingS P.threshold i.val.2 U.1; · have H(t):numbE P.threshold i.val.2 t U.1=t U.1:=Set.indicator_of_mem (s:={y|pingS P.threshold i.val.2 y}) h t; simp_rw[H,Canz,Finset.sum_apply, Pi.smul_apply]; exact (tip_bank _ _ (fun i _=>Mew.lift_b i _)).1 -- tune
 unfold numbE; simp_rw [Set.indicator_of_notMem (s:={A|pingS P.threshold i.val.2 A}) (a:=U.1) h]; exact zeroR _
include v hM
-- recipe API. terms add Milestone.Key.Str.
lemma Insert_p (vK:∀ y,PourUp z (M y)=(fun i=>K y i U))(e:∀ j,KidValid k (Γ j)) (h:River fun y=>exponentL P (W y) U.1) : Kin σ
   (fun y=> exp (exponentL P (W y) U.1+exponentL P (Canz σ _ (pureX aK) y) U.1)*fueled P (K y+Canz σ _ (payment σ Γ).B y) U)
   (fun y=> exp (exponentL P (W y) U.1)* fueled P (K y) U + exp (exponentL P (W y) U.1)*(∑ i:J,(Γ i).cashVector P y (M y) U)):=by
 let f(i)(y):=K y i U; let g(i:Force n)(y):=Canz σ _ (payment σ Γ).B y i U
 have ht(i): River (f i):=by
    have he(y):f i y= PourUp z (M y) i:=by unfold f; rw [vK]
    rw[show f i=fun y=>_ from funext he]; exact (tip_bank _ _ (fun j _=> hM j)).1
 have hp(i): River (g i):=by unfold g Canz; simp_rw [Finset.sum_apply,Pi.smul_apply]; exact (tip_bank _ _ (fun j _=>lift_b j _)).1
 have hC(i)(x:Key I)(p:x k=0):g i x=0:=by unfold g; rw[(Kins σ Γ k e x p).2]; rfl
 let W':=fun x:Key I=>exponentL P (W x) U.1; let D:=fun y:Key I=>exponentL P (Canz σ _ (pureX aK) y) U.1
 have hD: River D := Op_Can σ P U (pureX aK); have hδ(z)(p:z k=0): D z=0:=by unfold D; rw[(Kins σ Γ k e z p).1,Vale.still_Footprint]
 have he:=tilt_K (M:=Cipher n) σ Ω f g k ht hp hC W' D h hD hδ
 simp_rw[hum_pay v]; apply he.trans
 have h1:= ParameterRise σ Γ P U v M hM; simp_rw [vK] at h1
 have hT:=turn_hum σ Ω f g k ht hp hC; -- recycled
 have hx:River (fun x=> hum Ω id (fun i=>f i x)):=by
    have hh:=turn_hum (M:=Cipher n) σ Ω f (fun _ _ =>0) k ht (fun i=>zeroR _) (fun _ _ _=>rfl); simpa using hh.1
 apply loft_add (Kin.refl _ (h.exp_V.mul_T hx)) (Kin.mulT (Kin.refl _ h.exp_V) h1)
#print axioms Insert_p
end
end Rio
end YM.CF.Scree.Ing
end
