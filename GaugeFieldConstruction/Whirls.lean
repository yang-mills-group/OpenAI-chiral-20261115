import GaugeFieldConstruction.Burley
import GaugeFieldConstruction.Synod
import YM.UVNext.PRICED_KERNELS.Basin
import YM.CF.Yaw.Viv
import GaugeFieldConstruction.Plaid
import GaugeFieldConstruction.Corbie
/- Gauge average phase extensions. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
-- nongauge Hot support label
open Roots GJ Mew Wosk
open Tenant Push.AbsoluteSums Trees
open Sour Sour.SliceRoof
variable (I:Type)[LinearOrder I][Fintype I]
variable {e a d b c k u f E:ℝ}(F:Elm n Unit e a c)(R:Loom n)(k u:ℝ)(p:BudgetPoint)(m:ℕ)(b0:ℝ)(T:Ids n)
local notation "Y"=>Single n
local notation "B_"=>LoreM n I Unit
local notation "eV"=>eBook I F R u m b0 T
local notation "Kern"=> street I F R u m b0 T
variable (v:Roof n u k m R)(h:k<e)(hp:0<e)(v0:0≤ b0)(tK:coinH f b0)(z:hud_T 7 f)(t:1≤f)(w:p.threshold ≤ u)(s:p.order≤6) (hb:0≤b)
include v h hp v0 tK z t w s hb
local notation "A"=> ρperk a m
omit v h hp tK z t w s hb
lemma Desk_p (p:0<e):0≤ DeskK b0 e:=by unfold DeskK composeCost; positivity
omit v0
lemma leafage {V G:Type*}[AddCommMonoid G](f:V→ G)(L:Finset V): (L.toList.map f).sum=L.sum f:=Finset.sum_map_toList .. -- check
variable (ha:0<a)
include ha hp v0
lemma Arm_C (b:ℝ)(i j:Y): Lee (eV i j) (fun v=>weightV A b v)≤ DeskK b0 e* saleM a F.W i j:=by
 unfold eBook; rw [mapA]; let L:= Finset.univ.filter (fun S=> F.W S i j≠0); let g(S):= weightV A b (LemKer I F R u m b0 T i j S)
 have ht(S:Hubber n):0≤F.W S i j:=(F.coat S|>.1 ()|>.expo i j).positive
 have hG(S): g S≤ DeskK b0 e*(rent a S*F.W S i j):=by
    change rent A _ * b^(List.length ([]:List I))*(_*_) ≤_; rw [List.length_nil,pow_zero,mul_one]; exact (mul_le_mul_of_nonneg_right (rent_policy (j:=m) (X:=S) ha.le) (mul_nonneg (Desk_p _ v0 hp) (ht _))).trans_eq (by ring) -- tune namespace order
 unfold saleM; rw [mul_sum,Lee,leafage]; refine (sum_le_sum (fun i _=>hG i)).trans (sum_le_sum_of_subset_of_nonneg (subset_univ L) (fun i _ _=>mul_nonneg (Desk_p _ v0 hp) (mul_nonneg (Real.exp_pos _).le (ht i))))
omit ha hp v0
lemma seed_fee (i j:Y)(a b:ℝ): Lee (unitK I i j) (fun v=> weightV a b v) =if i=j then Real.exp a else 0:=by
 unfold unitK; split; · simp [baseK,Lee,weightV]
 · rfl
include ha hp v0
abbrev Rack0(a b c e:ℝ)(m:ℕ):ℝ:= Real.exp (ρperk a m)+ DeskK b e*c
lemma street_U (b:ℝ) : let h(i j):=Lee (Kern i j) (fun v=>weightV A b v); let R:=Rack0 a b0 c e m; (∀ i,∑ j,h i j ≤R)∧ ∀ j,∑ i,h i j≤R:=by
 intro g V0; have he(i j:Y) :g (true,i) (false,j) = if i=j then Real.exp A+Lee (eV j i) (weightV A b) else Lee (eV j i) (weightV A b):=by unfold g; change Lee (unitK I i j++eV j i) _=_; rw [appA,seed_fee]; split <;> simp
 have hh(i j:Y):g (true,i) (true,j)=0:=rfl; have hs(i j:Y):g (false,i) (true,j)=g (true,j) (false,i):=by
    unfold g street; rw [appA,appA,mapA,seed_fee,seed_fee]; congr 1; split_ifs<;>first|rfl | aesop
 have hw(i j:Y):g (false,i) (false,j)=0:=rfl
 have hx (i j:Y): g (true,i) (false,j) ≤ (if i=j then Real.exp A else 0)+DeskK b0 e*saleM a F.W j i:=by rw [show g (true,i) (false,j)= Lee (unitK I i j) (weightV A b)+Lee (eV j i) (weightV A b) from appA (unitK I i j) (eV j i) _ ,seed_fee]; exact add_le_add le_rfl (Arm_C I F R u m b0 T hp v0 ha b _ _)
 have hy (i:FinV n): ∑ j,g i j≤ V0:=by
    obtain ⟨w,i⟩:=i; rw [Fintype.sum_prod_type,Fintype.sum_bool]; cases w
    · simp_rw [hw,hs,sum_const_zero]; simp only [add_zero]; apply (sum_le_sum fun j _=> hx j i).trans; rw [sum_add_distrib, sum_ite_eq', if_pos (mem_univ _),←mul_sum]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (F.bank.rows _) (Desk_p _ v0 hp))
    simp_rw [hh,sum_const_zero]; rw [zero_add]; refine (sum_le_sum fun j _=> hx i j).trans ?_; rw [sum_add_distrib,sum_ite_eq,if_pos (mem_univ _),←mul_sum]; exact add_le_add le_rfl (mul_le_mul_of_nonneg_left (F.bank.cols _) (Desk_p _ v0 hp)) -- tune Bool order & ite
 refine ⟨hy,fun j=>?_⟩; refine le_trans (Eq.le ?_) (hy j); apply sum_congr rfl; rintro ⟨b,i⟩ v; obtain ⟨l,j⟩:=j; cases b <;>cases l <;> first|rfl | exact hs _ _ | exact (hs _ _).symm
omit hp ha v0
open UVNext.PricedKernels
abbrev Tubeτ := Bool × SpinIdx × SU.Slot
lemma Aeolus (a:ℝ)(hp:0<a)(x:Seat n): ∑ i:FinV n,Real.exp (-a*separation x (Ekm n i)) ≤ (Fintype.card Tubeτ:ℝ)*UVNext.PricedKernels.basin a:=by
 let f (i:Dwell n): Seat n × Tubeτ:= (node i.2.1.1,i.1,i.2.1.2,i.2.2); have he: Function.Injective f:=by
    rintro ⟨b,⟨⟨x,p⟩,i⟩⟩ ⟨c,⟨⟨y,q⟩,j⟩⟩ v; change (_,_)=(_,_ ) at v; have h:node x=node y:= (Prod.mk.inj v).1; have hv:x=y:=(assembly n).embed_injective (add_right_cancel h); simpa only [f,Prod.mk.injEq,hv,true_and] using v
 let S:= univ.image f; let TT(z:Seat n × Tubeτ):= Real.exp (-a*separation x z.1)
 calc
    _ = ∑ z∈ S,TT z:=by unfold S; rw [sum_image he.injOn]; rfl
    _ ≤ ∑ z,TT z:= sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun i _ _=>(Real.exp_pos _).le)
    _ = _* (∑ y:Seat n, Real.exp (-a*separation x y)):=by rw [Fintype.sum_prod_type]; simp_rw [TT,sum_const,nsmul_eq_mul,mul_sum,card_univ] -- tune
    _ ≤ _:=mul_le_mul_of_nonneg_left (UVNext.PricedKernels.funnel hp x) (show 0≤(↑(Fintype.card Tubeτ):ℝ) from by positivity)
abbrev Track_A(n:Side)(t:ℝ)(x y:Seat n):= Real.exp (-t*separation x y)
variable (G:Type*)
lemma tideV (x:LoreM n I Unit)(p:Grove (terr _) x.seat)(y:Seat n)(t:y∈x.seat)(a h:ℝ)(z:Seat n)(f:x.won≥0)(u:0<b)(hv:h+b≤a)(hb:0≤ d): bil h d x z≤ Track_A n b z y * weightV a d x:=by
 have he:0≤ weightV a d x:=WP_v _ _ _ hb f; unfold bil; split
 · next s =>
    let Rz(a):=Branch.rent a x.seat; have he:Rz h≤ Track_A _ b z y*Rz a:=by
       unfold Rz Track_A Branch.rent; rw [←Real.exp_add]; apply Real.exp_monotone; have hs:(separation z y:ℝ) ≤x.seat.card:=by exact_mod_cast (show separation z y≤x.seat.card from (p.lim z s y t).le)
       nlinarith [mul_le_mul_of_nonneg_right hv (Nat.cast_nonneg (α:=ℝ) x.seat.card)]
    exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he (pow_nonneg hb _)) f).trans_eq (by unfold Rz Branch.rent weightV; ring)
 exact mul_nonneg (Real.exp_pos _).le he
abbrev Pel_A (a b c e d:ℝ)(m:ℕ):= ((Fintype.card Tubeτ:ℝ)*basin d)*Rack0 a b c e m
include v h hp v0 tK z t w s ha hb
lemma BigCred (hc:0≤c)(hd:0< d)(ht:2*d ≤ ρperk a m): FumedH d b (Ekm n) Kern (Rack0 a b0 c e m) (Pel_A a b0 c e d m):=by
 let g:= Ker_Ω I F R k u p m b0 T v h hp v0 tK z t w s
 let P:=street_U I F R u m b0 T hp v0 ha b; let Q:=Rack0 a b0 c e m; let ℓ:=Kern; have hx:0≤Q:= add_nonneg (Real.exp_pos _).le (mul_nonneg (Desk_p _ v0 hp) hc)
 have hB(i j): Lee (ℓ i j) (fun k=>weightV d b k)≤Lee (ℓ i j) (fun k=>weightV (ρperk a m) b k):=by
    apply lea_p; intro k h; apply mul_le_mul_of_nonneg_right _ (g.day i j k h).1.1; apply mul_le_mul_of_nonneg_right _ (pow_nonneg hb _); exact Real.exp_monotone (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _))
 refine ⟨fun i j k u=> (g.day i j k u).1.1,fun i j k t=>(g.day i j k t).2.2,fun i=>(sum_le_sum fun j _=>hB i j).trans (P.1 i),fun i=>(sum_le_sum fun j _=>hB j i).trans (P.2 i),fun y=>?_⟩
 let g1(i:FinV n):= Track_A n d y (Ekm n i); refine le_trans (sum_le_sum (g:=fun i=> g1 i*Q) ?_) ?_
 · intro i u; unfold privH; refine le_trans ?_ (mul_le_mul_of_nonneg_left (P.1 i) (Real.exp_pos _).le); rw [mul_sum]; exact sum_le_sum fun j _=>(lea_p (ℓ i j) _ (fun x=> g1 i*weightV _ b x) (fun t p=> tideV I _ (g.day i j t p|>.2.1) (Ekm n i) (g.day i j t p|>.2.2.1) (ρperk a m) d y (g.day i j t p|>.1.1) hd (by linarith) hb )).trans_eq (lea_scale ..) -- rw tune
 rw [←sum_mul]; exact mul_le_mul_of_nonneg_right (Aeolus d hd y) hx
#print axioms BigCred
end MastTin
end YM.CF.XGarden
end
