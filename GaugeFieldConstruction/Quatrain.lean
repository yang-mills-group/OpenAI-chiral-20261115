import GaugeFieldConstruction.BrightRoot
set_option autoImplicit false
set_option maxRecDepth 5500
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
namespace ArtCart
open Buffered Lifted Girt Skye Window Vale
variable {x y:Cover}{d:ℕ}{k:Side}
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {F H:Paper n}{p:BudgetPoint}{c v h r:ℝ}(M: Male){o:Seat n}
open Spectrix Simmer Next.Rank.Spindle
open Gleam Gleam.Guide Fock.Flux
open Hood
open Py.Rate.LocalLimit.Papal Py.Rate.LocalLimit.Papal.FrameP
variable (x n k)
abbrev crestCard (x:Cover):= jungle x 24
abbrev Shots (n:Side)(x:Cover)(V:Genre) :Type:= crestCard x × (Fin V.orderB → Frills (Θk n x))
abbrev WordUp (i:Wa n): List (Creduct (Single n)):= i.elim [] (fun ⟨b,i,j⟩=>[(!b,i),(b,j)])
lemma Root_hi (i:Single n): RootBay (false,i) = Fock.put i ∧ RootBay (true,i)= Fock.takeF i:=⟨Fock.create_put .., Fock.remove_take ..⟩
lemma Word_roll (i:Wa n): rollC RootBay (WordUp n i)= dot_Q i:=by rcases i with _|⟨b,i,j⟩; rfl; cases b<;> (simp only [WordUp,Option.elim_some,Bool.not_false,Bool.not_true, rollC,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,Root_hi,mul_one]; rfl)
lemma Word_nest (i:jungle x d)(b:ℂ)(S:Hubber n)(w:knotX x d n⊆ S)(p:d<n.val) : nestM (onPage n S) 2 [(b, WordUp n (hereV n i))]:=by
 intro u q; rw [List.mem_singleton.mp q]; rcases i with _|⟨g,c,t⟩; refine ⟨⟨0,rfl⟩,Nat.zero_le _,nofun⟩
 have hp(j:mort x d): hereF n j∈ onPage n S:= mem_filter.mpr ⟨mem_univ _,w (here_Q j p)⟩
 refine ⟨even_two,le_rfl,fun j h=>?_⟩; rcases (show j=(!g,hereF n c)∨j=(g,hereF n t) from by simpa [WordUp,hereV] using h) with rfl|rfl <;> apply hp -- tune
-- factor powers. symbolic sign grade.S PIN tick.V is argument ALtar.Height.
abbrev Keyfee (n k:Side)(x:Cover)(i:crestCard x):= feeV n i*feeV k i
lemma KF_norm (i:crestCard x):‖Keyfee n k x i‖=1:=by rw [Keyfee,norm_mul,feeV_n,feeV_n,one_mul]
variable {n x}
def glossW (k:Side)(x:Cover)(U:Genre)(F:Paper n)(v:Shots n x U): Rope k :=
 ((Keyfee n k x v.1*pracR (Θk n x) F U (hereV n v.1) v.2, WordUp k (hereV k v.1)), List.ofFn fun i:Fin U.orderB=> coupon x k (v.2 i))
def Vanguard (k:Side)(x:Cover)(U:Genre)(F:Paper n):Ropes k:= univ.toList.map (glossW k x U F)
lemma grade2 (V:Genre): V.orderB ≤2:=by cases V<;>decide
abbrev LarkD (k:Side)(x:Cover)(F:Paper n)(U:Genre)(H: Confab (Θk n x)): FC (Single k):=∑ i:crestCard x,(Keyfee n k x i * crownx U F (hereV n i) (Θk n x) H) • dot_Q (hereV k i)
lemma dawn_expand (k:Side)(x:Cover)(U:Genre)(F:Paper n)(φ: Tick (More k) SU.group →ℝ): dawn (Vanguard k x U F) φ=LarkD k x F U (fun i=> φ (coupon x k i)):=by
 let V:= fun i:StampSet n x=> φ (coupon x k i); let L:=Shots n x U
 unfold FrameP.dawn Vanguard; rw [List.map_map,Finset.sum_map_toList,Fintype.sum_prod_type]; apply sum_congr rfl; intro i _; let o:= Θk n x; let K:= Keyfee n k x i
 change _= (K * crownx U F (hereV n i) o V) • _; rw [crown_pay,mul_sum,sum_smul]; apply sum_congr rfl; intro j w;
 let Y:= pracR o F U (hereV n i) j; let Q:= List.ofFn fun i:Fin U.orderB=> coupon x k (j i); change (↑(factorV Q φ):ℂ) • ((K*Y) • rollC RootBay (WordUp k (hereV k i)))= (K *((∏ i:Fin U.orderB,V (j i)) • Y)) • _
 have h : factorV Q φ=∏ i:Fin U.orderB,V (j i):=by unfold factorV Q; rw [List.map_ofFn, Fin.prod_ofFn]; try rfl -- name tune
 rw [h,Word_roll,smul_smul, Complex.real_smul, mul_left_comm]
lemma front_p (k:Side)(x:Cover)(U:Genre)(F:Paper n)(β:ℝ)(V:Pane k):propSeed (Vanguard k x U F) β V= LarkD k x F U (fun i=> Real.sqrt β*(coupon x k i).raw V):=dawn_expand .. -- tune
-- uniform V card: use upper via injections into Wa.B.Top fixed.
def Gocost (n:Side):ℕ:= ∑ o:Seat n, (1+Fintype.card (Frills o)) -- bound
lemma shot_k (V:Genre)(x:Cover)(w:300<n.val): (Fintype.card (Shots n x V))≤ Fintype.card (Wa n)*(Gocost n)^2:=by
 unfold Shots; rw [Fintype.card_prod,Fintype.card_fun]; apply Nat.mul_le_mul (Fintype.card_le_of_injective _ (hereI (x:=x) (show 24<n.val from by omega)))
 have ht:1+Fintype.card (Frills (Θk n x))≤ Gocost n:= single_le_sum (f:=fun x:Seat n=> 1+Fintype.card (Frills x)) (fun _ _=>Nat.zero_le _) (mem_univ _)
 rw [Fintype.card_fin]; exact (Nat.pow_le_pow_left (show _ from le_trans (le_add_of_nonneg_left (by decide : (0:ℕ) ≤ 1)) ht) V.orderB).trans (pow_le_pow_right₀ (by omega : 1 ≤ Gocost n) (grade2 V)) -- tune
lemma billReed (U:Genre)(F: Paper n)(w:300<n.val)(u:300<k.val)(h:MatPays F U (Θk n x) r v)(t:0≤r)(S:Support (More k))(p:knotX x temper k⊆ S): Reeds (Vanguard k x U F) stitch 2 S ((Fintype.card (Wa n)*(Gocost n)^2:ℕ)*r):=by
 let L:=glossW k x U F; constructor
 · intro i a; obtain ⟨q,v,rfl⟩:=List.mem_map.mp a; refine ⟨Word_nest k x _ _ _ (can_D x k S p) (by omega),?_,?_⟩ -- tune
   · change (List.ofFn _).length ≤ _; rw [List.length_ofFn]; exact grade2 U
   intro i pK; obtain ⟨i,v,rfl⟩:= (List.mem_ofFn.mp pK); exact acclaim x k S u p _ -- tune
 unfold Vanguard meterK; rw [List.map_map, List.map_map,sum_map_toList]; apply le_trans (sum_le_sum (g:=fun i=>r) fun i _=> (?_: ‖(L i).1.1‖≤ r)); swap
 · unfold L glossW; rw [norm_mul,KF_norm,one_mul]; exact h.bill ..
 rw [sum_const,card_univ,nsmul_eq_mul]; exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (shot_k U x w)) t
end ArtCart
end MastTin
end YM.CF.XGarden
end
