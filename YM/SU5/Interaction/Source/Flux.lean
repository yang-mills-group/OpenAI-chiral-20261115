import YM.SU5.Interaction.Source.Route
import YM.SU5.Interaction.Source.Stride
import YM.SU5.Interaction.Source.Reduction

/- # Local allocation of descent of the obstruction tensor

 The matrices still use the actual Kernel pieces at both ends. Flux construction works without
 even-period or block-tiling condition. Implement XIII on all axes via Sweep orientation pooling
 later (not commutativity of tie decisions). Units! $r$ is number of MATTER SITES per pose-step t_s.
 Pay the same operation at every matter root in a tile.
 -/
set_option autoImplicit false
set_option synthInstance.maxSize 25000
noncomputable section
namespace YM.CF.StressExchange
open Tulip
open Function Filter Metric NormedSpace Lattice Finset Fock Lat Spire Scroll Drapes Rush Pastry Thera Proa Hest Scree Reed Dial
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
variable {M:Type*}[AddCommGroup M]
abbrev arcOrder : List Axis := List.finRange 4
def north (r:ℕ)(a:Axis): List Axis:=arcOrder.erase a -- unused r?
variable {N:Side}
def packlet (r:ℕ)(J:LinksV N M) (a:Axis) : Site N→M := cubelet r (north r a) (StressExchange.grain (step a) fun x=>J (x,a))
lemma blockRecv (r:ℕ)(J:LinksV N M)(x:Site N): cubelet r arcOrder (desc J) x=∑ i:Axis,(packlet r J i (x+r • step i) - packlet r J i (x-r • step i)):=by
 let L:(Site N→M) →+ (Site N→M):= {toFun:=cubelet r arcOrder, map_zero':=cubelet_zero ..,map_add':=fun _ _=>cubelet_add ..}
 let Q: Axis→Site N→M:=fun i x=>J (x,i)-J (x-step i,i); change L (desc J) x=_
 have he:desc J=∑ i:Axis,Q i:=by ext; rw [desc, Finset.sum_apply]
 rw [he,map_sum,Finset.sum_apply]; apply sum_congr rfl; intro i _; change cubelet _ _ (Q i) x=_; have hp:(i::north r i).Perm arcOrder:= (List.perm_cons_erase (l:=arcOrder) (by simp [arcOrder,Axis])).symm -- tune
 let G:=StressExchange.grain (step i) (fun x=>J (x,i))
 rw [←cubelet_perm _ hp, cookie, show rake (step i) (Q i) r=(fun x=>G (x+r • step i)-G (x-r • step i)) from (funext (fun x=>stride _ _ _ _)), cubelet_jump]; rfl
local notation "O"=> Op (Single N)
def inhabit (x:Site N):(Finset (Single N)) := univ.filter (fun i:Single N=> i.1.1=x)
def houseW (x:Site N): O := cutM (inhabit x)
lemma all_house : (∑ x:Site N,houseW x)=1:=by
 ext i j; rw [Matrix.sum_apply]; by_cases h:i=j; swap; · simp [houseW,cutM,h,inhabit]
 subst j; simp [houseW,cutM,inhabit]
variable (S C: Op (Single N))
def dOp (S C:Op (Single N))(x:Site N):O := inhibit S C (houseW x)
def duoHouse (S C:Op (Single N))(x y:Site N):O:= (2:ℂ)⁻¹ • (dOp S C x * houseW y+ houseW y*dOp S C x)
-- asymmetry.Peer. subtract same with indexes swapped in descent. site coloring rank local.
abbrev preserveMap (S:Op (Single N)) : O →+ O where
 toFun:=preserve S
 map_zero':=by simp [preserve]
 map_add' _ _:=by simp only [preserve,mul_add,add_mul]; abel
noncomputable def inhibitMap (S C:Op (Single N)) : O →+ O where
 toFun:=inhibit S C
 map_zero':=by simp [inhibit,preserve]
 map_add' _ _:=by simp only [inhibit,preserve,mul_add,add_mul]; abel
variable {S C} (p:IsStarProjection S)(h:TagG S C)
include p h
lemma dOp_zero : (∑ x:Site N,dOp S C x)=0:=by
 change (∑ x:Site N,inhibitMap S C (houseW x))=_; rw [←map_sum,all_house]; change inhibit _ _ _=_; unfold inhibit preserve; simp only [mul_one,p.isIdempotentElem.eq,p.one_sub.isIdempotentElem.eq,add_sub_cancel]; rw [mul_eq_one_comm.mp h.mud,sub_self] -- simp tune
abbrev edgeV (S C:Op (Single N)):LinksV N O:= micropath (duoHouse S C)
lemma posts (x:Site N): desc (edgeV S C) x= dOp S C x:=by
 unfold edgeV; rw [routes]; simp only [duoHouse,sum_sub_distrib,←Finset.smul_sum,sum_add_distrib,←mul_sum,←sum_mul,all_house,dOp_zero p h,mul_one,one_mul,zero_mul,mul_zero,add_zero,smul_zero,sub_zero]
 rw [←two_smul ℂ (dOp S C x),inv_smul_smul₀ (by norm_num:(2:ℂ)≠0)]
def roomW (x:Site N)(r:ℕ):O:=cubelet r arcOrder houseW x
abbrev toll (r:ℕ)(S C:Op (Single N)): Axis→Site N→Op (Single N) := packlet r (edgeV S C)
lemma Eq126 (r:ℕ)(x:Site N): inhibit S C (roomW x r)=∑ i:Axis,(toll r S C i (x+r • step i)-toll r S C i (x-r • step i)):=by
 unfold roomW; change inhibitMap S C _=∑ i:Axis,(packlet r (edgeV S C) i (x+r • step i)-packlet r (edgeV S C) i (x-r • step i)); rw [←blockRecv r (edgeV S C) x, show desc (edgeV S C)= dOp S C from funext (posts p h)]
 exact congrFun (cubelet_natural (inhibitMap S C) houseW r arcOrder) x
omit p h
lemma rooms_pay (x:Site N)(r:ℕ): Commute (tickA N) (roomW x r):=by
 unfold roomW; have hz x: Commute (tickA N) (houseW x):= by rw [touchP]; unfold houseW Commute SemiconjBy cutM; rw [Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]; congr 1; ext i; exact mul_comm ..
 -- induction
 generalize arcOrder=L; induction L generalizing x with
 | nil=> exact hz _
 | cons a l p=>
   rw [cubelet_cons];
   suffices t:∀ k:ℕ,Commute (tickA N) (StressExchange.rake (step a) (cubelet r l houseW) k x) from t _
   intro k; induction k with| zero=> rw [rake]; exact Commute.zero_right _| succ i h=> rw [rake]; exact ((((h.add_right (p _)).add_right (p _)).add_right (p _)).add_right (p _))
end YM.CF.StressExchange
