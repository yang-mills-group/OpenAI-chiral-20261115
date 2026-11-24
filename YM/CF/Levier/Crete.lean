import YM.CF.Levier.Flute
set_option maxHeartbeats 350000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Levier
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Spire Nacre
-- analytic profiles under affine pullback incl sail seams
variable {N:Side}(b:Bool)(a:Shape)
open Urn
variable {P: Side}(G:Ratio N P)(h: Odd G.count.val)(e:ℝ)(k:Sweep N)(q:Shape)
local notation "κ"=> (Iota G)
-- dual locally evaluate on conjugated ambient
variable {C:Seal (Site (More P))→Toll (Iota G)}{d p r:ℝ}{v t:Bool}
open Proa Hake Pastry
variable (W:Meter Grave G e)(x:cro G e)
lemma bandX(i: Grave): toSpin G k (feeX G i)=feeX G (flingX i (accent k)):=by
 unfold feeX flingX; simp only [carL,beltG, ne_eq]; simp only [Bool.xor_left_inj]; -- tune
 split; unfold toSpin steer; rw [singT,win_c,twist_scalar,win_i,map_one]; congr 1; unfold cSignX; split; simp; rfl
 unfold toSpin steer; rw [singT,win_z,map_zero]
include h
lemma gold_W(w:∀ i k S x,toSpin G k (W i S x)= W (flingX i (accent k)) (toRoar G k⁻¹ S) (toWish G e k x))(S:Seal (Site (More P)))(i:Grave): toSpin G k (heal G e W i S x)= heal G e W (flingX i (accent k)) (toRoar G k⁻¹ S) (toWish G e k x):=by
 let f:=toSpin G k; let T:=accent k; have hp : carL (flingX i T)=beltG (flingX i T) ↔ carL i=beltG i:=by unfold flingX carL beltG; simp only; simp
 unfold heal; simp only [show flingX i (accent k)=flingX i T from rfl, ne_eq,hp,show (flingX i T).1=i.1 from rfl,show (flingX i T).2.1=i.2.1 from rfl]; split
 swap; exact w ..
 have he(A B:Op κ): f ((2:ℂ)⁻¹ • (A-star B))=(2:ℂ)⁻¹ • (f A-star (f B)):=by unfold f toSpin steer; simp only [singT,win_c,win_s,win_l,twist_scalar,map_sub,map_star]; congr 1; unfold cSignX; split; simp; rfl
 rw [show toSpin _ _ (_ • (_-_))=_ from he _ _, show giveX (flingX i T) = flingX (giveX i) T from rfl]; unfold f; simp_rw [w,wish_f]; rfl
abbrev KinG (V:Finset (Seal (Site (More P)))):Oak (Iota G):= oakN G (fun i=> (∑ S∈V,heal G e W i S x) + feeX G i)
lemma kins (V:Finset (Seal (Site (More P))))(t:chillF G e x=x): KindX (Urn.soar (KinG G e W x V)):=by
 apply wingV; intro i k; rw [star_add, star_sum]; let p:=pays_p G i k; rw [← p]; rw [add_add_add_comm,←sum_add_distrib]; simp_rw [show ∀ s,_+_= (0:Op κ) from (fun s=>bite_p G e W x s i k t), sum_const_zero,zero_add]
lemma playG (V:Finset (Seal (Site (More P)))) (w:∀ i k S x,toSpin G k (W i S x)= W (flingX i (accent k)) (toRoar G k⁻¹ S) (toWish G e k x)): playX k.charge (accent k) (pflux (castX k) G (spinU k.charge k.s) (xtra k.charge)) (KinG G e W x V) (KinG G e W (toWish G e k x) (V.image (toRoar G k⁻¹))):=by
 intro g z t u p; let i:Grave:=(g,z,t,u); change (∑ S∈V.image (toRoar G k⁻¹),heal G e W (flingX i (accent k)) S (toWish G e k x))+feeX G (flingX i (accent k)) = toSpin G k ((∑ S∈V,heal G e W i S x)+feeX G i); have hl(A:Op κ): toSpin G k (A+feeX G i)= toSpin G k A + toSpin G k (feeX G i):=by unfold toSpin steer; rw [singT,win_a,map_add]; rfl
 rw [hl,toSpin_sum _ h,bandX, sum_image]; swap; · exact fun a _ b _ p=> (weaveS G k⁻¹).injective p
 simp_rw [gold_W G h e k W x w]
end YM.CF.Levier
