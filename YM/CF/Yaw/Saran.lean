import YM.CF.Yaw.Saw
import YM.CF.Yaw.Viv
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Yaw
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Eire Jet Scroll Push.AbsoluteSums.Trees
variable {N P B:Side}(G:Ratio (mid N B) (mid P B))(S:StepData (Domain N B) (Domain P B)) (e:ℝ)(X: Meter TailB G e)(V: Meter Grave G e)
variable (HX:TailB→Support (Domain P B)→Toll (Iota G))(HY:Grave→Support (Domain P B)→Toll (Iota G))
local notation "α'"=> Scion.tinOre (switchG G).symm
local notation "H'"=> Eire.Ride S
local notation "W'"=> LeanV (Single (mid N B))
local notation "τ"=> Urn.Twig (Single (mid P B))
variable {ι:Type*}{n B0 s:ℕ}{a A A' U:ℝ}(k d:ℕ)
section
variable {X E z Q R:ℝ} {t:Side}
local notation "Ḱ"=> Harper (Site t)
variable {U:Support t}{F Y:Track (Harper (Site t)) ℝ}
lemma singleK {α:Type*}[DecidableEq α](x:α)(u:ℝ)(h:0≤u):0≤(Pi.single x u:α→ℝ):=by intro i; rw [Pi.single_apply]; split_ifs; exact h; exact le_rfl
lemma incP (W:Ride S)(B:Raid (LeanV (Single (mid N B))))(z:0≤B):0≤ (Pi.single W B:Track H' (Raid _)):= hug_v _ _ z
lemma Kings_add(h:KeepsP U F B0 a Q)(g:KeepsP U Y B0 a R) : KeepsP U (F+Y) B0 a (Q+R):=by
 refine ⟨add_nonneg h.high g.high,fun i v=>?_,?_⟩
 · by_cases p:F i=0; exact g.roads i (fun l=>v (by simp [p,l])); exact h.roads i p
 rw [map_add]; exact add_le_add h.tall g.tall
lemma Kings_sum {E:ι→ℝ}(S:Finset ι)(K:ι→Track (Harper (Site t)) ℝ)(h:∀ i∈S,KeepsP U (K i) B0 a (E i)): KeepsP U (∑ i∈S,K i) B0 a (∑ i∈ S,E i):=by induction S using Finset.induction_on with| empty=> rw [sum_empty,sum_empty]; exact ⟨le_rfl,fun i h=>False.elim (h rfl),(map_zero _).le⟩| insert i S p ih=> rw [sum_insert p,sum_insert p]; exact Kings_add (h i (mem_insert_self ..)) (ih fun i l=> h i (mem_insert_of_mem l))
lemma Kings_bot(B0:ℕ)(X:Support t)(x:ℝ)(p:0≤x): KeepsP X (Pi.single (⊥:Ḱ) x) B0 a x:=by
 refine ⟨singleK _ _ p,fun i v=> Or.inl (by by_contra h; exact v (Pi.single_eq_of_ne h _)),?_ ⟩; rw [bloom_s,bayB,blank_z,one_mul]
lemma Kings_budget {F:Track (Harper (Site t)) ℝ}(h:KeepsP U F B0 a Q)(u:Q≤z): KeepsP U F B0 a z:={h with tall:=h.tall.trans u}
lemma ray_t(S:Support t)(Q:ℝ)(p:0≤Q)(h:Q≠0 → ¬Disjoint U S): KeepsP U (Pi.single (beamH S) Q) B0 a (Push.AbsoluteSums.Trees.currency B0 a S * Q):=by
 refine ⟨singleK _ _ p,fun i v=>?_,?_⟩
 · rw [Pi.single_apply] at v; split_ifs at v with f; · exact Or.inr (by rw [f,bay_beam]; exact ⟨h v,rfl⟩)
   contradiction
 rw [bloom_s,bay_beam]
end
variable (x:∀ i Y, Suite (badge _) (pinH G e true) (pinH G e false) Y (HX i Y) (X i Y))
variable (u:∀ i Y, Suite (badge _) (pinH G e true) (pinH G e true) Y (HY i Y) (heal G e V i Y)) (q:Raid (LeanV (Single (mid N B))))(h: Turner q)
variable (b:B0>0)(p:k ≤ s*B0)(y:0≤a)(t: a*2*χ s ≤ B0*A)(t':a*2*χ s≤ B0*A')(b':0≤A)(y':0≤A')
include x
lemma xPos (T:Support (Domain P B))(i:τ)(j:W'):0≤ payK G d HX T i j:=mul_nonneg (richP d) ((x _ _).nonn _ _)
lemma X_pos(i:τ):0≤ sign_l G S k d HX i:=sum_nonneg fun T _=> hug_v _ _ (sum_nonneg fun i _=> singleK _ _ (xPos G e X HX d x _ _ _))
omit x
include u
lemma zPos(T:Support (Domain P B))(i j:τ):0≤ payZ G d HY T i j:=mul_nonneg (richP d) ((u _ _).nonn _ _)
lemma Z_pos(i j:τ):0≤ sign_z G S k d HY i j:=add_nonneg (sum_nonneg fun T _=> hug_v _ _ (singleK _ _ (zPos G e V HY d u T i j))) (hug_v _ _ (singleK _ _ (norm_nonneg _)))
omit u
abbrev call(T:Support (Domain P B))(i:τ)(b:Raid (LeanV (Single (mid N B)))):=∑ j:W',b {j}*payK G d HX T i j
local notation "L'"=> Domain P B
local notation "V_"=> Domain N B
include x h b p y t b'
lemma sail_k(i:τ)(D:Support V_)(v:Eire.mint S (twigS i).2∈D) : KeepsP D (rateT q (sign_l G S k d HX i)) B0 a (Real.exp (a*(χ s:ℝ)) * ∑ Y:Support L',Branch.rent A Y* call G HX d Y i q):=by
 unfold sign_l; rw [rateF, Finset.mul_sum]; refine Kings_sum _ _ fun W _=>?_ ; rw [heroV]; let Y:=halo k (hatY S W); let z:=call G HX d W i q
 rw [show joinV q (SureV _ _)= z from ?_]; swap; · unfold SureV; rw [joinVsum]; unfold joinV z call; simp only [Pi.single_apply, mul_ite, mul_zero, sum_ite_eq', mem_univ, if_true]
 have he:0≤z:= sum_nonneg fun _ _=> mul_nonneg (h.fee _) (xPos G e X HX d x ..) -- xPos needs t arguments implicit
 have hj(l:z ≠0): ¬Disjoint D Y ∧ Grove (terr L') W:=by
    obtain ⟨j,p',m⟩:=exists_ne_zero_of_sum_ne_zero l; obtain ⟨f,t,v'⟩:= ((x _ _).expo _ _).triggered (right_ne_zero_of_mul (right_ne_zero_of_mul (show q {j}* (payK G d HX W i j) ≠0 from m))); refine ⟨fun d=>disjoint_left.mp d v ?_,f⟩; rw [melt G]; exact halo_subset k _ (mem_image_of_mem _ t)
 refine Kings_budget (ray_t Y z he (fun w=>(hj w).1)) ?_; change _≤ _*(_*z)
 by_cases f:z=0; · rw [f,mul_zero,mul_zero,mul_zero]
 rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (aidV S.ratio (hj f).2 p b y t b') he
omit x t b'
include u y' t'
lemma pair_k (i j:τ)(D:Support V_)(v: Eire.mint S (twigS i).2∈D): KeepsP D (rateT q (sign_z G S k d HY i j)) B0 a (Real.exp (a*(χ s:ℝ)) * (∑ Y:Support L',Branch.rent A' Y* payZ G d HY Y i j)+ ‖due_z G i j‖):=by
 unfold sign_z; rw [tFit,rateF,Finset.mul_sum]; refine Kings_add (Kings_sum _ _ fun W _=>?_ ) ?_
 · rw [heroV]; let Y:=halo k (hatY S W); let z:= payZ G d HY W i j; have hv :0≤z:= zPos G e V HY d u ..; rw [show joinV q _=q ∅*z from ?_]; swap; · simp [joinV,Pi.single_apply,z,mul_ite]
   have he:0≤q ∅:=h.fee _; have ht: q ∅≤1:=h.red
   have hj(l:z ≠0): ¬Disjoint D Y∧Grove (terr L') W:=by
      obtain ⟨x,h,v'⟩:= ((u _ _).expo _ _).triggered (right_ne_zero_of_mul (show payZ G d HY W i j ≠0 from l)); refine ⟨fun d=>disjoint_left.mp d v ?_,x⟩; rw [melt G]; exact halo_subset k _ (mem_image_of_mem _ h)
   refine Kings_budget (ray_t Y (q ∅*z) (mul_nonneg he hv) (fun f=>(hj (right_ne_zero_of_mul f)).1)) ?_; change _ ≤ _*(Branch.rent A' W*z); by_cases f:z=0; · simp [f]
   rw [←mul_assoc (Real.exp _)]; exact mul_le_mul (aidV S.ratio (hj f).2 p b y t' y') (mul_le_of_le_one_left hv ht) (mul_nonneg he hv) (mul_nonneg (Real.exp_pos _).le (rent_pos _ _).le)
 rw [heroV]; simp only [joinV,Pi.single_apply,mul_ite,mul_zero,sum_ite_eq',mem_univ,if_true]; -- simp may rewrite Pi single too far
 refine Kings_budget (Kings_bot _ _ _ (mul_nonneg (h.fee _) (norm_nonneg _))) (mul_le_of_le_one_left (norm_nonneg _) h.red)
end YM.CF.Yaw
