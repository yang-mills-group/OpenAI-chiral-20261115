import Merino.Plume.Cloud
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 600000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Merino.Plume
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG Mew Rive Nor Hake MeasureTheory Bake Rue Salt
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Swell

variable {n:Side}
local notation "I"=> Single n
open Window Buffered Buffered.Lifted StressExchange Dial
variable {m:ℕ}


abbrev Quiz (m:ℕ):=Nib m→Nib m→Nib m→Nib m→Bool
def quiz (m:ℕ)(τ:ℝ)(x:LinksC): Quiz m:= fun i j k a=>
 decide (SU.group.chord (dot x i*(dot x j*((dot x k)⁻¹*(dot x a)⁻¹))) < τ)

lemma quizzed {τ:ℝ}{x y:LinksC}(p:quiz m τ x=quiz m τ y)(i:Face (Per (More n))):
    SU.group.chord (faceValue (dark n m x) i)<τ →
    SU.group.chord (faceValue (dark n m y) i)<τ:=by
 have h(a b c d:Nib m): SU.group.chord (dot x a*(dot x b*((dot x c)⁻¹*(dot x d)⁻¹)))<τ→
    SU.group.chord (dot y a*(dot y b*((dot y c)⁻¹*(dot y d)⁻¹)))<τ:=by
   have j:=congrFun (congrFun (congrFun (congrFun p a) b) c) d
   exact fun g=>of_decide_eq_true (j.symm.trans (decide_eq_true g))
 simp only [faceValue,square,travel,mul_one]
 exact h _ _ _ _


lemma lit_dark {τ:ℝ}{x y:LinksC}(p:quiz m τ x=quiz m τ y)
    (B:BudgetPoint)(v:B.threshold=τ)(o:Seat n):
    dark n m x∈pass B o → dark n m y∈pass B o:=by
 subst τ
 intro g i r
 exact quizzed p i (g i r)

/-- Only boundedly many links pay in fare, even without restricting
it. Use pin discrepancy in L² operator norms on Slot. -/
abbrev Echo(m:ℕ):=Nib m→Twig
def echoC(m:ℕ)(x:LinksC):Echo m:=fun i=>brand (dot x i)
lemma echoC_bounded(m:ℕ):TotallyBounded (Set.range (echoC m)):=by
 refine (isCompact_closedBall (0:Echo m) 1).totallyBounded.subset ?_
 rintro _ ⟨x,rfl⟩
 rw [Metric.mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg zero_le_one]
 exact fun _=>brand_norm _ |>.le



def capacity(m:ℕ):ℝ:=(Fintype.card (Pin m):ℝ)
lemma cap_pos(m:ℕ):0≤capacity m:=Nat.cast_nonneg _
lemma milk {x y:LinksC}(T:Sa n)(m:ℕ):
 fare T (profile (dark n m x)) (profile (dark n m y)) ≤ capacity m*dist (echoC m x) (echoC m y):=by
 let j:Pin m→Edge (Seat n):=fun p=>(wrap _ p.1.val,p.2)
 let S:=univ.image j
 let a(V:LinksC):=profile (dark n m V)
 let g(e):ℝ:= ‖a x e-a y e‖
 let L:=dist (echoC m x) (echoC m y)
 have e(i):g i≤L:=by
   simp only [g,pi_norm_le_iff_of_nonneg (show 0≤L from dist_nonneg)]
   have d:=norm_le_pi_norm (echoC m x-echoC m y) (hole m i)
   unfold L;rw [dist_eq_norm]
   rintro (_|_)
   · simp only [Pi.sub_apply,a,profile,dark,comp_apply,Bool.false_eq_true,if_false,
       ←star_sub,norm_star]
     exact d
   exact d



 have away(i)(v:i∉S):g i=0:=by
   have h:lift i.1 ∉ Lattice.box m:=by
     intro h
     apply v
     exact mem_image.mpr ⟨(⟨_,h⟩,i.2),mem_univ _,by simp [j]⟩
   have t:a x i=a y i:=by funext r; simp only [a,profile,dark,comp_apply,hole,dif_neg h,dot]
   unfold g;rw [t,sub_self,norm_zero]
 unfold fare
 calc
   ∑ i∈leaks T,g i = ∑ i∈(leaks T ∩ S),g i :=
      (sum_subset inter_subset_left (by
         intro i h n
         exact away i (fun j=> n (mem_inter.mpr ⟨h,j⟩)))).symm
   _ ≤ ∑ _i∈S,L:=by
      refine (sum_le_sum (s:=leaks T ∩ S) (g:=fun _=>L) (fun _ _=> e _)).trans ?_
      exact sum_le_sum_of_subset_of_nonneg inter_subset_right fun _ _ _=>dist_nonneg
   _ ≤ _:=by
      rw [sum_const,nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (card_image_le.trans (card_univ.le))) dist_nonneg

