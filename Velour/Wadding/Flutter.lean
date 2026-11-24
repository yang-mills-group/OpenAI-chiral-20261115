import Velour.Wadding.Lamella
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5000
set_option maxHeartbeats 1250000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common Ballad Cordial
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance Lamour.Bridge.Celeste Designs Twah Prototype
open Lamour.Bridge.Celeste.Morn
open Spine
open CF.Velvet CF.Pannier.Chancel
open QuadClock
open Aria Casting MacroGrid Preparation.Yoke Yoke.Travel
open SatinNucleus Six DoseTravel Set

namespace Spine




open Aria Casting Six OS.Semigroup OS.Semigroup.Balloon
open MacroGrid SatinNucleus SatinJets DoseTravel Set



open YM.Velour
open Boundary Probe

lemma Gleams.uniform {H:Hilbert}{f:ℕ→H.Op}{g:H.Op}(h:Gleams H f g)
   {S:Set H.space}(p:IsCompact S){ε:ℝ}(e:0<ε):
 ∀ᶠ i in atTop, ∀x∈S, dist (f i x) (g x)≤ε:=by
 by_contra q
 obtain ⟨m,t,w⟩:=extraction_of_frequently_atTop ((by
    rw [←not_eventually]
    simpa only [not_not] using q) : ∃ᶠ i:ℕ in atTop, ¬∀x∈S,dist (f i x) (g x)≤ε)
 push Not at w
 choose x a b using w
 obtain ⟨y,hy,j,s,u⟩:=p.isSeqCompact a
 have z:= ((h.glints (t.tendsto_atTop.comp s.tendsto_atTop)).both u).dist ((g.continuous.tendsto _).comp u)
 rw [dist_self] at z
 obtain ⟨i,c⟩:=(z.eventually (gt_mem_nhds e)).exists
 exact not_lt_of_ge (b (j i)).le c

variable (P:Spine)(j:Axis)(x:P.Spectrum0 j)
local notation "ℋ"=> P.ColorHil j x
local notation "𝓗"=> P.ManyF j x
local notation "Σ₀"=> P.physicalEnergy j x
local notation "Σ₁"=> P.seasons j x

local notation "E₀"=> (Σ₀).E
local notation "E₁"=> (Σ₁).E
local notation "ϕ"=> P.enter j x
local notation "ρ"=> P.wealth j x
local notation "W"=> P.cartage j x
local notation "Ξ"=> P.truck j x

variable (d l r : ℝ)
local notation "⊥₀"=> P.tableau j x 0
variable (F : SampleDose)(t:ℕ)

lemma lamina_diff {X Y:(ℋ).Op} {v:𝓗} {s:ℝ}
   (p:∀z∈ tsupport F.val, dist (X (P.streakV j x d r v z)) (Y (P.streakV j x d r v z))≤ s):
 dist (P.lamina j x d l r F t X (ϕ v)) (P.lamina j x d l r F t Y (ϕ v))≤ P.package F t*s:=by
 rw [dist_eq_norm]
 unfold lamina package
 rw [_root_.sum_apply,_root_.sum_apply, ←Finset.sum_sub_distrib,Finset.sum_mul]
 refine (norm_sum_le ..).trans (Finset.sum_le_sum fun k a=>?_ )
 rw [smul_apply,smul_apply,←smul_sub,norm_smul,P.lam_act,P.lam_act,
    ←map_sub,P.truck_norm,veneer,veneer,←map_sub]
 have e:=p _ ((P.usedPose _ _ _).mp a)
 rw [dist_eq_norm] at e
 refine mul_le_mul_of_nonneg_left (le_trans (ContinuousLinearMap.le_opNorm ..)
   ((mul_le_of_le_one_left (norm_nonneg _) ((Σ₀).shrinks _)).trans e)) (norm_nonneg _)



structure Spreads (A:ℕ→(ℋ).Op)(a:(𝓗).Op) :Prop where
 price: ∃B:ℝ,∀ᶠ i in atTop, ‖A i‖≤B
 runs(v:𝓗): Tendsto (fun i=>A i (ϕ v)) atTop (𝓝 (ϕ (a v)))

lemma lamina_changes {X:ℕ→(ℋ).Op}{Y:(ℋ).Op}
 (g:Gleams ℋ X Y)(v:𝓗){m:ℕ→ℕ}(w:Tendsto m atTop atTop):
 Tendsto (fun i=>dist (P.lamina j x d l r F (m i) (X i) (ϕ v))
                      (P.lamina j x d l r F (m i) Y (ϕ v))) atTop (𝓝 0):=by
 apply Metric.tendsto_nhds.mpr
 let c:=F.l1+1
 have hp:0<c:=add_pos_of_nonneg_of_pos (integral_nonneg fun _=>norm_nonneg _) zero_lt_one
 intro ε e
 have a:∀ᶠ i in atTop,P.package F (m i)<c:=
     ((P.package_arrives F).comp w).eventually (gt_mem_nhds (lt_add_one _))
 filter_upwards [Gleams.uniform g (F.budget.image
    (P.streakV_cont j x d r v)) (div_pos e hp), a] with i b s
 rw [Real.dist_0_eq_abs,abs_of_nonneg dist_nonneg]
 refine (P.lamina_diff j x d l r F _ (fun z t=> b _ ⟨z,t,rfl⟩)).trans_lt
    ((mul_lt_mul_of_pos_right s (div_pos e hp)).trans_eq ?_)
 exact mul_div_cancel₀ ε hp.ne'


lemma lamina_spreads {a:P.Spectrum0 3}(J:P.Ellis 3 a)
    {X:ℕ→(P.ColorHil j (P.advocate 3 a j)).Op}{Y:(P.ColorHil j (P.advocate 3 a j)).Op}
    (g:Gleams (P.ColorHil j (P.advocate 3 a j)) X Y)
    {m:ℕ→ℕ}(w:Tendsto m atTop atTop):
 let x:=P.advocate 3 a j
 P.Spreads j x (fun i=>P.lamina j x d l r F (m i) (X i))
   (P.flounce j x d l r (P.tableau j x 0 Y) F):=by
 intro z
 refine ⟨?_, fun v=> ((P.lamina_static j d l r F a J Y v).comp w).congr_dist ?_⟩
 · obtain ⟨B,p⟩:=g.bought
   refine ⟨(F.l1+1)*B,?_⟩
   filter_upwards [p, ((P.package_arrives F).comp w).eventually
      (gt_mem_nhds (lt_add_one _))] with i c b
   have e: P.package F (m i)≤F.l1+1:=(show _ < _ from b).le
   exact (P.lamina_bound ..).trans (mul_le_mul e c (norm_nonneg _)
     (add_nonneg (integral_nonneg fun _=> norm_nonneg _) zero_le_one))
 exact (P.lamina_changes j z d l r F g v w).congr fun i=>dist_comm ..


variable {P j x}
lemma Spreads.prod_runs {I:Type}(L:List I) {A:I→ℕ→(ℋ).Op}{a:I→(𝓗).Op}
 (h:∀i∈L, P.Spreads j x (A i) (a i)) (v:𝓗):
 Tendsto (fun n=>(L.map fun i=> A i n).prod (ϕ v))
  atTop (𝓝 (ϕ ((L.map a).prod v))):=by
 induction L with
 | nil=>exact tendsto_const_nhds
 | cons i L ih=>
   have p:= h i List.mem_cons_self
   obtain ⟨B,g⟩:=p.price
   obtain ⟨m,t⟩:=g.exists
   exact firmly (A i) ((norm_nonneg _).trans t) g (p.runs _)
     (ih fun j e=>h j (List.Mem.tail _ e))

lemma Spreads.agree {A B:ℕ→(ℋ).Op}{a:(𝓗).Op}(h:P.Spreads j x A a)
 (p:A=ᶠ[atTop] B):P.Spreads j x B a:=by
 obtain ⟨c,u⟩:=h.price
 refine ⟨⟨c,u.mp (p.mono fun i b=>b ▸ id)⟩,
    fun v=>(h.runs v).congr' (p.mono fun i b=>by rw [b])⟩

#print axioms lamina_spreads
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection

