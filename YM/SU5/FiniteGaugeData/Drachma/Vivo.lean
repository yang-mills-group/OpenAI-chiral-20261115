import YM.SU5.FiniteGaugeData.Drachma.Garm
import YM.CF.Font.Halt
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef

/-! # harmonic and gauge regulation on every period. -/
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option synthInstance.maxSize 15000
set_option linter.flexible false
noncomputable section
namespace YM.SU5.FiniteGaugeData.Drachma
open Function Finset Matrix Lattice Wilson RG Precision Exterior Tree Laurent Bloch CF.Font Next.Rank.Axial
open scoped Topology BigOperators Matrix Classical
variable {c f:Side} {p:Clip} {a A:ℝ} {P Q:Bed}

abbrev plaid (P:Bed)(f:Side):sp (LT f):=K (P.metric.acts f)
def lasers(f:Side): Matrix Axis (LT f) ℝ:=LinearMap.toMatrix' (LinearMap.pi fun i=> integralLink (0: Site f) (swirl f i))
lemma loan(X:coin (LT f))(i:Axis): (lasers f *ᵥ X) i=integralLink (0:Site f) (swirl f i) X:=by rw [lasers,LinearMap.toMatrix'_mulVec]; rfl
abbrev chips(F:AfterT f) (P:Bed):= plaid P f+prizes (tickets F)+prizes (lasers f)
abbrev chassis(P:Bed)(f:Side):= (chips (axle f) P).det
lemma plaidS (h:(P.metric.acts f).IsSymm): (plaid P f).IsSymm:=by
 unfold Matrix.IsSymm plaid K; simp [h.eq,Matrix.mul_assoc]
lemma chipsS(F:AfterT f)(h:(P.metric.acts f).IsSymm): (chips F P).IsSymm:= ((plaidS h).add (prize_sym _)).add (prize_sym _)
lemma plaid_cost (x y:coin (LT f)):dotProduct x (plaid P f *ᵥ y)=dotProduct (d 1 f*ᵥ x) ((P.metric.acts f)*ᵥ (d 1 f*ᵥ y)):= boost_bill ..
lemma ant_c (t:Site f→ℝ):d 1 f *ᵥ ant t=0:=by rw [ant_d,mulVec_mulVec, Exterior.closed 0,zero_mulVec]
lemma plaid_nil (P:Bed)(x:coin (LT f))(he:d 1 f*ᵥ x=0):plaid P f*ᵥ x=0:=by rw [plaid,K,←mulVec_mulVec,he,mulVec_zero]
lemma lasers_d(v:form 0 f):lasers f *ᵥ (d 0 f*ᵥ v)=0:=by funext i; rw [loan,telescopes,swirl_stop]; exact sub_self _
lemma lasers_ant (t:Site f→ℝ): lasers f*ᵥ ant t=0:=by rw [ant_d,lasers_d]
lemma lasers_read(v:coin Axis): lasers f*ᵥ amble v=(f.val:ℝ) • v:=by
 ext i; rw [loan]; exact mend (0:Site f) v i
lemma amble_d(v:coin Axis): d 1 f*ᵥ amble v=0:=by
 funext i; obtain ⟨i,j⟩:=i; obtain ⟨j,rfl⟩:=plaqEquiv.surjective j; rw [plaq_map,d_plaquettes]; simp [amble]
lemma legal (F:AfterT f)(x:coin (LT f))(h1:d 1 f*ᵥ x=0)(h2:lasers f*ᵥ x=0)(h3:tickets F*ᵥ x=0): x=0:=by
 obtain ⟨v,z,h⟩:=useful (0:Site f) x h1; rw [h,mulVec_add,lasers_d,lasers_read,zero_add] at h2
 have hf:(f.val:ℝ)≠0:=by exact_mod_cast f.property.ne'
 have hv:z=0:=(smul_eq_zero.mp h2).resolve_left hf
 let t:Site f→ℝ:=fun i=>v (i,vac); rw [h] at h3 ⊢ -- tune
 have he:d 0 f*ᵥ v=ant t:=by rw [ant_d]; congr; ext ⟨i,j⟩; rw [vac_only j]
 rw [hv,show amble (n:=f) 0=0 from rfl,add_zero,he] at h3 ⊢; rw [tickets_bill] at h3
 funext i; unfold ant SectorNext.Vacuum.FlatTree.climb; simp only [all_anchor F t h3, sub_self,neg_zero]; rfl
-- Numeric gap on full curls and real PD
section
variable {n:Type}[Fintype n]
lemma flourish(x:coin n):0 ≤ dotProduct x x:=sum_nonneg fun _ _=>mul_self_nonneg _
lemma flourish_p(x:coin n) (he:x≠0): 0<dotProduct x x:=by
 obtain ⟨i,hi⟩:= Function.ne_iff.mp he; exact sum_pos' (fun i _=>mul_self_nonneg _) ⟨i,mem_univ _,mul_self_pos.mpr hi⟩
end
lemma chips_live(F:AfterT f)(h:Floor P p f a A)(hp:0<a): (chips F P).PosDef:=by
 apply Matrix.PosDef.of_dotProduct_mulVec_pos (Matrix.isHermitian_iff_isSymm.mpr (chipsS F h.symmetric.1)); intro x hx; rw [star_trivial, chips,plus_bill,plus_bill,plaid_cost,prize_bill,prize_bill]
 have he:= (h.uniform.1 (d 1 f*ᵥ x)).1; by_cases H:d 1 f*ᵥ x=0
 · rw [H,mulVec_zero,dotProduct_zero,zero_add]; by_cases L:lasers f*ᵥ x=0
   · exact add_pos_of_pos_of_nonneg (flourish_p _ fun hi=> hx (legal F x H L hi)) (flourish _)
   exact add_pos_of_nonneg_of_pos (flourish _) (flourish_p _ L)
 exact add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg (lt_of_lt_of_le (mul_pos hp (flourish_p _ H)) he) (flourish _)) (flourish _)
lemma chassis_p (h:Floor P p f a A)(hp:0<a): 0<chassis P f:= (chips_live (axle f) h hp).det_pos

-- The Booth's Floor may depend on the period and have no positive `a`; get analogous from direct >= clip > 0 anyway.
end YM.SU5.FiniteGaugeData.Drachma
