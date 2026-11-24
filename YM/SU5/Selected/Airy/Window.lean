import YM.SU5.Selected.Airy.Grid
import Mathlib.Analysis.Complex.Tietze
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 380000
noncomputable section
namespace YM.CF.Crest.Airy
open Function Filter Metric NormedSpace Lattice Laurent Bloch Next.Free MeasureTheory
open Ember Jill Fir Shore Real Finset
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder
local notation "I"=>Complex.I
local notation "φ" => 2 * π
local instance : Fact (0<φ):= ⟨piRank⟩
attribute [local instance] opCStarAlgebra
-- Separating patch fixed throughout. Construct normalized G-cell partition exactly. Only needs continuity.
variable (G:Side) (p: 8 ≤ G.val)
def stageR (t:ℝ):ℝ:= max 0 (t-1)* max 0 (2-t)
def stage (w:roundC):= AddCircle.liftIoc (2*π) (-π) stageR w
lemma stage_coe {x:ℝ}(h:x∈ deck) : stage (x:roundC)=stageR x:= AddCircle.liftIoc_coe_apply (by rwa [td_ioc])
lemma stage_c : Continuous stage:= by
 apply AddCircle.liftIoc_continuous; · rw [td_ioc]; have h:= pi_gt_three; unfold stageR; rw [max_eq_left (show -π-1 ≤ 0 by linarith), max_eq_left (show 2-π ≤ 0 by linarith),zero_mul,mul_zero]
 unfold stageR; fun_prop
lemma steps_in {x:ℝ}(p:x∈deck)(t:stage (x:roundC)≠0): x∈ Set.Ioo 1 2:=by
 rw [stage_coe p] at t; contrapose! t; rcases le_or_gt x 1 with h|h
 · unfold stageR; rw [max_eq_left (by linarith),zero_mul]
 unfold stageR; have he : 2≤ x:= le_of_not_gt (fun y=> t ⟨h,y⟩); rw [max_eq_left (show 2-x ≤ 0 by linarith),mul_zero]
lemma lodgeDeck {x:ℝ}(p:x∈ Set.Icc 1 2): x∈deck:= ⟨(by linarith [pi_pos,p.1]),(by linarith [pi_gt_three,p.2])⟩
private lemma in_stage {x:ℝ}(p:x∈ Set.Ioo 1 2):stage (x:roundC) ≠0:= by rw [stage_coe (lodgeDeck (Set.Ioo_subset_Icc_self p)),stageR]; apply mul_ne_zero <;> exact ((lt_max_of_lt_right (by linarith [p.1,p.2]))).ne'
def stackfee (w:roundC):ℝ:= (∑ s∈ range G.val, stage (w+s • tier G)^2)/(G.val:ℝ)
def chart (w:roundC):ℝ:= stage w / Real.sqrt (stackfee G w)
-- tonal seam ride
lemma stack_more (s:ℕ)(w:roundC): stackfee G (w+s • tier G)=stackfee G w:=by
 have h(v:roundC): stackfee G (v+tier G)=stackfee G v:=by
    unfold stackfee; congr 1; let f(n:ℕ):=stage (v+n • tier G)^2
    have hv(j:ℕ): v+tier G+j • tier G=v+(j+1) • tier G := by rw [add_smul,one_smul]; abel
    have hq:f G.val=f 0:=by unfold f; rw [flipRoot,zero_smul]
    have hl:= sum_range_succ f G.val; rw [sum_range_succ'] at hl -- tune
    simp_rw [hv]; exact add_right_cancel (hq ▸ hl) -- binder
 induction s with
 | zero=> simp
 | succ s ih=> rw [add_smul,one_smul,←add_assoc,h,ih]
include p
lemma stack_pos (w:roundC): 0<stackfee G w:=by
 let D:= G.val; let u:=tier G; apply div_pos _ (by exact Lat.nPos G); suffices h:∃ i∈ range G.val, stage (w+i • u) ≠0 by obtain ⟨i,e,v⟩:= h; exact (sq_pos_of_ne_zero v).trans_le (single_le_sum (f:=fun i:ℕ=> stage (w+i • u)^2) (fun i _=> sq_nonneg _) e)
 induction w using QuotientAddGroup.induction_on with | _ x =>
 let q:=φ/(G.val:ℝ); have hq:0<q:= div_pos piRank (Lat.nPos G);
 have gq:q<1:=by unfold q; rw [div_lt_one (Lat.nPos G)]; linarith [show (8:ℝ)≤G.val by exact_mod_cast p, Real.pi_lt_four]
 let y:=toIocMod hq 1 x; let a:ℤ:= -(toIocDiv hq 1 x); have hv : y∈ Set.Ioo 1 2:= ⟨left_lt_toIocMod hq ..,(toIocMod_le_right hq ..).trans_lt (by linarith : (1:ℝ)+q<2)⟩
 let b:= a % (D:ℤ); have ht:b < D:=Int.emod_lt_of_pos _ (by exact_mod_cast G.property); have hx:0 ≤ b:= Int.emod_nonneg _ (by have h:(0:ℤ)< (D:ℤ):=(by exact_mod_cast G.property); exact h.ne') -- tune
 have hw:b.toNat • u=a • u:=by
    rw [←natCast_zsmul,Int.toNat_of_nonneg hx]
    have h:D • u=0:=flipRoot G; conv_rhs => rw [←Int.emod_add_mul_ediv a (D:ℤ)]
    rw [add_smul,mul_comm (D:ℤ),mul_smul,natCast_zsmul,h,smul_zero,add_zero]
 refine ⟨b.toNat, mem_range.mpr (by change b.toNat <D; omega), ?_⟩; rw [hw, show ((x:ℝ): roundC)+a • u=(y:roundC) from ?_]; exact in_stage hv
 unfold u tier; rw [←AddCircle.coe_zsmul,←AddCircle.coe_add]; congr 1; unfold a y; rw [neg_smul, ← sub_eq_add_neg,self_sub_toIocDiv_zsmul hq]
lemma chart_c : Continuous (chart G):=by
 have h:Continuous (stackfee G):=by unfold stackfee; have he:= stage_c; fun_prop
 apply Continuous.div stage_c h.sqrt; intro i; exact (Real.sqrt_pos.mpr (stack_pos G p i)).ne' -- tune
lemma stack_price (w:roundC): ∑ i∈ Finset.range G.val, (chart G (w+i • tier G))^2=(G.val:ℝ):=by
 have hp:0<stackfee G w:= stack_pos G p _; unfold chart; simp_rw [div_pow,stack_more]; rw [←Finset.sum_div,Real.sq_sqrt hp.le]; rw [div_eq_iff hp.ne']; unfold stackfee; field_simp [ne_of_gt (Lat.nPos G)]
omit p
abbrev Torch:= Br (Fin 3)
def road(x:Facet3):Torch:= fun i=> ((x i:ℝ):roundC)
def soap (x:Torch):ℝ:= ∏ i:Fin 3,chart G (x i)
def pier (w:Coast) : Torch:= fun i:Fin 3=> w i.castSucc
def lapse (w:Coast) : roundC := w 3
@[simp] lemma here_p (w:Torch)(t: roundC): pier (Ε w t)=w:=by funext i; unfold pier; simp
@[simp] lemma here_l (w:Torch)(t: roundC): lapse (Ε w t)=t:=by unfold lapse; simp
@[simp] lemma to_whole(w: Coast): Ε (pier w) (lapse w)= w:= Fin.snoc_init_self _
@[fun_prop] lemma pier_c :Continuous pier:=by unfold pier; fun_prop
@[fun_prop] lemma lapse_c : Continuous lapse:=by unfold lapse; fun_prop
lemma cueDeck (w:roundC) : ∃ x∈ deck, w=(x:roundC):=by
 have h:= AddCircle.coe_image_Ioc_eq (p:=2*π) (-π); rw [td_ioc] at h; obtain ⟨x,p,g⟩:=(h.symm ▸ (Set.mem_univ w)) -- tune
 exact ⟨x,p,g.symm⟩
lemma road_race (w:Torch): ∃ x:Facet3,(∀ i,x i∈deck)∧w=road x:=by
 choose x p e using fun i=> cueDeck (w i); exact ⟨x,p,funext e⟩
lemma soap_back {x:Facet3}(p:∀ i,x i∈deck)(h: soap G (road x) ≠0): x∈grounds:= fun i _=> Set.Ioo_subset_Icc_self (steps_in (p i) (fun t=> h (by unfold soap; exact Finset.prod_eq_zero (mem_univ i) (by unfold chart road; rw [t,zero_div]))))
lemma soap_support {w:Torch}(h:soap G w≠0): ∃ x∈grounds,w=road x:=by obtain ⟨x,p,rfl⟩:= road_race w; exact ⟨_,soap_back G p h,rfl⟩
include p
@[fun_prop] lemma soap_c : Continuous (soap G):=by unfold soap; have h:= chart_c G p; fun_prop
omit p
open Topology
lemma road_c : Continuous road:= continuous_pi (fun i=> (AddCircle.continuous_mk' _).comp (continuous_apply i))
lemma road_plant : IsClosedEmbedding (fun k:grounds=> road k.val):=by
 haveI: CompactSpace grounds:= isCompact_iff_compactSpace.mp groundsCompact
 apply Continuous.isClosedEmbedding (road_c.comp continuous_subtype_val); intro x y h; ext1; funext i
 have ht(x:grounds):x.val i ∈ Set.Ioc (-π) (-π+(2*π)):= by rw [td_ioc]; exact lodgeDeck (boundsG x.2 i)
 exact AddCircle.coe_eq_coe_iff_of_mem_Ioc (ht x) (ht y)|>.mp (congrFun h i) -- tune
end YM.CF.Crest.Airy
open YM.CF.Crest.Airy
#print axioms stack_price
#print axioms soap_support
#print axioms road_plant
