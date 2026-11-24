import YM.CF.Buffered.RailsMirror
/-! # The mark chessboard. arbitrary even axis lengths, not powers of two. -/
set_option autoImplicit false
set_option synthInstance.maxSize 22000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
noncomputable section
namespace YM.CF.Buffered.Region.MarkCastle
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Mir.Trip Phase RP MeasureTheory Roost Rails Mil RG WilsonStartup Spark Nova Fock Push.SectorMeasure Ordered Cin Stripe Tile Traversed Stack Bays Saddle Stampu
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder Fin.NatCast Function
attribute [local instance] opCStarAlgebra
variable {δ:Axis→Side} (h: Landing δ)
local notation "N" => Fintype.card (Rail δ)
local notation "K" => FaceM δ
local notation "S" i:max => Traversed.self i δ

section fill
-- local stability for any reflected slice
variable (P:FaceM δ→ Prop) (s:∀ x:FaceM δ,P x→∀ i:Axis,∀ t:Fin (δ i).val,∀ b:Bool,P (base (Traversed.self i δ) t b x))
def singles (x:FaceM δ)(b:Bool): Prop:=∀ i,x i=b -- later
variable (x: FaceM δ) (w:P x)
include h s w
private lemma homogeneous (i:Axis): P (fun r=> x (loc (S i) 0 (tail (S i) r))) :=by
 let n:Side := δ i; let V:= S i; let l:= n.val/2; have hp: Even n.val:= h i; have hc: n.val=l+l:=by obtain ⟨a,h⟩:=hp; unfold l; omega
 have hv:0<n.val:= n.property; let F(v:K)(k:ℕ):=∀ t:Fin n.val,t.val<k→∀ z:Car (away i δ), v (loc V t z)=x (loc V 0 z)
 have he (k:ℕ) (p:0<k)(u:k≤l):∃ v:K, P v ∧ F v k:=by
    induction k,p using Nat.le_induction with
    | base=> exact ⟨x,w,fun t h _=> by rw [show t=0 from Fin.ext (by rw [Fin.val_zero]; omega)]⟩
    | succ k p ih=>
      obtain ⟨v,he,ht⟩:= ih (by omega); let a:Fin n.val:=⟨k,by omega⟩
      refine ⟨_,s _ he i a false,fun i t z=>?_⟩; change base V a false v (loc V i z)=_
      unfold base; rw [lead_loc]; by_cases h:i.val=k
      · have hp:i=a:=Fin.ext h; subst i; rw [if_neg (show ¬half a a=false from by unfold half; rw [sub_self]; simp only [Fin.val_zero]; rw [decide_eq_true (by omega)]; decide)]
        unfold Stampu.pivot; rw [lead_loc,tail_loc]; apply ht; unfold mirrored; rw [sub_self,Fin.val_add_eq_ite,Fin.val_rev, Fin.val_zero]; have he:a.val=k:=rfl
        split_ifs <;> omega
      have hh: i.val<k:=by omega
      rw [if_pos ?_]; · exact ht i hh z
      unfold half; apply decide_eq_false; have he:= Fin.intCast_val_sub_eq_sub_add_ite i a; rw [if_neg (not_le.mpr (show i<a from hh))] at he; have ha:a.val=k:=rfl; change ¬(i-a).val < l; omega
 obtain ⟨v,q,t⟩:= he l (by omega) le_rfl
 have he := s v q i 0 true
 rw [show (fun r=> x (loc V 0 (tail V r)))= base V 0 true v from ?_]; · exact he -- tune mismatch? variable V
 funext r; obtain ⟨⟨j,w⟩,rfl⟩:= V.click.surjective r; unfold base; rw [show V.click (j,w)=loc V j w from rfl,tail_loc, lead_loc]; split_ifs with h; · unfold half at h; simp at h; exact (t j h w).symm
 unfold Stampu.pivot; rw [lead_loc, tail_loc, mirrored,sub_zero,add_zero]; apply (t _ _ w).symm; unfold half at h; simp at h; rw [Fin.val_rev]; have hp:=j.isLt; have heq: n.val=(δ i).val:=rfl; omega

lemma smooth_fill : P (fun _=> x 0) :=by
 let f(s:Finset Axis)(r:Rail δ):= x (fun i=> if i∈s then 0 else r i)
 have he(s':Finset Axis): P (f s'):=by
    induction s' using Finset.induction_on with
    | empty=> rwa [show f ∅=x from ?_] -- tune
              funext r; unfold f; simp
    | insert i t u ih=>
       rw [show f (insert i t)= _ from (show _=(fun r=> f t (loc (S i) 0 (tail (S i) r))) from ?_)] -- tune
       · exact homogeneous h _ s _ ih i -- h
       funext r; unfold f; apply congrArg; funext j; by_cases p:j=i
       · subst j; rw [if_neg u,loc_v, if_pos (mem_insert_self _ _)]; rfl
       simp only [mem_insert, p, false_or]; rw [show loc (S i) 0 (tail (S i) r) j=_ from loc_h (S i) _ _ ⟨j,p⟩]; rfl
 rw [show (fun _=> x (0:Rail δ))=f univ from ?_]; exact he _ -- tune
 funext i; unfold f; simp; rfl
end fill

section maximize
variable {f:FaceM δ→ℝ}
def first : K:= fun x=> decide (x=0)
def weight (f:FaceM δ)(c:Bool→ℝ):= ∏ i,c (f i)
structure Crew (f:FaceM δ→ℝ):Prop where
 nonneg(i):0≤f i
 steps (v)(i:Axis)(k:Fin (δ i).val): f v^2≤f (base (S i) k true v)*f (base (S i) k false v)
namespace Crew
variable (H:Crew f)
include H h
lemma bright : (∀ v:FaceM δ,0 < f v→ 0 < f (fun _=>v 0)) :=by
 intro v u; apply smooth_fill h (fun v=>0<f v) _ v u; intro x g i t b; have hp:= lt_of_lt_of_le (pow_pos g 2) (H.steps x i t); cases b; exact pos_of_mul_pos_right hp (H.nonneg _); exact pos_of_mul_pos_left hp (H.nonneg _)
lemma maximal (v:K) : f v ≤ max (f (fun _=>true)) (f (fun _=>false)):=by
 obtain ⟨i,_,e⟩:= exists_max_image (univ: Finset K) f univ_nonempty
 have hs:∀ j,f j≤f i:=fun j=>e j (mem_univ _)
 suffices p:f i=f (fun _=> i 0) by refine (hs v).trans (p.le.trans ?_); cases z:i 0 <;> simp
 symm; refine smooth_fill h (fun v=> f v=f i) ?_ i rfl; intro v x j t b
 let Y:=base (S j) t; have hp:=H.steps v j t; change f v=f i at x; rw [x] at hp
 have he:(f i)^2 ≤ f (Y true v)* f (Y false v):=hp; have ht:=hs (Y true v); have hy:=hs (Y false v); have hz:=H.nonneg (Y true v); have hx:=H.nonneg (Y false v); cases b <;> change f (Y _ v)=f i <;> nlinarith
omit h
lemma mult {g:FaceM δ→ℝ}(p:Crew g):Crew (f*g):= by
 refine ⟨fun i=> mul_nonneg (H.nonneg i) (p.nonneg i),fun v i t=> ?_⟩; simp only [Pi.mul_apply,mul_pow]; rw [mul_mul_mul_comm]; exact mul_le_mul (H.steps ..) (p.steps ..) (sq_nonneg _) (mul_nonneg (H.nonneg _) (H.nonneg _))
lemma scale (t:ℕ): Crew (fun i=> f i^t):=by
 refine ⟨fun i=> pow_nonneg (H.nonneg _) _,fun v i j=>?_⟩; rw [←pow_mul, mul_comm t, pow_mul, ←mul_pow]; exact pow_le_pow_left₀ (sq_nonneg _) (H.steps ..) _
omit H
lemma weight_v (c:Bool→ℝ)(p:∀ i, 0≤c i) : Crew (fun x:FaceM δ=>weight x c):= by
 refine ⟨fun i=> prod_nonneg (fun _ _=>p _),fun v i t=> le_of_eq ?_⟩
 rw [weight,pow_two,weight,weight]; let e:Equiv.Perm (Rail δ):=⟨pivot (S i) t,pivot (S i) t,pivot_twice (S i) t,pivot_twice (S i) t⟩
 nth_rw 1 [←Equiv.prod_comp e (fun i=> c (v i))]
 rw [←prod_mul_distrib, ←prod_mul_distrib]; apply prod_congr rfl; intro j _; unfold base; cases u:half t (lead (S i) j) <;> simp only [u,Bool.false_eq_true,Bool.true_eq_false,ite_false,ite_true]
 · rfl -- or comm?
 exact mul_comm _ _
-- only need singleton
include h H
lemma single (w: 0 < f (fun _=>false)): f first ^ N ≤ f (fun _=>true) * f (fun _=>false) ^ (N-1) :=by
 by_cases p:f first=0
 · rw [p,zero_pow]; swap; · exact (Fintype.card_pos (α:=Rail δ)).ne'
   exact mul_nonneg (H.nonneg _) (pow_nonneg w.le _)
 let a:= f (fun _=>true); let b:= f (fun _=>false)
 have v:0 < a:=by have he:=bright h H first ((H.nonneg _).lt_of_ne (Ne.symm p)); simpa only [first,decide_true] using he
 let c(i:Bool):= if i then a⁻¹ else b⁻¹; have hc:∀ i,0 ≤ c i:=by intro i; unfold c; split <;> positivity
 let k (i:FaceM δ):= f i^N * weight i c
 have hk:Crew k:= (H.scale N).mult (weight_v c hc) -- tune
 have hx:= maximal h hk first
 have ha(X:ℝ)(v: Bool)(p:f (fun _=> v)= X)(h:0 < X)(u:c v=X⁻¹): k (fun _=> v)=1:=by unfold k weight; simp only [p,u,prod_const,card_univ]; rw [←mul_pow,mul_inv_cancel₀ h.ne',one_pow]
 rw [ha a true rfl v rfl, ha b false rfl w rfl,max_self] at hx
 have hq:weight (first (δ:=δ)) c = (a*b^(N-1))⁻¹ :=by
    rw [weight,← mul_prod_erase univ _ (mem_univ (0:Rail δ)), prod_eq_pow_card (b:=b⁻¹), card_erase_of_mem (mem_univ _),card_univ]; -- tune
    · unfold first c; simp; ring
    rintro x v; change (if first x then _ else _)=_; rw [if_neg (by simp [first, (mem_erase.mp v).1])]
 change _ ≤ a*b^(N-1); unfold k at hx; rw [hq,←div_eq_mul_inv,div_le_one (by positivity)] at hx; exact hx
end Crew
end maximize
end YM.CF.Buffered.Region.MarkCastle
#print axioms YM.CF.Buffered.Region.MarkCastle.Crew.single
