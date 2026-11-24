import YM.SU5.Relativistic.Slicer
import YM.CF.Fock.Sphere
/-! # incoming oscillator masks. Choose ANY frame; concatenate disjointly supported.
relative to occupancy. -/
set_option autoImplicit false
set_option maxHeartbeats 520000
noncomputable section
namespace YM.CF.Papyrus.Franc
open Function Filter NormedSpace Fock Thera Finset
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators
attribute [local instance] opCStarAlgebra
structure Pea (I:Type*)[LinearOrder I][Fintype I] where
  fill : Op I
  pour : Op I
  home : IsStarProjection fill
  water : IsStarProjection pour
  leg : fill*pour=0
namespace Pea
variable {I:Type*}[LinearOrder I][Fintype I] (A B:Pea I)
local notation "F"=> A.fill
local notation "D"=> A.pour
lemma lic : D*F=0:=by simpa only [star_mul,A.home.isSelfAdjoint.star_eq,A.water.isSelfAdjoint.star_eq,star_zero] using (congrArg star A.leg)
def robe := F+D
lemma robe_p : IsStarProjection A.robe:=by
 constructor; unfold IsIdempotentElem robe; rw [add_mul,mul_add,mul_add,A.home.isIdempotentElem.eq,A.water.isIdempotentElem.eq,A.leg,A.lic]; simp
 exact A.home.isSelfAdjoint.add A.water.isSelfAdjoint
lemma flsp : F*A.robe=F:=by rw [robe,mul_add,A.home.isIdempotentElem.eq,A.leg,add_zero]
lemma spfl : A.robe*F=F:=by rw [robe,add_mul,A.home.isIdempotentElem.eq,A.lic,add_zero]
lemma posp : D*A.robe=D:=by rw [robe,mul_add,A.water.isIdempotentElem.eq,A.lic,zero_add]
lemma sppo : A.robe*D=D:=by rw [robe,add_mul,A.water.isIdempotentElem.eq,A.leg,zero_add]
variable {A B}
structure Zones(A B:Pea I):Prop where
  fares : A.robe*B.robe=0
namespace Zones
variable (p:Zones A B)
include p
lemma partner :Zones B A:=⟨by
  simpa only [star_mul,A.robe_p.isSelfAdjoint.star_eq,B.robe_p.isSelfAdjoint.star_eq,star_zero] using congrArg star p.fares⟩
private lemma harmonic {x y:Op I}(h:x*A.robe=x)(g:B.robe*y=y) : x*y=0:=by nth_rw 1 [←h,←g]; simp only [mul_assoc]; rw [←mul_assoc A.robe,p.fares,zero_mul,mul_zero]
lemma fl : F*B.fill=0:=p.harmonic A.flsp B.spfl
lemma fp : F*B.pour=0:=p.harmonic A.flsp B.sppo
lemma pf : D*B.fill=0:=p.harmonic A.posp B.spfl
lemma po : D*B.pour=0:=p.harmonic A.posp B.sppo
def fuse : Pea I :=⟨F+B.fill,D+B.pour,⟨by unfold IsIdempotentElem; rw [add_mul,mul_add,mul_add,A.home.isIdempotentElem.eq,B.home.isIdempotentElem.eq,p.fl,p.partner.fl,add_zero,zero_add], A.home.isSelfAdjoint.add B.home.isSelfAdjoint⟩, ⟨by unfold IsIdempotentElem; rw [add_mul,mul_add,mul_add,A.water.isIdempotentElem.eq,B.water.isIdempotentElem.eq,p.po,p.partner.po,add_zero,zero_add],A.water.isSelfAdjoint.add B.water.isSelfAdjoint⟩, by rw [add_mul,mul_add,mul_add,A.leg,B.leg,p.partner.fp,p.fp]; simp⟩
lemma fuse_robe:p.fuse.robe=A.robe+B.robe:=by unfold robe fuse; dsimp; abel
end Zones
variable (A)
def Φ (a b:ℝ):=1+a • F+b • D
lemma tale(a b:ℝ): IsSelfAdjoint (A.Φ a b):=((show IsSelfAdjoint (1:Op I) from star_one _).add (show IsSelfAdjoint _ from (by unfold IsSelfAdjoint; rw [star_smul,star_trivial,A.home.isSelfAdjoint]))).add (show IsSelfAdjoint _ from (by unfold IsSelfAdjoint; rw [star_smul, star_trivial,A.water.isSelfAdjoint]))
local notation "x⚬" => (1/(2:ℝ))
lemma philosophy(k b z d:ℝ) : A.Φ k b * A.Φ z d=A.Φ (k+z+k*z) (b+d+b*d):=by
 unfold Φ; simp only [add_mul,mul_add,one_mul,mul_one,Algebra.smul_mul_assoc,Algebra.mul_smul_comm, A.leg,A.lic,A.home.isIdempotentElem.eq,A.water.isIdempotentElem.eq,add_smul,smul_smul,smul_zero]; module
/-- sell represents inverse occupancy-penalty. -/
def mint : Shaft I:=⟨A.Φ (-x⚬) 1,A.Φ 1 (-x⚬),by rw [A.philosophy]; norm_num [Φ]⟩
lemma minted {B C:Pea I} (p:Zones B C): p.fuse.mint=B.mint.foldC C.mint:=by
 have he(a b:ℝ): p.fuse.Φ a b=B.Φ a b*C.Φ a b:=by unfold Φ Zones.fuse; simp only [add_mul,mul_add, Algebra.mul_smul_comm,Algebra.smul_mul_assoc,p.fl,p.po,p.fp,p.pf,smul_add, mul_one,one_mul,smul_zero]; abel
 have hp(a b:ℝ): p.fuse.Φ a b=C.Φ a b*B.Φ a b:=by nth_rw 1 [← (p.fuse.tale a b).star_eq]; rw [he,star_mul,(C.tale a b).star_eq,(B.tale a b).star_eq]
 unfold mint Shaft.foldC; congr 1; exact he _ _; exact hp _ _
variable (e f:ℝ)
-- number rank as natural. tick
abbrev nodes :ℕ:= ⌊(Matrix.trace F).re⌋₊
lemma trace_e(U: UNI I)(s:Finset I)(h:F=twist U (cutM s)) : Matrix.trace F=(s.card:ℂ):=by
 rw [h,trace_twist, cutM, Matrix.trace_diagonal,sum_ite,sum_const_zero]; simp -- tune
lemma nodes_spec (U : UNI I)(s:Finset I)(h:F=twist U (cutM s)) : A.nodes=s.card:=by unfold nodes; rw [A.trace_e _ _ h]; simp
lemma nodF {X Y:Pea I} (p:Zones X Y) : p.fuse.nodes=X.nodes+Y.nodes:=by
 obtain ⟨U,S,v⟩:=spot_projection _ X.home; obtain ⟨V,T,d⟩:=spot_projection _ Y.home; rw [X.nodes_spec _ _ v,Y.nodes_spec _ _ d]
 unfold nodes Zones.fuse; simp only [Matrix.trace_add]; rw [X.trace_e _ _ v,Y.trace_e _ _ d]; push_cast; exact_mod_cast Nat.floor_natCast (R:=ℝ) (S.card+T.card) -- tune
lemma laid : ∃ (U:UNI I) (F' D':Finset I), F=twist U (cutM F') ∧ D=twist U (cutM D')∧ Disjoint F' D':=by
 let S:=F-D; obtain ⟨U,d,g⟩:= spectral_exists S (A.home.isSelfAdjoint.sub A.water.isSelfAdjoint); have hs:S*S=A.robe:=by unfold S; rw [mul_sub,sub_mul, sub_mul,A.home.isIdempotentElem.eq,A.water.isIdempotentElem.eq,A.lic,A.leg]; unfold robe; abel
 have ht:S*S*S=S:=by rw [hs]; unfold S; rw [mul_sub,A.spfl,A.sppo]
 rw [g,spectral_mul, spectral_mul] at ht
 have he:d*d*d=d:=le_antisymm ((spectral_le _ _ _).mp ht.le) ((spectral_le _ _ _).mp ht.ge)
 have hf(i:I): d i=1∨d i=-1 ∨d i=0:=by
    have h0:=congrFun he i; simp only [Pi.mul_apply] at h0; by_cases h:d i=0; simp [h]
    have ht:d i*d i=1:= mul_right_cancel₀ h (by rw [one_mul]; exact h0); rcases eq_or_ne (d i) (1:ℝ) with u|u; exact Or.inl u; obtain v|v:= lt_or_gt_of_ne u <;> (first|exact Or.inr (Or.inl (by nlinarith))|exfalso; nlinarith)
 let F':=univ.filter fun i=>d i=1; let D':=univ.filter fun i=>d i=-1; refine ⟨U,F',D',?_,?_,disjoint_left.mpr (by intro i x y; linarith only [(mem_filter.mp x).2,(mem_filter.mp y).2])⟩
 · rw [show F=(1/2:ℝ) • (S*S+S) from (?_),g,spectral_mul,spectral_add,spectral_smul,spectral,cutM]; swap; · rw [hs]; unfold S robe; change _ = _ • (F+D+(F-D)); module
   apply congrArg; ext i j; by_cases h:i=j; subst j; rcases hf i with t|t|t <;> norm_num [t,F']; simp [h]
 rw [show D=(1/2:ℝ) • (S*S-S) from (?_),g,spectral_mul,spectral_sub,spectral_smul,spectral,cutM]; swap; · rw [hs]; unfold S robe; module
 apply congrArg; ext i j; by_cases h:i=j; subst j; rcases hf i with t|t|t <;> norm_num [t,D']; simp [h]
lemma phile (U:UNI I)(s t:Finset I)(x:F=twist U (cutM s))(y:D=twist U (cutM t))(h:Disjoint s t) (a b:ℝ): A.Φ a b=twist U (Matrix.diagonal fun i=> if i∈s then ((1+a:ℝ):ℂ) else if i∈t then ((1+b:ℝ):ℂ) else 1):=by
 rw [Φ,x,y,←map_smul,←map_smul,←map_one (twist U),←map_add,←map_add]
 apply congrArg; ext i j; by_cases k:i=j
 · subst j; by_cases p:i∈s; have he:i∉t:=disjoint_left.mp h p; simp [cutM,p,he,Complex.real_smul]; by_cases v:i∈t <;> simp [cutM,p,v,Complex.real_smul]
 simp [cutM,k]
end Pea
end YM.CF.Papyrus.Franc
