import YM.CF.Hove.Cite
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Hove
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill

variable{c:Side}(o:Site c)
-- projector polynomial moments through wt4
abbrev culm(W:Pal):= baseF false* W* baseF true
def jetsL (X:Op (Single c)): Dome:= (mornC o X,(fun i=>culm (partX o X i)),(fun i=> culm (partY o X i)))
def seedsP(z:Dome):Prop:= culm z.1=z.1∧ (∀ i,culm (z.2.1 i)=z.2.1 i)∧ ∀ i,culm (z.2.2 i)=z.2.2 i
def lendP(z:Dome): Dome:= (z.1,(fun i=>z.2.1 i +(ditF false i)ᴴ*z.1),(fun i=> z.2.2 i + z.1*ditF true i)) -- off-block exact for projected valuation
variable (P:Op (Single c))(b:Bool)(a:Axis)
lemma φ_sq (b:Bool): baseF b * baseF b = baseF b:=by cases b; exact binsSq _; unfold baseF; simp; rw [sub_mul,one_mul,mul_sub,mul_one,binsSq]; abel
lemma φ_a : (baseF b)ᴴ=baseF b:=by
 let M:Male:=⟨1,odd_one⟩
 have he:star (Tap.boot 1 M 0)=Tap.boot 1 M 0:=by unfold Tap.boot; rw [op_star_kron,(Fir.firm_bar 1 M.val M.property (base_subset_realCube zone_pos (by simpa [bout_zero] using bout_h 0 0 (by norm_num)))).2,star_one]
 cases b; swap; · rw [show baseF true = boot 1 M 0 from (boot_o ..).symm]; exact he
 change star (bins Slot)=bins Slot; rw [show bins Slot=(1 - boot 1 M 0) from (by rw [boot_o]; abel),star_sub,he,star_one]
lemma φ_mix : baseF b * ditF b a + ditF b a * baseF b = ditF b a:=by
 let M:Male:=⟨1,odd_one⟩; let F(x):Op Kt:= if b then boot 1 M (bout a x) else 1-boot 1 M (bout a x); let G:= if b then boom a else -boom a
 have ht:HasDerivAt F G 0:=by cases b; exact (barox 1 le_rfl M a).const_sub _; exact barox _ le_rfl M _
 have hh : F 0= baseF b:=by unfold F; rw [bout_zero,Tap.boot_o,baseF,sub_sub_cancel]
 have hx: F =ᶠ[𝓝 0] F*F:=by
    filter_upwards [Ps_b 1 le_rfl M a] with i e; unfold F; cases b; swap; exact e.1.symm; change 1-Tap.boot 1 M (bout a i)=(1-Tap.boot 1 M (bout a i))*(1-Tap.boot 1 M (bout a i)); rw [sub_mul,one_mul,mul_sub,mul_one,e.1]; abel
 have hy: baseF b*G+ G*baseF b=G:=by rw [add_comm, ←hh]; exact ((ht.mul ht).congr_of_eventuallyEq hx).unique ht
 unfold ditF; rw [Matrix.mul_smul, Matrix.smul_mul, ←smul_add,show _ + _= G from hy]
lemma span_P : spanH b o a= spanH b o a*baseF b + rampF b o * ditF b a:=by
 ext x i; let z:=portB x; let v:= ox o x; let y:=baseF b; let d:=ditF b a; simp only [spanH,rampF,Matrix.add_apply, Matrix.mul_apply, Matrix.of_apply]; simp_rw [mul_assoc (ζw o x), ←mul_sum]; rw [←mul_add]; congr 1; change _ = (moonB b a v*y+y*d) z i
 rw [show moonB b a v*y +y*d=moonB b a v from ?_]; unfold moonB; have he: y*y=y:= φ_sq _; change _*y+_= _ • y + d; rw [Matrix.add_mul,Matrix.smul_mul,he,add_assoc _ (d*y), add_comm (d*y),φ_mix]
lemma span_W : rampF b o *baseF b=rampF b o:=by
 ext x i; unfold rampF; rw [Matrix.mul_apply]; simp only [Matrix.of_apply]; simp_rw [mul_assoc (ζw o x),←mul_sum]; rw [←Matrix.mul_apply,φ_sq]
local notation "A_"=> baseF false
local notation "B_"=> baseF true
local notation "V"=> rampF
lemma partV : partX o P a= A_*partX o P a* B_+(ditF false a)ᴴ *mornC o P :=by
 unfold partX mornC; simp only [← Matrix.mul_assoc]; rw [Matrix.mul_assoc _ (V true o),span_W]
 nth_rw 1 [span_P]; simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_mul, φ_a, Matrix.add_mul]
lemma pactV : partY o P a= A_*partY o P a* B_+mornC o P*ditF true a:=by
 unfold partY mornC; have ht:A_*(V false o)ᴴ=(V false o)ᴴ:=by rw [← φ_a false,← Matrix.conjTranspose_mul,span_W]
 simp only [← Matrix.mul_assoc,ht]; nth_rw 1 [span_P]; simp only [Matrix.mul_add, ← Matrix.mul_assoc]
lemma dawn_u : domF o P = lendP (jetsL o P):=Prod.ext rfl (Prod.ext (funext fun i=>partV o P i) (funext fun i=>pactV o P i))
lemma cul_p(z:Pal):culm (culm z)=culm z:=by unfold culm; rw [← Matrix.mul_assoc A_,← Matrix.mul_assoc,φ_sq, Matrix.mul_assoc,φ_sq]
lemma true_P : seedsP (jetsL o P):=by
 refine ⟨?_,fun i=>cul_p _,fun i=>cul_p _⟩; change A_*((V false o)ᴴ * P* V true o)* B_=_; have ht:A_*(V false o)ᴴ=(V false o)ᴴ:=by rw [←φ_a,← Matrix.conjTranspose_mul,span_W]
 simp only [← Matrix.mul_assoc,ht]; rw [Matrix.mul_assoc _ (V true o), span_W]; rfl
end YM.CF.Hove
