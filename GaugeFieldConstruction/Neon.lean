import GaugeFieldConstruction.Planet

/-!
# Compact rotation algebra, coordinate version. No classification assumed.
-/
set_option autoImplicit false
noncomputable section
namespace YM.GaugeFieldConstruction.Apit
open Stage Cauchy Matrix -- adjust
open scoped Topology Matrix BigOperators

abbrev G:= Ortho.Skew
abbrev Endr (X : Type*) [AddCommGroup X] [Module ℝ X]:= Module.End ℝ X
lemma anti (x y:G): tick x y= -tick y x:=Subtype.ext (by simp [tick])
def piston (x : G): Endr G where
  toFun:=tick x
  map_add' a b:= Subtype.ext (by simp [tick, mul_add, add_mul]; abel)
  map_smul' a b:= Subtype.ext (by simp [tick,smul_sub])
def bracket : G→ₗ[ℝ] Endr G where
  toFun:=piston
  map_add' x y:= LinearMap.ext fun i=> Subtype.ext (by change (x.val+y.val)*_ - _*(x.val+y.val)= (_ + _); rw [mul_add,add_mul]; change _= (_-_)+(_-_); abel)
  map_smul' a x := LinearMap.ext fun i=>Subtype.ext (by change (a • x.val)*i.val-i.val*(a • x.val)=a • (_ - _); rw [Matrix.smul_mul,Matrix.mul_smul,smul_sub]) -- name
lemma bracket_tick (x y): bracket x y=tick x y:=rfl
lemma flips (x y:G): bracket x y= -bracket y x:=anti x y
lemma jac (x y z:G) : bracket x (bracket y z)+bracket y (bracket z x)+bracket z (bracket x y)=0:= by
  simp_rw [bracket_tick]; apply Subtype.ext; simp only [tick, Submodule.coe_add,Submodule.coe_zero]; noncomm_ring

lemma odd (a:G) (i j:Axis): a.val i j= -a.val j i:= congr_fun (congr_fun a.property j) i
lemma same (a:G) (i:Axis): a.val i i=0 := by linarith [odd a i i]

def Jx (i:S3):G:= Ortho.plane (cw i).castSucc (ccw i).castSucc
def Mx (i:S3):G:= Ortho.plane i.castSucc timeAxis
def phx (i:S3) : G→ₗ[ℝ] ℝ where
  toFun x:=x.val (cw i).castSucc (ccw i).castSucc
  map_add' _ _:=rfl; map_smul' _ _:=rfl
def pax (i:S3) : G→ₗ[ℝ] ℝ where
  toFun x:=x.val i.castSucc timeAxis
  map_add' _ _:=rfl; map_smul' _ _:=rfl
lemma cwc (i:S3) : cw (ccw i)=i:=by fin_cases i <;> decide
lemma ccw_c (i:S3) : ccw (cw i)=i:=by fin_cases i <;> decide
lemma cw_c (i:S3):cw (cw i)=ccw i:=by fin_cases i <;> decide
lemma pre_1 (i:S3): i≠cw i:=by fin_cases i<;> decide
lemma pre_2 (i:S3): i≠ccw i:=by fin_cases i<;> decide
lemma is_p (i j:S3) (p:i≠j): i=cw j ∨ i=ccw j:=by fin_cases i <;> fin_cases j <;> first|decide|exact (p rfl).elim
lemma test (a b:G) (h:∀ i, phx i a=phx i b) (p:∀ i,pax i a=pax i b):a=b:= by
  apply Subtype.ext; apply Matrix.ext; intro i j
  have he (i:S3): a.val i.castSucc (cw i).castSucc=b.val i.castSucc (cw i).castSucc := by
    have v:= h (ccw i); change a.val _ _ = b.val _ _ at v
    rw [show cw (ccw i)=i from cwc _,show ccw (ccw i)=cw i by fin_cases i<;> decide] at v; exact v
  refine Fin.lastCases ?_ ?_ i <;> refine Fin.lastCases ?_ ?_ j -- j dep? i split gives ∀ i' bound
  · rw [same,same]
  · intro j; rw [odd,odd b]; exact congr_arg Neg.neg (p j) -- adjust
  · intro i; exact p i
  intro j i; by_cases v:i=j
  · rw [v,same,same]
  rcases is_p j i (Ne.symm v) with s|s
  · rw [s]; exact he _
  have u:cw j=i:=by rw [s,cwc]
  rw [odd a,odd b]; exact congr_arg Neg.neg (by rw [← u]; exact he j)

-- basis bracket via elementary multiplication. on rotations P.
lemma mxP (a b c d : Axis):
    tick (Ortho.plane a b) (Ortho.plane c d)=
      (if b=c then Ortho.plane a d else 0) + (if d=a then Ortho.plane b c else 0) - (if a=c then Ortho.plane b d else 0) - (if b=d then Ortho.plane a c else 0):=by
  have e (x y z w:Axis): single x y (1:ℝ) * single z w 1= if y=z then single x w 1 else 0:= by split_ifs with t; subst z; rw [Matrix.single_mul_single_same,mul_one]; exact Matrix.single_mul_single_of_ne (h:=t) .. -- indent next
  apply Subtype.ext; simp only [tick, Ortho.plane, Submodule.coe_sub, Submodule.coe_add]; simp only [apply_ite Subtype.val]; simp only [Submodule.coe_zero,sub_mul,mul_sub, e] -- maybe ite_single
  simp only [show (c=b)=(b=c) from propext eq_comm,show (a=d)=(d=a) from propext eq_comm, show (c=a)=(a=c) from propext eq_comm,show (d=b)=(b=d) from propext eq_comm]; split_ifs <;> abel

lemma n23 (i:S3): cw i≠ ccw i:= by fin_cases i<;> decide
lemma lpair (i:S3): bracket (Jx i) (Jx (cw i))= - Jx (ccw i) :=by
  rw [bracket_tick,Jx,Jx, mxP, Jx, cw_c,ccw_c,cwc, show ccw (ccw i)=cw i by fin_cases i<;> decide]; simp only [Fin.castSucc_inj,Ne.symm (pre_1 i),pre_1,pre_2,n23,Ne.symm (pre_2 i), ite_false,ite_true,add_zero,sub_zero]
  apply Subtype.ext; simp [Ortho.plane]
lemma lpart (i:S3): bracket (Jx i) (Mx (cw i)) = - Mx (ccw i):=by rw [bracket_tick,Jx,Mx,mxP]; simp [Mx,n23,Ne.symm (n23 i), Ne.symm (Fin.castSucc_ne_last _)]
lemma mpart (i:S3): bracket (Mx i) (Jx (cw i)) = - Mx (ccw i):=by rw [bracket_tick,Jx,Mx,mxP,cw_c,ccw_c]; simp [Mx,pre_1,pre_2,Ne.symm (Fin.castSucc_ne_last _)]; apply Subtype.ext; simp [Ortho.plane]
lemma mpair (i:S3): bracket (Mx i) (Mx (cw i))= -Jx (ccw i):=by rw [bracket_tick,Mx,Mx,mxP]; simp [Jx,pre_1,cwc, Ne.symm (Fin.castSucc_ne_last _), show ccw (ccw i)=cw i by fin_cases i<;> decide]
lemma same_i (i:S3) : bracket (Mx i) (Jx i)=0:=by rw [bracket_tick,Jx,Mx,mxP]; simp [pre_1 i,pre_2 i, Ne.symm (pre_2 i),Ne.symm (Fin.castSucc_ne_last _)]
lemma self (x:G): bracket x x=0:=by rw [bracket_tick]; apply Subtype.ext; simp [tick]

def sig (p : Bool):ℝ := if p then 1 else -1
def mot (p : Bool) (i:S3):G:= (-1/2:ℝ) • (Jx i + sig p • Mx i)
lemma sym_sr (p i) : bracket (mot p i) (mot p (cw i))=mot p (ccw i):=by
  simp only [mot,map_smul,map_add,LinearMap.smul_apply,LinearMap.add_apply]; rw [lpair,mpair,lpart,mpart]; cases p
  all_goals simp [sig,smul_sub,smul_add]; module -- tactic module
lemma away' (p i) : bracket (mot p i) (mot (!p) (cw i))=0:= by
  simp only [mot,map_smul,map_add,LinearMap.smul_apply,LinearMap.add_apply]; rw [lpair,mpair,lpart,mpart]; cases p <;> simp [sig,smul_sub,smul_add] <;> module
lemma away_pair (p : Bool) (i j : S3) : bracket (mot p i) (mot (!p) j)=0 := by
  by_cases h:i=j
  · subst j; simp only [mot,map_smul,map_add,LinearMap.smul_apply,LinearMap.add_apply,self,same_i]; rw [flips (Jx i), same_i]; simp
  rcases is_p j i (Ne.symm h) with q|q
  · rw [q]; exact away' ..
  rw [flips]; suffices H :bracket (mot (!p) j) (mot p i)=0 by rw [H,neg_zero];
  have he:= away' (!p) j; rw [Bool.not_not,show cw j=i by rw [q,cwc]] at he; exact he
abbrev Tape := Bool × S3
def wall (w : Tape):= mot w.1 w.2
def point (w : Tape): G→ₗ[ℝ]ℝ := -phx w.2-sig w.1 • pax w.2
lemma p_m (b:Bool) (i j:S3):phx j (mot b i)=if i=j then -1/2 else 0:=by
  rw [mot,map_smul,map_add,map_smul]; unfold Jx Mx phx Ortho.plane; simp only [LinearMap.coe_mk,AddHom.coe_mk,Matrix.sub_apply]; fin_cases i <;> fin_cases j <;> simp (config:={ decide:=true }) [cw,ccw, Matrix.single,Matrix.of_apply]
lemma p_y (b:Bool) (i j:S3): pax j (mot b i)=if i=j then -sig b/2 else 0:=by
  rw [mot,map_smul,map_add,map_smul]; unfold Jx Mx pax Ortho.plane; simp only [LinearMap.coe_mk,AddHom.coe_mk,Matrix.sub_apply]; fin_cases i <;> fin_cases j <;> simp (config:={ decide:=true }) [cw,ccw, Matrix.single,Matrix.of_apply,mul_comm] <;> ring
lemma shines (p q:Tape) : point p (wall q)=if p=q then 1 else 0 := by
  rcases p with ⟨b,i⟩; rcases q with ⟨d,j⟩; simp only [point,wall,LinearMap.neg_apply,LinearMap.smul_apply,LinearMap.sub_apply, p_m,p_y]
  by_cases p:j=i <;> cases b <;> cases d <;> simp [p,sig,Ne.symm] <;> norm_num
lemma stretch (x y:G) (v:∀ i,point i x=point i y): x=y:= by
  apply test
  all_goals
    intro i; have p:=v (true,i); have q:=v (false,i); simp only [point,LinearMap.sub_apply,LinearMap.smul_apply,LinearMap.neg_apply,sig, Bool.false_eq_true,↓reduceIte,neg_one_smul,one_smul] at p q; linarith
lemma repr (x:G) : ∑ i:Tape,point i x • wall i=x:= by
  apply stretch; intro i; rw [map_sum]; simp_rw [map_smul,shines]; simp
end YM.GaugeFieldConstruction.Apit
