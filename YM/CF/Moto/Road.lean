import YM.CF.Moto.Rune
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.Moto
open Function Filter Metric Fir Lattice Laurent Next.Free Bloch Finset Lat Stationary Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Fock Tulip Font Spire Nacre Ember Pec
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix Matrix.Norms.L2Operator Kronecker MatrixOrder Classical
attribute [local instance] opCStarAlgebra
open Tap Hake Urn Yaw Levier Proa Rill
open Hove Haro
variable {n:Side}(o x y:Site n)(a b:Pal)(S T:Matrix (Single n) Kt ℂ)(P:Op (Single n))(k:ℕ)(gT:SU.E)(r:Bool)(i:Axis)
def pub : Op (Single n) →ₗ[ℂ] Dome:=(snapH (rampF false o) (rampF true o)).prod ((LinearMap.pi fun i:Axis=>coneL.comp (snapH (spanH false o i) (rampF true o))).prod (LinearMap.pi fun i:Axis=>coneL.comp (snapH (rampF false o) (spanH true o i))))
lemma pub_eq: jetsL o P=pub o P:=Prod.ext rfl (Prod.ext (funext fun _=>rfl) (funext fun _=>rfl))
abbrev rain_U(x:Site n):= Rush.wind o (Lattice.lift (x-o))
def seed_k (x y:Site n)(a:Pal):Op (Single n):= Matrix.of fun u v=> if x=u.1.1∧y=v.1.1 then a (Hove.portB u) (Hove.portB v) else 0
abbrev bud_k(x y:Site n)(a:Pal):= seed_k x y (rain_U o x • rain_U o y • a)
local notation "L"=> seed_k x y a
lemma star_P (v w:Site n):matPH L v w= if x=v∧y=w then a else 0:=by
 split_ifs with g
 · ext i j; exact if_pos (show x=v∧y=w from g)
 ext i j; exact if_neg (show ¬(x=v∧y=w) from g)
lemma palp: snapH S T L=(nose S x)ᴴ*a*nose T y:=by rw [grantF]; simp_rw [star_P]; simp [apply_ite,ite_mul,mul_ite,ite_and] -- tune
local notation "Y₀"=> baseF false
local notation "Y₁"=> baseF true
local notation "V"=> bud_k o x y a
lemma vibra(s t:Pal)(p:nose S x=rain_U o x• s)(q:nose T y=rain_U o y • t): snapH S T (bud_k o x y a)=sᴴ*a*t:=by
 unfold bud_k; rw [palp,p,q]; let Q:= rain_U o x; let z:=rain_U o y; change star (Q • s) *(Q • z • a)*(z • t)=_; rw [star_smul, show star Q= Q from fee_real _]; simp only [Matrix.smul_mul,Matrix.mul_smul]; simp only [smul_smul]; rw [show z * (Q * (z * Q)) = (z*z)*(Q*Q) from (by ring),show z*z=1 from fee_one _,show Q*Q=1 from fee_one _,mul_one,one_smul]; rfl
lemma pillar (Z:Axis)(b:Bool) : baseF b * ditF b Z * baseF b=0:=by
 let M:= baseF b; let P:=ditF b Z; have he:=congrArg (· * M) (show M*P+P*M=P from φ_mix b Z); rw [add_mul,mul_assoc P,show M*M=M from φ_sq _] at he; exact add_right_cancel (he.trans (zero_add _).symm)
local notation "ℓx"=> Lattice.lift (x-o)
local notation "ℓy"=> Lattice.lift (y-o)
local notation "sX" i=> ((ℓx i:ℂ) • a)
local notation "sY" i=> ((ℓy i:ℂ) • a)
lemma vita (p:culm a=a): pub o V=(a,fun i=>sX i,fun i=>sY i):=by
 have hx:Y₀*a=a:=by nth_rw 1 [←p]; unfold culm; rw [←mul_assoc Y₀,←mul_assoc Y₀,φ_sq]; exact p
 have hy:a*Y₁=a:=by nth_rw 1 [←p]; unfold culm; rw [mul_assoc,φ_sq]; exact p
 refine Prod.ext ((vibra o x y a (rampF false o) (rampF true o) Y₀ Y₁ rfl rfl).trans (by rw [φ_a,hx,hy])) (Prod.ext (funext fun i=>?_) (funext fun i=>?_)) -- ABI
 · change culm (snapH (spanH false o _) (rampF true o) V)=_; rw [vibra o x y a _ _ (moonB false i ℓx) Y₁ rfl rfl]; unfold culm moonB; change Y₀ * (star ((ℓx i:ℂ) • Y₀+ditF false i) *a* Y₁)*Y₁=_; simp only [star_add,star_smul,map_intCast, Matrix.add_mul,Matrix.mul_add]; rw [show star Y₀=_ from φ_a false]; let T:= ditF false i
   have he:Y₀*star T*a=0:=by rw [←hx, ←mul_assoc (Y₀*_), show Y₀*star T*Y₀=star (Y₀*T*Y₀) from (by simp only [star_mul,show star Y₀=Y₀ from φ_a false,mul_assoc]), pillar,star_zero,zero_mul] -- tune
   simp only [Matrix.mul_smul,Matrix.smul_mul,hx,hy]; rw [←mul_assoc Y₀,←mul_assoc Y₀, he]; simp
 change culm (snapH (rampF false o) (spanH true o _) V)=_; rw [vibra o x y a _ _ Y₀ (moonB true i ℓy) rfl rfl]; unfold culm moonB; rw [φ_a]; let T:=ditF true i; change Y₀*(Y₀*a*((ℓy i:ℂ) • Y₁+T))*Y₁=_
 have he:a*T*Y₁=0:=by nth_rw 1 [←hy]; rw [mul_assoc a,mul_assoc a,pillar,mul_zero]
 simp only [Matrix.mul_smul,Matrix.smul_mul,hx,hy,mul_add,add_mul]; rw [←mul_assoc Y₀,hx,he,add_zero] -- simp after
local notation "D" x:max y:max a:max=> bud_k o x y a
variable (Ψ:Dome)
def spring_V (p:Site n):= let U:=fun i=>p+step i; bud_k p p p Ψ.1 + ∑ i:Axis, ((bud_k p (U i) p (Ψ.2.1 i)-bud_k p p p (Ψ.2.1 i))+(bud_k p p (U i) (Ψ.2.2 i)-bud_k p p p (Ψ.2.2 i)))
variable (g:seedsP Ψ)
lemma pulse_(a:Pal)(h:culm a=a): pub o (bud_k o o o a)=(a,0,0):=by rw [vita _ _ _ a h]; simp; rfl
include g
lemma fief_Ψ (p:3≤n.val) : jetsL o (spring_V Ψ o)=Ψ:=by
 unfold spring_V; rw [pub_eq,map_add,map_sum, pulse_ o _ g.1]; simp_rw [map_add,map_sub, vita _ _ o _ (g.2.1 _),pulse_ o _ (g.2.2 _),vita _ o (o+_) _ (g.2.2 _)] -- vita may match pulse wrong
 simp_rw [add_sub_cancel_left,sub_self,lift_step p]; refine Prod.ext ?_ (Prod.ext (funext fun i=>?_) (funext fun i=>?_))<;> (simp [step,Prod.fst_sum,Prod.snd_sum,Finset.sum_apply,Pi.single_apply])
end YM.CF.Moto
