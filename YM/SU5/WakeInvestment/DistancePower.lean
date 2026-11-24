import ZecaQuorum

/-! Homogeneity and identity of pure spin prices in announced coordinate units.
 Wake covariance includes the *signs*. For `qRaw`, which uses raw c,r respectively
 (and 1/16 both-leg normalization), `Powe` on that price: limit at
 $R \text{ matter mesh steps}$ of $R^3$ times the unnormalized sum of c*r
 (or $1/2$ per each factor to pay the scaled $qRaw$ in gauge R units).
 -/
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Ballad.SpinReceipt
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Lifted Bilinear Window Skye Emu Onyx Kea Flare Dial
open Cache Glaze Cordial
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
open Lead (Clan)
open Twah
open YM.Stationary (Gaia)
variable {I:Type*}
private lemma howPair {L:List I} (z:Bout I)(h:z∈picks L): z.back.length+1=L.length:=by
 induction L generalizing z with
 | nil=> simp [picks] at h
 | cons x L ih=>
    rcases List.mem_cons.mp h with p|p; · rw [p]; rfl
    obtain ⟨x,h',rfl⟩:= List.mem_map.mp p; exact congrArg (·+1) (ih x h') 
private lemma howMuch {L:List I} (v:Cl I)(h:v∈ claps L): v.up.length*2+v.term.length=L.length:=by
 induction L generalizing v with
 | nil=> change v∈[⟨false, [],[]⟩] at h; rw [List.mem_singleton.mp h]; rfl
 | cons i L ih=>
    obtain ⟨l,q,p⟩:= List.mem_flatMap.mp h; specialize ih l q; rcases List.mem_cons.mp p with p|p
    · rw [p]; change l.up.length*2+(l.term.length+1)=L.length+1; omega
    obtain ⟨y,p',rfl⟩:= List.mem_map.mp p; change (l.up.length+1)*2+y.back.length=L.length+1; have hp:=howPair y p'; omega
private lemma offer_factor {L:List I} (z:Cl I)(D:I→I→ℂ)(a:ℂ)(h:z∈claps L) (M:ℕ)(p:L.length=M*2) : spinC (fun u v=>a*D u v) z= a^M * spinC D z:=by
 let d(u v:I):= a*D u v; unfold spinC; split; swap; · rw [mul_zero]
 next he=> have ht:=howMuch z h; rw [List.isEmpty_iff_length_eq_zero] at he; rw [he,p] at ht; have hz:z.up.length=M:=by omega
           have hf(V:List (I×I)) : (V.map (fun u=>a* D u.1 u.2)).prod=a^V.length*(V.map (fun u=>D u.1 u.2)).prod:=by induction V with|nil=> simp|cons z v ih=>rw [List.map_cons,List.map_cons,List.prod_cons,List.prod_cons,ih,List.length_cons,pow_succ]; ring -- indent
           unfold offer; rw [hf,hz]; ring
private lemma rune_factor (L:List I)(M:ℕ)(p:L.length=M*2)(D:I→I→ℂ)(a:ℂ): runes (fun u v=>a*D u v) L=a^M*runes D L:=by
 unfold runes; generalize e : claps L= W; have he:∀ z∈ W,z∈ claps L:= by rw [e]; tauto; -- tune
 clear e; induction W with|nil=>simp|cons i W ih=> rw [List.map_cons,List.map_cons,List.sum_cons,List.sum_cons,ih (fun i p=> he i (List.mem_cons_of_mem _ p)),offer_factor i D a (he i (List.mem_cons_self)) M p,mul_add]

private lemma pencil_scale (x:Gaia) {a:ℝ}(p:0<a): Onyx.pencil x=a^3 • Onyx.pencil (a • x):=by
 have hg: gleamV (a • x)=a • gleamV x:=by
    unfold gleamV; rw [←Matrix.mul_smul,Finset.smul_sum]; apply congrArg (minA* ·); exact sum_congr rfl fun i _=> by rw [PiLp.smul_apply,smul_eq_mul,Complex.ofReal_mul,RCLike.real_smul_eq_coe_smul (K:=ℂ),smul_smul]; rfl -- need use Complex real smul
 unfold Onyx.pencil; rw [norm_smul,Real.norm_of_nonneg p.le,hg,smul_smul,smul_smul, mul_pow,mul_inv_rev] -- tune inv
 congr 1; field_simp

variable (u v:I→Gaia)(a:ℝ)(x:0<a)(d:∀ i j,u i - u j = a • (v i-v j))
variable (l:List I)(g:I→Clan)(b:I→DirSpin)
local notation "Pᴬ" => (fun i:Cellz I=>u i.1)
local notation "Qᴬ" => (fun i:Cellz I=>v i.1)
def wakeSum (u:I→Gaia)(l:List I)(g:I→Clan)(b:I→DirSpin):= (1/2:ℂ)^l.length * Twah.witness g l (fun i:Cellz I=>u i.1) b
include d x
lemma wakePower : wakeSum v l g b=(a:ℂ)^(3*l.length)* wakeSum u l g b:=by
 let c:= (a:ℂ)^3; let D:= germRho (Pᴬ) b; let G:=germRho (Qᴬ) b; let w:=Pᴬ; let X:=Qᴬ
 have hv(i j:I): billX X b i j=c*billX w b i j:=by
    unfold billX; rw [show w _-w _ = a • (v i - v j) from d i j]; change Onyx.pencil (v i-v j) _ _=_; nth_rw 1 [pencil_scale (v i-v j) x]; simp [Complex.real_smul,c]
 have he:G=(fun i j=> c*D i j):=by
    funext i j; obtain ⟨i,a,x⟩:=i; obtain ⟨j,b₁,y⟩:=j; unfold G D; cases x <;> cases y
    all_goals unfold w X at hv; simp only [funds_neg,dcash,funds,hv,mul_zero,mul_ite,mul_neg] -- `dcash`, hv uses w not match
 have ht(M:ℕ)(A:List (Stamp I))(p:A.length=M*2): chore g (runes G) A l=c^(M+l.length)*chore g (runes D) A l:=by
    induction l generalizing A M with
    | nil=> rw [List.length_nil,add_zero]; change runes G A=_*runes D A; rw [he,rune_factor _ _ p]
    | cons i L ih=>
       rw [chore,List.length_cons,chore,mul_sum]; apply sum_congr rfl; intro v bv; rw [ih (M+1) _ (by unfold Twah.sayHi; rw [List.length_append,p]; change _+2=_; ring),show M+1+L.length=M+(L.length+1) from by omega]
 unfold wakeSum witness; rw [show chore g _ _ l=chore g (runes G) [] l from rfl,ht 0 _ rfl,pow_mul]; unfold c; rw [zero_add]; ring
omit d x
-- keep sign and normalization on off-axis x, orientations equal to qRaw in IC.3
variable (x' y:Gaia)(Z W:Clan)
def curlWeyl (x:Gaia):ℂ:= ((((Real.pi^2*‖x‖^4)⁻¹:ℝ):ℂ)/2)*((x 3:ℂ)+(x 2:ℂ)*Complex.I)
lemma shapeWeyl (x:Gaia): kP20 x=2*curlWeyl x:=by unfold kP20 curlWeyl Onyx.pencil; rw [Matrix.smul_apply,quaternion,Complex.real_smul]; ring
abbrev componentPrice :ℂ:= if Z=W then (dimf Z:ℂ) * (curlWeyl (y-x'))^2 else 0
lemma one_payment (p:I): wakeSum u [p] (fun _=>Z) b=0:=by
 unfold wakeSum; rw [chorus2]; unfold lyric; rw [Quorum.side u b]; ring
lemma two_payment (p q:I): wakeSum u [p,q] g 0=componentPrice (u p) (u q) (g p) (g q):=by
 unfold wakeSum componentPrice; rw [Quorum.duo_pay u _]; unfold billX; change (1/2:ℂ)^2*(if g p=g q then _ * -(kP20 (u p-u q)* kP20 (u q-u p)) else _)=_; rw [show u p-u q= -(u q-u p) from Eq.symm (neg_sub ..),k_flip,shapeWeyl]; split_ifs<;> ring -- ring
#print axioms shapeWeyl
#print axioms wakePower
end YM.CF.Buffered.Ballad.SpinReceipt
