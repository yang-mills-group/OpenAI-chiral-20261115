import YM.CF.Levier.Voila
set_option maxHeartbeats 350000
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 20000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Levier
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Matrix Scroll Thera Branch Laic Cube
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Proa Urn
open Kennel
variable {L N P:Side}{j:ℕ}{A:Type*}(K:WG A)(S:A→Male)(G:Ratio N P)(h:Odd G.count.val)(i:A)
variable {b r:Bool}(a:Shape)(B:ColorT b)(U:UNI SpinIdx)
-- sparse relation matrices all profiles
local notation "R"=>pflux a G U B
local notation "Q"=>Shape.broad G a
variable (x:Nom N P) {e:ℝ}
local notation "z"=> stanza G a B x
variable (hp:∀ y:Bkg (More N),Guard y e→PaidG j e y)(hv:∀ y:Bkg (More P),Guard y e→PaidG j e y)
variable (u:JetS a.s b r U)(p:1≤j)(f:JointB G x e)
def marge(W: Op (Iota G)):= W.submatrix id (patchQ G)
lemma zoom (i j:Single N):(R).val (patchQ G i) (patchQ G j)=(prepU a U B N).val i j:=by
 rcases i with ⟨⟨v,s⟩,i⟩; rcases j with ⟨⟨x,t⟩,j⟩
 let D(y:Site N):=(milU a U B y).val
 change jump (paceU a G) (fun i=> D i.1) ((v,0),s,i) ((x,0),t,j)= jump (Tofu a N) D (v,s,i) (x,t,j); rw [jump_apply,jump_apply]; change (if (_,a.s.act (0:Site G.count))=(x,0) then _ else _)=(if _ then _ else _); simp
lemma exitZ (x:Single N)(i:Iota G)(p:i∉ lows (patchQ G)): (R).val (patchQ G x) i=0:=by
 let L:= hood G
 have he: sings b R L=L:= hoodL ..
 have hj: windX b L=L:=by unfold L; rw [lighthouse]; cases b; rfl; ext i j; unfold cutM; rw [windX]; simp only [ite_true,cc_apply]; simp [Matrix.diagonal_apply]; split <;>simp[*] -- tune
 rw [singT, hj, twist_formula] at he; have hp:(R).val *L=L*(R).val:=by nth_rw 2 [←he]; rw [mul_assoc,(R).property.1,mul_one]
 unfold L at hp; rw [lighthouse] at hp; have ht:= Matrix.ext_iff.mpr hp (patchQ G x) i; rw [cutM,mul_diagonal,diagonal_mul,if_pos (coil_hit ..),one_mul,if_neg p,mul_zero] at ht; exact ht.symm
lemma marchT(X:Op (Iota G)): marge G (sings b R X)= suburban b R (prepU a U B N) (marge G X):=by
 unfold marge suburban; rw [singT, twist_formula]; ext i l
 let D:= windX b X; change ((R).val*D*star (R).val) i (patchQ G l)= _; rw [Matrix.mul_apply, Matrix.mul_apply,← sum_subset (subset_univ (lows (patchQ G)))]; swap; · intro k _ v; change _*star ((R).val _ _)=_; rw [exitZ G a B U _ _ v,star_zero,mul_zero] -- tune
 unfold lows; rw [sum_map]; apply sum_congr rfl; intro j _; change _*star ((R).val _ (patchQ G j))=_*star ((prepU a U B N).val l j); rw [zoom]; congr 1; simp only [Matrix.mul_apply]; cases b <;>rfl
variable (y:Bkg (More P))(hk:Guard y e)
local notation "ξ"=>profile y
local notation "ω₀"=> profile (stir B Q y)
include u p hv h hk
lemma barf (t v:Bool): sings b R (Urn.vane G j S i t v (unionP x,ξ))= vane G j S i (t.xor r) v (unionP z,ω₀):=by
 rw [vane,vane,portFoot G h]; cases v; rw [show Urn.cope _ _ _ _ _ _=1 from rfl,singT,win_i,map_one]; rfl
 dsimp only; rw [Bool.xor_comm t]; exact congrArg (foot G) (skew_lobe Q B U u j p _ y _ hv hk t) -- issue notation
variable (xk:∀ o (y:Nom N P), y=x∨y= (stanza G a B x) → Along j G.count h (Thread j) o (S i) G (unionP y))(J:IsUnit (Peaks.cloth j (S i) G (unionP x)))(c:K i P (profile (stir B (Shape.broad G a) x.1))=Thera.jazz r (sings b (prepU (Shape.broad G a) U B P) (K i P (profile x.1)))) (l:IsUnit (1+nuke G.count h j K S i G (unionP x)))(m:IsUnit (1+nukeR j K S h i G (unionP x)))
local notation "R₁"=>dancer K S G h i a B U x hp hv u p f xk J c l m
local notation "R₂"=>barf S G h i a B U x hv u p y hk
include hp f xk J c l m
lemma settle (t v:Bool): sings b R (Ash G h j K S i t v (unionP x,ξ))= Ash G h j K S i (t.xor r) v (unionP z,ω₀):=by
 have hy(P:Op (Iota G)):sings b R (star P)=star (sings b R P):=by rw [singT,singT,win_s,map_star]
 unfold Ash Sky treeF; rw [smoke_r,smoke_r]; dsimp only; rw [revI,revI,singm,singm,hy,hy,R₂,hoodL]; congr 2; rw [R₁] -- tune
lemma player (t s v n o q:Bool): sings b R (ember G h j K S i t s v n o q (unionP x,ξ))= ember G h j K S i (t.xor r) (s.xor r) v n (o.xor r) (q.xor r) (unionP z,ω₀):=by
 have hy(P:Op (Iota G)): sings b R (star P)=star (sings b R P):=by rw [singT,singT,win_s,map_star]
 unfold ember Urn.meet Spree; rw [smoke_r,smoke_r]; dsimp only; rw [revI,revI,singm,singm,singm,hy,hy,R₂,R₂,R₁,R₁]
end YM.CF.Levier
