import YM.CF.Urn.Role
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
variable {α n:Type*}[Fintype n][LinearOrder n]{P N L:Side}(G:Ratio N P)(j:ℕ)(K: WG α)(S:α→Male)
-- Backward orientation of same tilt
abbrev vaseR (i:α) {N P:Side}(G: Ratio N P)(x: Coil N P):= -star (prime j K S i G (icec x))
abbrev nukeR(h:Odd L.val): Script α:= fun i _ _ G x=> bentT (pine j L h (Thread j) false (S i) G x) (wh j L h false (S i) G x) (ticketT (Thread j) false (S i) G x) (vaseR j K S i G x)
lemma soarR(L:Side)(h:Odd L.val)(hj:Even j)(p:1≤j)(v:Lively K)(f:∀ i n,K i n 1=0):Slope L (nukeR j K S h) (1/2):=by
 have he:Save L true true (vaseR j K S) := by
    have hx:=(prism_s L h j hj p K v f S).1; -- tune
    have hy:= ((Save.one α).sub (Save.one α)).sub (hx.withOpp ..)
    simpa only [sub_self,zero_sub,vaseR] using hy
 obtain ⟨W,X,B⟩:=cup j L h hj p (canUse j L h) false; let A:=transportS (pine_funds j L h hj p _ (canUse j L h) false) S
 apply ThinSlope _ ((A.mul ((transportS B S).mul (transportS W S))).mul he) _ _ (by norm_num)
 intro i N P G hg; unfold vaseR; rw [show icec (1:Coil N P)=1 from ?_, pale_z j K f]; simp
 have ht: unionP (1:Nom N P)=1:= ?_; rw [← ht, revI]
 simp [unionP,profile_trivial]
-- elementary air
open Kennel
variable {b r:Bool}(U:UNI n)
lemma prima(P X C:Op n)(x:IsStarProjection X)(h:sings b U P=swapX r X):capT X (Thera.jazz r (sings b U C))= Thera.jazz r (sings b U (capT P C)):=by
 -- requires star
 cases r
 · unfold swapX at h; change sings _ _ P=X at h; subst X; unfold capT; change _= sings _ _ _; simp only [singT,win_m,win_l,win_i,map_mul,map_sub,map_one]; rfl
 · change sings _ _ P=1-X at h
   change capT X (-star _)= -star _; unfold capT; rw [singm,singm, singT b U (1-P),win_l,win_i,map_sub, map_one]; rw [←singT,h,sub_sub_cancel,star_mul,star_mul, x.one_sub.isSelfAdjoint, x.isSelfAdjoint, mul_neg,neg_mul,mul_assoc]
end YM.CF.Levier
