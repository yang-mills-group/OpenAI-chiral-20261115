import YM.CF.Levier.Palais
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
include hp hv p f u
lemma covers (J:IsUnit (Peaks.cloth j (S i) G (unionP x)))(t:Bool): sings b R (foal j t (S i) G (unionP x))=foal j (t.xor r) (S i) G (unionP z) ∧ sings b R (wh j G.count h t (S i) G (unionP x))= wh j G.count h (t.xor r) (S i) G (unionP z)∧ sings b R (ticketT (Thread j) t (S i) G (unionP x))=ticketT (Thread j) (t.xor r) (S i) G (unionP z):=by
 obtain ⟨x,y⟩:= hoarD G h a B U u j p (S i) e x f hp hv t; rw [Bool.xor_comm t]; exact ⟨x,y,titles _ h _ _ _ u _ _ _ _ J⟩
local notation "A₁"=>prime j K S i G
variable (xk:∀ o (y:Nom N P), y=x∨y= (stanza G a B x) → Along j G.count h (Thread j) o (S i) G (unionP y))(J:IsUnit (Peaks.cloth j (S i) G (unionP x)))(c:K i P (profile (stir B (Shape.broad G a) x.1))=Thera.jazz r (sings b (prepU (Shape.broad G a) U B P) (K i P (profile x.1)))) (l:IsUnit (1+nuke G.count h j K S i G (unionP x)))(m:IsUnit (1+nukeR j K S h i G (unionP x)))
include xk J l m c
local notation "R₀"=>covers S G h i a B U x hp hv u p f J
local notation "π₀"=> Proa.prism G.count h j K S i G
lemma season : π₀ (unionP z)= Thera.jazz r (sings b R (π₀ (unionP x))):=by
 let M:= S i; let D(y:Nom N P)(t):= foal j t M G (unionP y); have ht: A₁ (unionP z)= Thera.jazz r (sings b R (A₁ (unionP x))):=by
    have hx:sings b R (D x true)=swapX r (D z true):=by rw [show sings _ _ (D x true)=D z (true.xor r) from (R₀ true).1]; cases r; rfl; exact foil_neg ..
    have hg(T:Op (Single P)):foot G (Thera.jazz r T)= Thera.jazz r (foot G T):=by cases r <;>rfl
    change capT (D z true) (foot G (K i P (profile (stir _ Q x.1))))= _; rw [c,hg,←portFoot G h]; exact prima R (D x true) _ _ (xk true z (Or.inr rfl)).lead hx
 unfold Proa.prism; rw [ht]; refine piano S G h i a B U x z xk _ (tag_g _ (xk true _ (Or.inl rfl)).lead) R₀ l ?_; unfold nukeR vaseR at m; rw [revI] at m; exact m
lemma dancer (t q:Bool): sings b R (Urn.startZ j K S h t q i G (unionP x))= Urn.startZ j K S h (t.xor r) (q.xor r) i G (unionP z):=by
 unfold Urn.startZ; rw [saved_P,saved_P,singm]; simp only [mul_one]
 let W(o:Bool)(y:Nom N P):=wh j G.count h o (S i) G (unionP y); let A(u:Bool)(y:Nom N P):=coldY j S u i G (unionP y)
 have hpri(q y): Proa.sprig q (W true y)= W q y:=by cases q; exact (wh_neg j G.count h G true _ _).symm; rfl
 -- no shadow leads issue
 change sings _ _ (Proa.sprig q (W _ _))*sings _ _ (liftJet t _ (A _ _) (A _ _))= Proa.sprig (q.xor r) (W _ _) * _
 have hk(u): sings b R (A u x)=A (u.xor r) z:=(R₀ u).2.2
 rw [hpri,hpri,show sings _ _ (W q x)=_ from (R₀ q).2.1]; change W _ _*_ = W _ _ * liftJet _ (π₀ (unionP z)) (A true z) (A false z); rw [season K S G h i a B U x hp hv u p f xk J c l m]; congr 1; unfold liftJet
 cases t<;> simp only [Bool.false_eq_true,ite_false,ite_true,singT,win_m,win_a,win_l,win_i,win_s,map_mul,map_add,map_sub,map_one,map_star] <;> simp_rw [← singT] <;>rw [hk] <;> cases r <;>simp [Thera.jazz,sub_eq_add_neg]
end YM.CF.Levier
