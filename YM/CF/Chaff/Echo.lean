import YM.CF.Chaff.Load
import YM.CF.Fief.Lucid
import YM.CF.Char.Gel
import YM.Next.STATIONARY.Joint.OnShell
import YM.CF.Rill.Pott
import YM.CF.Skye.Hark
import YM.CF.Prism.Pecu
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 450000
noncomputable section
namespace YM.CF.Chaff
open Function NormedSpace Filter Metric Finset Lattice MeasureTheory RG
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical Kronecker
open Pressure
open Cube Lat Tenant Tulip Gully Spire Scroll Scree Jet Ave Skye Gas Pastry Dial Fock
open scoped Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {m B N: Side}{a e K H C:ℝ}{n:ℕ}
local notation "Λ" => CSide m B
local notation "ξ"=> Domain m B
local notation "G"=>SU.group
open Phase Branch
variable {D:Ave.Briar m B e→ Scree.Cipher (CSide m B)}{S:Stamp m B}
variable (p:0≤e)(h:Inscribed K e n S H D C)
local notation "Γ"=> tangD Λ
variable {s:ℝ}{R:Scree.Loom (CSide m B)}{P:BudgetPoint}{c:ℕ}(A:Roof (CSide m B) a s c R)(pH: P.threshold ≤ a)(v:s < e)(l:c≤P.B)
open MultiNext.SignedSource
variable (o:Seat (CSide m B))(y:o∈S) (t:Grove (terr _) S)
variable {r Y V x μ b θ C' ρ:ℝ} {M:ℕ}
lemma polyF (n:ℕ)(p:0<a):∃ c:ℝ,0≤c∧∀ i:ℕ,(1+i:ℝ)^n ≤ c*Real.exp (a*i):=by
 obtain ⟨c,u,h⟩:= Jet.stash 0 le_rfl n (show 0<2*a by linarith); refine ⟨_,u,fun i=>?_⟩; have hf:= h 1 zero_le_one i i le_rfl; rw [show 2*a/2=a by ring] at hf; let r:= (1+i:ℝ); have he: Real.exp (a*i)* (1+i:ℝ)^n≤Real.exp (a*i)* mercury i n 0 1:=by
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le; unfold mercury; apply le_mul_of_one_le_left (by positivity); rw [mul_zero,Real.exp_zero,mul_one,mul_one]; have h: (1:ℝ) ≤ n.factorial:=by exact_mod_cast Nat.factorial_pos _
    exact one_le_mul_of_one_le_of_one_le h (by simp)
 apply le_of_mul_le_mul_left ((he.trans hf).trans (le_of_eq ?_)) (Real.exp_pos _); rw [mul_one, mul_left_comm,← Real.exp_add]; congr 2; ring
lemma tuneR(K n:ℕ)(p:0<a):∃ V:ℝ,0 ≤ V∧∀ (P:BudgetPoint), P.power=K→ P.order=n→∀ (i:ℕ)(C:ℝ),0 ≤ C→ payP P i*(composeCost P.order C (riseH P i))+ C ≤ V*(Real.exp (a*i)*C):=by
 obtain ⟨X,t,g⟩:= polyF (K+K*n) p; let M:= n.factorial*(2:ℝ)^n; have hM:0 ≤ M:=by unfold M; positivity
 refine ⟨M*X+1,by positivity,fun P b c i C u=>?_⟩; rw [add_mul,one_mul]; unfold payP composeCost riseH; rw [b,c]; apply add_le_add
 · let q:ℝ:=(1+i:ℝ)^K; have hx:q ≥ 1:=one_le_pow₀ (by linarith [Nat.cast_nonneg (α:=ℝ) i]); have ht:1+P.threshold*q≤2*q:=(by rw [two_mul]; exact add_le_add hx (mul_le_of_le_one_left (zero_le_one.trans hx) P.threshold_le)); change q*((n.factorial:ℝ)*C*(1+P.threshold*q)^n) ≤ _; have hy: 0 ≤ (1+P.threshold*q):=by have he:=P.threshold_pos; positivity
   calc
    _ ≤ q*(n.factorial*C*(2*q)^n):=by gcongr
    _ = M*C*(1+i:ℝ)^(K+K*n):=by unfold q M; rw [pow_add,mul_pow,pow_mul]; ring
    _ ≤ _:= (mul_le_mul_of_nonneg_left (g i) (mul_nonneg hM u)).trans_eq (by ring)
 exact le_mul_of_one_le_left u (Real.one_le_exp (mul_nonneg p.le (Nat.cast_nonneg _)))
open Fief
lemma pay_g (T:Stamp m B)(h:Grove (terr _) T)(g:0<b)(t:2*P.supportExponent*(tileN 3)≤ b/2* (P.B:ℝ)):Real.exp (P.supportExponent* coverNumber P.B (taleX P T)) ≤ Real.exp (P.supportExponent*tileN 3)*rent (b/2) T:=by
 let F:= idrat (Domain m B); have ht (x:Site ξ): F.parent x=x:=by nth_rw 1 [←show F.embed x=x from glass ..]; exact Ratio.embed_parent ..
 have he:T.image F.parent=T:=by ext; simp [ht]
 nth_rw 1 [←he]; unfold taleX; exact fen F T P.B 3 P.B_pos _ P.supportExponent g P.exponent_pos.le (by change 2*P.supportExponent*(tileN 3)≤ b/2* (↑(1:ℕ):ℝ)* P.B; simp only [Nat.cast_one,mul_one]; exact t) h
/-- helper bill piece, integrate into spine. -/
abbrev cliff (P:BudgetPoint)(a C κ V t:ℝ)(U:Stamp m B):= taxH P U.card C κ+ t *(rent a U*(payP P U.card* composeCost P.order C (riseH P U.card)))
def HopeN(P:BudgetPoint)(a V t κ:ℝ):ℝ:= Real.exp (P.supportExponent * tileN 3)*(composeCost P.order (4*κ^2) 1+ Real.exp (-a*P.B)*V+t*V)
lemma hope_ng (p:0≤ V)(t:0≤ r): 0≤ HopeN P a V r θ:=by unfold HopeN composeCost; positivity
lemma told_S (S:Stamp m B)(v':0 ≤ V)(u:0 ≤ C)(f:0< b)(t:0≤r)(h:Grove (terr _) S)(x:payP P S.card*(composeCost P.order C (riseH P S.card))+C ≤ V*(rent b S*C))(y:2*P.supportExponent*(tileN 3)≤ b*(P.B:ℝ)) :
 P.mass (taleX P S) (cliff (m:=m) P b C θ μ r S) ≤ HopeN P b V r θ*(rent (4*b) S*C):=by
 let q:=Real.exp (P.supportExponent*tileN 3); have hv:=pay_g S h (b:=2*b) (by positivity) (by rw [show 2*b/2=b by ring]; exact y); rw [show 2*b/2=b by ring] at hv; let V':=cliff (m:=m) P b C θ μ r S; let Y:=composeCost P.order C (riseH P S.card); let t':=payP P S.card; let T (a:ℝ):=rent a S; let W:=T (4*b)
 have hU:1≤T b:= rent_one f.le S; have ht:1 ≤ t':= one_le_pow₀ (by simp); have hw:0 ≤ Y:=by unfold Y riseH composeCost; have he:=P.threshold_pos; positivity
 have hh:T b*T b*T b ≤ W:=by unfold T W rent; simp only [←Real.exp_add]; apply Real.exp_le_exp.mpr; nlinarith [mul_nonneg f.le (Nat.cast_nonneg (α:=ℝ) S.card)]
 have he:T b*(r*(T b*(t'*Y))) ≤ r*V*(W*C) :=by
    have hy:= (le_add_of_nonneg_right u).trans x; change t'*Y≤ V*(T b*C) at hy
    let R:=T b; have h:0 ≤R :=zero_le_one.trans hU; apply (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hy h) t) h).trans
    have hℓ:=mul_le_mul_of_nonneg_left hh (show 0 ≤ r*V*C by positivity); linarith -- maybe slow
 unfold BudgetPoint.mass; have hi:0≤V':= add_nonneg (ψtax _ _ u _) (mul_nonneg t (mul_nonneg (rent_pos ..).le (mul_nonneg (one_pos.trans_le ht).le hw)))
 refine (mul_le_mul_of_nonneg_right hv hi).trans ?_; set K1:=composeCost P.order (4*θ^2) 1; let K2:=Real.exp (-b*P.B)*V; have hk:0≤ K1:=by unfold K1 composeCost; positivity
 change q*T b*(taxH _ _ _ _+r*(T b*(t'*Y))) ≤ q*(K1+K2+r*V)*(W*C); rw [mul_assoc,mul_assoc q]; apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
 rw [mul_add,add_mul]; apply add_le_add _ he; rw [add_mul]; unfold taxH; split_ifs with g
 · rw [show composeCost _ _ _= K1*C from (show composeCost P.order (2*(C+C)*θ^2) 1=_ by unfold K1 composeCost; ring)]
   have hv:T b≤ W:=rent_up (by linarith : b ≤4*b) _; have hg:0≤ W:= (rent_pos ..).le; unfold K2; nlinarith [mul_le_mul_of_nonneg_right hv (mul_nonneg hk u), mul_nonneg (mul_nonneg (Real.exp_pos (-b*P.B)).le v') (mul_nonneg hg u)]
 have hv: T b*(composeCost P.order C (riseH P S.card)+C) ≤ T b*(V*(T b*C)):= mul_le_mul_of_nonneg_left ((add_le_add_left (le_mul_of_one_le_left hw ht) C).trans x) (rent_pos ..).le -- add_le_add orientation tune
 apply hv.trans; refine le_trans ?_ (le_add_of_nonneg_left (mul_nonneg hk (mul_nonneg (rent_pos ..).le u))); have hh: T b*T b ≤ Real.exp (-b*P.B)* W:=by
    unfold W T rent; simp only [←Real.exp_add]; apply Real.exp_monotone; have ht:(P.B:ℝ)≤ S.card:= Nat.cast_le.mpr (le_of_lt (not_le.mp g)); nlinarith [mul_nonneg f.le (Nat.cast_nonneg (α:=ℝ) S.card)]
 have hy:=mul_le_mul_of_nonneg_right hh (mul_nonneg v' u); unfold K2; linarith
end YM.CF.Chaff
