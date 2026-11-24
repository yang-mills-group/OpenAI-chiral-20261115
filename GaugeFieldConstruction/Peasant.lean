import GaugeFieldConstruction.Rallied
set_option autoImplicit false
set_option maxHeartbeats 100000
noncomputable section
namespace YM.GaugeFieldConstruction.Wick.Yacht
open StressFHeat MeasureTheory Analysis Function Filter Metric Maxwell Finset Gap Complex Cauchy Row Phys Flux.One Lamp
open Lattice CF CF.XGarden CF.XGarden.MastTin CF.XGarden.MastTin.ArtCart CF.XGarden.MastTin.ArtCart.Violets CF.Py.Rate.LocalLimit.Papal
open scoped Topology ContDiff BigOperators Classical
open HopeC CF.Buffered CF.Buffered.Lifted
-- sum over stencil. unitaries factors. weights. arbitrary n0.
variable {N:Side}
def BaseD : Genre → ℕ
 | .pure=> 3
 | .gauge=>4
 | .mixed=>5
abbrev pPow (i:Payν N):ℕ:=BaseD i.2.1
namespace Rally
lemma wallet {α:Type*}{s:Finset α}{F G:α→ℂ}{C b:ℝ}(t:0≤ b)(p:∀ i∈s,Rally C b (F i) (G i)): Rally (↑s.card*C) b (∑ i∈s,F i) (∑ i∈s,G i):=by
 classical
 induction s using Finset.induction_on with
 | empty=> simp; exact zero 0 b le_rfl t
 | insert a s f h=>
    have he:=p a (mem_insert_self ..); have hp:=h (fun i hi=>p _ (mem_insert_of_mem hi)); simpa [f,add_mul,add_comm] using he.twice hp
lemma fall {α:Type*}[Fintype α]{F G:α→ℂ}{C b:ℝ}{L:ℕ}(t:0≤ b)(v:0≤C)(r:Fintype.card α≤L)(p:∀ i,Rally C b (F i) (G i)): Rally ((L:ℝ)*C) b (∑ i,F i) (∑ i,G i):=(wallet t (fun i _=>p i)).mono (mul_le_mul_of_nonneg_right (by exact_mod_cast r) v) t
lemma abide {x y z:ℂ}{K C p:ℝ}(w: 0≤C)(t:0≤p)(v: Rally C p y z)(h:‖x‖≤K): Rally (K*C) p (x*y) (x*z):=by
 have he:0≤ K:=(norm_nonneg _).trans h; refine ⟨(norm_mul ..).le.trans (mul_le_mul h v.go (norm_nonneg _) he),(norm_mul ..).le.trans (mul_le_mul h v.pay (norm_nonneg _) he),?_⟩ -- w t unused
 rw [←mul_sub,norm_mul,mul_assoc]; exact mul_le_mul h v.error (norm_nonneg _) he
end Rally
variable (t:ℝ)(g:0<t)
open Gleam.Guide.Pitcher.Coins
include g
lemma p2sale(a b:Payν N)(i:Eams a)(j:Eams b): Chip.budget2 κg κF (apices a i) (apices b j)=(t:ℂ)^(pPow a+pPow b)*Chip.budget2 (gT t) (fT t) (apices a i) (apices b j):=by
 rcases a with ⟨w,v,r⟩; rcases b with ⟨x,p,Y⟩; have ht:(t:ℂ)≠0:=by exact_mod_cast g.ne'
 cases v <;> cases p <;> dsimp only [Chip.budget2, pPow,BaseD,gT,fT,P2Γ,apices,ChipUp] -- tune remove
 all_goals field_simp <;> ring -- dsimp projection mixed shapes works?
lemma p3sale (a b c:Payν N)(i:Eams a)(j:Eams b)(k:Eams c): Chip.budget3 κg κF (apices a i) (apices b j) (apices c k)=(t:ℂ)^(pPow a+pPow b+pPow c)*Chip.budget3 (gT t) (fT t) (apices a i) (apices b j) (apices c k):=by
 rcases a with ⟨w,v,r⟩; rcases b with ⟨x,p,Y⟩; rcases c with ⟨l,e,D⟩; have ht:(t:ℂ)≠0:=by exact_mod_cast g.ne'
 cases v <;> cases p <;> cases e <;> dsimp only [Chip.budget3,pPow,BaseD,gT,fT,P2Γ,T2Γ,Δρ,apices,ChipUp]
 all_goals field_simp <;> ring -- tune
lemma lap2n(a b:Payν N): quotaZ a b (gT t) (fT t)= quotaZ a b κg κF/(t:ℂ)^(pPow a+pPow b):=by
 rw [eq_div_iff (pow_ne_zero _ (show (t:ℂ)≠0 from by exact_mod_cast g.ne')),mul_comm]; unfold quotaZ; simp_rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; rw [p2sale t g,mul_left_comm]
lemma lap3n (a b c:Payν N): quotas a b c (gT t) (fT t)= quotas a b c κg κF/(t:ℂ)^(pPow a+pPow b+pPow c):=by rw [eq_div_iff (pow_ne_zero _ (show (t:ℂ)≠0 from by exact_mod_cast g.ne')),mul_comm]; unfold quotas; simp_rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; apply Finset.sum_congr rfl; intro j _; apply sum_congr rfl; intro k _; rw [p3sale t g,mul_left_comm]
omit g
variable (m:ℕ)
abbrev RankBook (i:Payν N):Book:=∑ v:Eams i, Forces i v • Lake t m i.1 (apices i v)
namespace Rally
variable {X:Type}[AddCommGroup X][Module ℂ X]{I J K:Type*}[Fintype I][Fintype J][Fintype K]{L M N₀:ℕ}{a:I→ℂ}{b:J→ℂ}{d:K→ℂ}{u v w B C:ℝ}{f:I→X}{e:J→X}{q:K→X}
private lemma B12 (F:X→ₗ[ℂ]X→ₗ[ℂ]ℂ)(f:I→X)(e:J→X)(a:I→ℂ)(b:J→ℂ): F (∑ i,a i • f i) (∑ j,b j • e j)=∑ i,∑ j,a i*b j*F (f i) (e j):=by
 rw [map_sum F,LinearMap.sum_apply]; apply Finset.sum_congr rfl; intro i _; rw [map_smul F,LinearMap.smul_apply,map_sum,smul_eq_mul,mul_sum]; exact Finset.sum_congr rfl (fun j _=> by rw [map_smul,smul_eq_mul,mul_assoc])
private lemma B13 (F:X→ₗ[ℂ]X→ₗ[ℂ]X→ₗ[ℂ]ℂ)(f:I→X)(e:J→X)(q:K→X)(a:I→ℂ)(b:J→ℂ)(d:K→ℂ): F (∑ i,a i • f i) (∑ j,b j • e j) (∑ k,d k • q k)=∑ i,∑ j,∑ k,a i*b j*d k*F (f i) (e j) (q k):=by
 rw [map_sum F,LinearMap.sum_apply,LinearMap.sum_apply]; apply Finset.sum_congr rfl; intro i _; rw [map_smul F,LinearMap.smul_apply,LinearMap.smul_apply,B12 (F (f i)),smul_eq_mul, Finset.mul_sum]; simp_rw [mul_sum, ←mul_assoc]
private lemma rank_B2 {P:I→J→ℂ}(g:0≤B)(c:0≤ C)(r:0≤u)(s:0≤v)(h:Fintype.card I≤ L)(k:Fintype.card J≤M)(hu:∀ i,‖a i‖ ≤ u)(hv:∀ j,‖b j‖≤v)(F:X→ₗ[ℂ]X→ₗ[ℂ]ℂ)(p:∀ i j,Rally C B (P i j) (F (f i) (e j))): Rally ((L:ℝ)*((M:ℝ)*(u*v*C))) B (∑ i,∑ j,a i*b j*P i j) (F (∑ i,a i • f i) (∑ j,b j • e j)):=by

 rw [show F _ _ = ∑ i:I,∑ j:J,a i*b j*F (f i) (e j) from B12 F f e a b]; refine Rally.fall (C:=(M:ℝ)*(u*v*C)) g (by positivity) h fun i=> Rally.fall (C:=u*v*C) g (by positivity) k fun j=>?_ ; exact abide c g (p _ _) ((norm_mul ..).le.trans (mul_le_mul (hu i) (hv j) (norm_nonneg _) r))
lemma rank_B3 {P:I→J→K→ℂ}(g:0≤ B)(c:0≤ C)(r:0≤ u)(s:0 ≤ v)(e0:0≤w)(h:Fintype.card I≤ L)(k:Fintype.card J≤M)(l:Fintype.card K≤ N₀)(hu:∀ i,‖a i‖ ≤ u)(hv:∀ j,‖b j‖≤v)(hk:∀k,‖d k‖ ≤w)(F:X→ₗ[ℂ]X→ₗ[ℂ]X→ₗ[ℂ]ℂ)(p:∀ i j k,Rally C B (P i j k) (F (f i) (e j) (q k))):Rally (↑L*(↑M*(↑N₀*(u*v*w*C)))) B (∑ i,∑ j,∑ k,a i*b j*d k*P i j k) (F (∑ i,a i • f i) (∑ j,b j • e j) (∑ k,d k • q k)):=by

 rw [show F _ _ _=∑ i:I,∑ j:J,∑ k:K,a i*b j*d k*F (f i) (e j) (q k) from B13 F f e q a b d]; refine Rally.fall (C:=(M:ℝ)*(↑N₀*(u*v*w*C))) g (by positivity) h fun i=> Rally.fall (C:= ↑N₀*(u*v*w*C)) g (by positivity) k fun j=>Rally.fall (C:=u*v*w*C) g (by positivity) l fun i' =>?_ ; refine abide c g (p _ _ _) ?_; simp only [norm_mul]; exact mul_le_mul (mul_le_mul (hu i) (hv j) (norm_nonneg _) r) (hk i') (norm_nonneg _) (mul_nonneg r s)
end Rally
include g
lemma Ring2n {c u v:ℝ}{L M:ℕ}(a b:Payν N)(p:Captain t a.1 b.1 m c)(h:1≤ c)(hL:Fintype.card (Eams a)≤L)(hM:Fintype.card (Eams b)≤M)(H:∀ i,‖Forces a i‖≤ u)(w:∀ j,‖Forces b j‖≤ v)(hu:0≤u)(hv:0≤v): Rally (↑L*(↑M*((u*v)*cashF c))) (t^(m+1)) (quotaZ a b κg κF/((t:ℂ)^(pPow a+pPow b))) (BigP (mount t a.1) (mount t b.1) (RankBook t m a) (RankBook t m b)):=by
 rw [←lap2n t g]
 refine Rally.rank_B2 (C:=cashF c) (f:=fun i=>Lake t m a.1 (apices a i)) (e:=fun j=>Lake t m b.1 (apices b j)) (P:=fun i j=> Chip.budget2 (gT t) (fT t) (apices a i) (apices b j)) (pow_nonneg g.le _) (by unfold cashF; positivity) hu hv hL hM H w _ ?_
 intro i j; exact breech t _ _ m p h g _ _ (Uptick ..) (Uptick ..)
omit g
lemma chip_x (a:Payν N)(v:a.2.1≠Genre.mixed)(i:Eams a): (apices a i).nox=true:=by rcases a with ⟨x,u,F⟩; cases u; rfl; contradiction; rfl
include g
lemma Ring3n {c u v W:ℝ}{L M N':ℕ}(a b d:Payν N)(Z:a.2.1 ≠ Genre.mixed)(p:Captain t a.1 b.1 m c)(P:Captain t b.1 d.1 m c)(V:Captain t a.1 d.1 m c)(h:1≤ c)(hL:Fintype.card (Eams a)≤L)(hM:Fintype.card (Eams b)≤M)(hk:Fintype.card (Eams d)≤N')(H:∀ i,‖Forces a i‖≤ u)(w:∀ j,‖Forces b j‖≤ v)(hF:∀ j,‖Forces d j‖≤ W)(hu:0≤u)(hv:0≤v)(he:0≤W): Rally (↑L*(↑M*(↑N'*(u*v*W*cashF c)))) (t^(m+1)) (quotas a b d κg κF/((t:ℂ)^(pPow a+pPow b+pPow d))) (prism (mount t a.1) (mount t b.1) (mount t d.1) (RankBook t m a) (RankBook t m b) (RankBook t m d)):=by
 rw [←lap3n t g]; refine Rally.rank_B3 (C:=cashF c) (f:=fun i=>Lake t m a.1 (apices a i)) (e:=fun j=>Lake t m b.1 (apices b j)) (q:=fun j=>Lake t m d.1 (apices d j)) (P:=fun i j k=> Chip.budget3 (gT t) (fT t) (apices a i) (apices b j) (apices d k)) (pow_nonneg g.le _) (by unfold cashF; positivity) hu hv he hL hM hk H w hF _ ?_
 intro i j k; exact tryst t _ _ _ m p V P h g _ _ _ (chip_x a Z i) (Uptick ..) (Uptick ..) (Uptick ..)
end YM.GaugeFieldConstruction.Wick.Yacht
end
