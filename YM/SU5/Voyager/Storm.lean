import YM.SU5.Voyager.Deacon
set_option autoImplicit false
noncomputable section
namespace YM.Spectral.Orbit.Prairie
open Function Filter Set Metric Finset Complex MeasureTheory Measure
open Boundary Boundary.Probe Caino
open scoped NNReal ENNReal Topology InnerProductSpace ComplexConjugate ComplexOrder BigOperators Classical
variable {K:Type*}[Fintype K][DecidableEq K]
local notation "X"=> Terrain K
variable {H: Hilbert} (T: Orbit H (Terrain K)) (P: PVM H (Terrain K))
local notation "U"=> T.translation
local notation "μ" y:max=> P.diagonal y
variable (g:ℝ)(n:ℕ)(k:K)(x:H)
local notation "ρ[" k "]"=> sight g k
local notation "Θ" k:max=> dart T g k
local notation "V"=> (Finset.univ:Finset K)
local notation "λ₀"=> Fintype.card K
local notation "d"=> (Fintype.card K:ℝ)
local notation "λ'"=> lamps g (V)
local notation "𝒫" n:max=> serves (P.diagonal x) (lamps g (V)) n
local notation "χ" n:max=> charFun (𝒫 n)
variable (p:T.Spectrum P)
include p
lemma caress (S:Finset K) : ∃ y:H,μ y= serves (μ x) (lamps g S) n∧ ‖y‖≤(2^n)^S.card*‖x‖:=by
 induction S using Finset.induction_on with
 | empty=> exact ⟨x,by simp [serves,lamps,chisels],by simp⟩
 | insert i S hi ih=>
   obtain ⟨y,h,q⟩:=ih; refine ⟨((Θ i)^n) y,?_,?_⟩
   · rw [n_dart T P g n i y p,h]; unfold serves; rw [ colors (μ x) ((lamps_cont ..|>.pow n).measurable) ((mallet_t ..|>.pow n).measurable) (fun i=>pow_nonneg (lamps_p _ S i) _), show lamps g (insert i S)= lamps g S*mallet ρ[i] from (prod_insert hi).trans (mul_comm ..),mul_pow];
   refine (darts_n ..).trans ((mul_le_mul_of_nonneg_left q (show 0 ≤ (2:ℝ)^n from by positivity)).trans_eq ?_); rw [card_insert_of_notMem hi,pow_succ',mul_assoc]
lemma lampsF : IsFiniteMeasure (𝒫 n):=by obtain ⟨y,v,w⟩:= caress T P g n x p (Finset.univ:Finset K); rw [←v]; infer_instance
lemma localLamp : ∃ c:ℝ,0<c ∧ ∀ᶠ i:ℕ in atTop, ∀ v:X,‖(χ i) v‖≤c^i:=by
 let c:ℝ:=(2^λ₀)^2; have hc:0<c:=(by positivity);
 refine ⟨c+1,(by positivity),?_⟩; filter_upwards [least hc (lt_add_one c) (‖x‖*‖x‖)] with i t; intro v; obtain ⟨y,h,q⟩:=caress T P g i x p (V); rw [←h,p]; refine (norm_inner_le_norm ..).trans ?_; rw [T.unitary]; apply le_trans (mul_le_mul q q (norm_nonneg _) (by positivity)) ?_; rw [←pow_mul, mul_comm i, pow_mul, card_univ]; refine Eq.le ?_ |>.trans t; unfold c; rw [← pow_mul (2^λ₀:ℝ),mul_comm 2 i,pow_mul]; ring
omit p
/- Laplace-temperature property EVERY direction for THIS specimen, after price FSpec promotion. no boost yet. -/
structure Quilt (g e b:ℝ) : Prop where
 edgeQ: 0<e
 beamQ: 0<b
 stays (k:K)(n:ℕ)(r:ℝ) (h:0<r): Offer T k x ((dart T g k^n) x) (e+r) (b*(2*g*n/r)^n)
-- numeric budget
private lemma roomBill (D g e R z:ℝ)(v:ℕ)(h:1 ≤ D)(p:0<g)(t:0<e)(q: 0<v)(hr:4*D*(e+g+1)*v ≤ R)(u:R ≤ D*z) : e+(1+R)/(4*D)+v*g≤ z:=by
 have he:0<D:=(by linarith); have ht: e+v*g ≤ (e+g)*v:=by nlinarith [(show 1 ≤ (v:ℝ) from (by exact_mod_cast q))] -- tune
 have hd:0≤ D*(v:ℝ):=(by positivity); have hw:(1+R)/(4*D)*(4*D)=1+R:=div_mul_cancel₀ _ (by positivity); apply le_of_mul_le_mul_right ?_ he; nlinarith [mul_le_mul_of_nonneg_right ht he.le,(show 1 ≤ (v:ℝ) by exact_mod_cast q)]
variable {e b:ℝ} (hg:0<g)(u: Quilt T x g e b)
include p u hg
variable [Nonempty K]
local notation "Y" k:max=> Finset.erase V k
lemma lamp_beam (k:K)(z:X)(n:ℕ)(q:4*d*(e+g+1)*n ≤ ‖z‖)(r:‖z‖ ≤ d*z k)(v:0<n): ‖(χ n) z‖≤((2:ℝ)^(2*λ₀+1))^n*b*(8*d*g*n/(1+‖z‖))^n :=by
 let D:ℝ:= (1+‖z‖)/(4*d); have he:1≤d:=by exact_mod_cast Fintype.card_pos (α:=K)
 have hD:0<D:=by positivity
 have ht:= leapFirst T g n k x (((Θ k)^n) x) hg (u.stays k n D hD)
 let x':=((Θ k)^n) x; obtain ⟨w,W,h⟩:=garment T P g n x' p (Y k) k _ (show k ∉ (Y k) from (by exact Finset.notMem_erase _ _)) ht
 have h': μ w= 𝒫 n:=by
   rw [W, show μ x'= serves (μ x) (mallet ρ[k]) n from n_dart T P g n k x p]; unfold serves; rw [colors (μ x) ((mallet_t ..|>.pow n).measurable) ((lamps_cont ..|>.pow n).measurable) (fun x=>pow_nonneg (mallet_p ρ[k] x) n), show lamps g V=mallet ρ[k]*lamps g (Y k) from (congrArg (lamps g) (Finset.insert_erase (mem_univ k)).symm).trans ( prod_insert (show k ∉ (Y k) from (by exact Finset.notMem_erase _ _))), mul_pow]; -- p
 let r':= b*(2*g*n/D)^n; let M:= ((2:ℝ)^(2*n))
 rw [← h',p]; apply le_trans (h z (roomBill d g e ‖z‖ (z k) n he hg u.edgeQ v q r)) _
 have hp:0 ≤ r':=by have hb:=u.beamQ; positivity
 have hx:0 < b:=u.beamQ
 refine (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (a:=M) (show _ from (by dsimp [M]; exact one_le_pow₀ (by norm_num))) (Finset.card_le_univ _)) (show 0 ≤ (2:ℝ)^n*r' from by positivity)).trans_eq ?_ -- adapt one_le_pow₀
 change ((2:ℝ)^(2*n))^λ₀ * (2^n*(b*(2*g*n/D)^n))=_; rw [← pow_mul,← pow_mul, show (2*λ₀+1)*n =2*n*λ₀+n by ring, pow_add, show 2*g*n/D=8*d*g*n/(1+‖z‖) from (by unfold D; field_simp; ring)]
 ring
lemma flashed : FlairC (fun i=> charFun (serves (P.diagonal x) (lamps g (V)) i)):=by
 letI : ∀ i, IsFiniteMeasure (𝒫 i):= fun n=> lampsF T P g n x p
 refine ⟨fun i=>measurable_charFun,localLamp T P g x p,?_⟩
 let a:=4*d*(e+g+1); let D:= (2:ℝ)^(2*λ₀+1); let q:= (8*d*g); have he:0<e:=u.edgeQ; let C:= max a (2*D*q); have hC:0<C:=(by positivity); have v':(0:ℝ)<1:=zero_lt_one
 refine ⟨C,hC,?_⟩; filter_upwards [eventually_gt_atTop 0,least v' (by norm_num: (1:ℝ)<2) b] with i hi hx; intro z hz; rw [one_pow,mul_one] at hx
 suffices h₀:‖(χ i) z‖ ≤ D^i*b*(q*i/(1+‖z‖))^i by
    apply h₀.trans; have hp:0≤D^i:=by positivity
    calc _ ≤ (D^i*(2:ℝ)^i)*(q*i/(1+‖z‖))^i:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx hp) (by positivity)
         _ = ((2*D*q)*i/(1+‖z‖))^i:=by rw [← mul_pow,← mul_pow]; congr 1; ring
         _ ≤ _:=by gcongr; exact le_max_right ..
 obtain ⟨k,r⟩:= shinAngle_bound z; have h:a*i ≤ ‖z‖:=(mul_le_mul_of_nonneg_right (le_max_left a _) (by positivity:(0:ℝ) ≤ (i:ℝ))).trans hz
 by_cases hy:0 ≤ z k
 · rw [abs_of_nonneg hy] at r; exact lamp_beam T P g x p hg u k z i h r hi
 rw [abs_of_nonpos (le_of_not_ge hy)] at r; have ht: ‖-z‖ ≤ d*(-z) k:=by simpa using r
 have he:= lamp_beam T P g x p hg u k (-z) i (by rwa [norm_neg]) ht hi; rw [norm_neg,charFun_neg,Complex.norm_conj] at he; exact he
omit p hg u
lemma lampsAlt {A:Type*}[NormedAddCommGroup A][InnerProductSpace ℝ A][FiniteDimensional ℝ A][MeasurableSpace A][BorelSpace A](p y w:A): ∃ f:ℂ→ℂ, Differentiable ℂ f ∧ ∀ t:ℝ,f t= mallet p (y+t • w) := by
 let X' (p:A)(z:ℂ):=comet y w z (-p); refine ⟨fun z=>2-X' p z-X' (-p) z,?_ ,fun t=> ?_⟩
 · unfold X' comet; fun_prop
 simp only [X',comet_at, neg_neg,mallet_color]; norm_num
lemma lotsAlt(p y:X)(S:Finset K): ∃ f:ℂ→ℂ, Differentiable ℂ f ∧ ∀ t:ℝ, f t=lamps g S (p+t • y):= by induction S using Finset.induction_on with
 | empty=> exact ⟨fun _=>1,differentiable_const _,fun t=>by simp [lamps]⟩
 | insert i S hi ih=> obtain ⟨f,w,v⟩:=ih; obtain ⟨q,h,u⟩:=lampsAlt ρ[i] p y; exact ⟨fun t=>q t*f t, h.mul w,fun t=> by dsimp only; rw [u,v,show lamps g (insert i S)=_ from (prod_insert (f:=(fun i:K=>mallet ρ[i])) hi)]; simp [Pi.mul_apply,lamps]⟩
include p u hg
lemma minted : Furnished (P.diagonal x) (lamps g (V)):=⟨fun i=> lampsF T P g i x p, lamps_cont .., lamps_p g (V), fun x y=> lotsAlt g x y _, flashed T P g x p hg u⟩
end YM.Spectral.Orbit.Prairie
#print axioms YM.Spectral.Orbit.Prairie.minted
