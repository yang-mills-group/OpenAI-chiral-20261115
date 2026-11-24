import YM.SU5.FiniteGaugeData.SalonG.Peppermint
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
namespace SalonG
open Nacre Heat Charm Chrono Journey
variable {K:Calibration}{m:Side}{N:Side}(a:Axis)
variable (d n:ℕ)(S T:Finset Cover)
local notation "N'"=> K.c m
local notation "H"=> proceed K n d
local notation "V"=> Ran (T:=T) (d:=d) K
local notation "η"=> K.ℓ
variable (x f:W K)
-- use analytic square slope estimates (powers go back to BASE later)
abbrev Jacket := Fold K a 0 (Train K a d f n) (Train K a d f n)
abbrev blanket := refract a 0 (proceed_set K a d S n)∪proceed_set K a d S n
local notation "Q"=> blanket (K:=K) a d n S
lemma blanket_flight (p:Locator K f S) : Locator K (Jacket a d n f) (blanket a d n (K:=K) S):= helve_loc a (train_loc K a d n _ p) (train_loc K a d n _ p)
lemma blanket_p (t:Studio a 0 (yard K d) K.ℓ S): Studio a (-(proceed K n d:ℤ)) (proceed K n d) K.ℓ (blanket a d n (K:=K) S):=seal_twice K a (proceed_geo K a d n t) -- rewrite
lemma blanket_on (p:Studio a 0 (yard K d) K.ℓ S)(u:2*(proceed K n d) ≤ N.val): later (proceed K n d) N (refract a (proceed K n d) (blanket (K:=K) a d n S)) a K.ℓ:= (blanket_p a d n S p).earlier (by omega)
abbrev CarrierF := Jacket a d n f * fire K a (proceed K n d) (Jacket a d n f)
abbrev terrace := Q ∪ refract a (proceed K n d) Q
lemma vigilant (p:Locator K f S): Locator K (CarrierF a d n f) (terrace (K:=K) a d n S):= locate_join K _ (locate_sub _ (blanket_flight _ _ _ _ _ p) subset_union_left) (locate_sub _ (locate_cold K Q a _ (blanket_flight _ _ _ _ _ p)) subset_union_right)
variable (K m)
lemma train_tang (i:Axis)(q:i ≠ a): Cardboard K m i 0 (wall S) (proceed_set K a d S n):=by
 induction n with
 | zero=> intro x h; rw [proceed_set] at h; exact (notMem_empty x h).elim
 | succ n ih=> have he:=grace K m i S; exact (he.conjU (he.cross q.symm _)).conjU (ih.deduct q.symm _)
lemma permitV (i:Axis)(q:i ≠ a): Cardboard K m i 0 (wall S) (terrace a d n S (K:=K)):=by have hx:=train_tang K m a d n S i q; have hp:= (hx.cross (a:=a) q.symm 0).conjU hx; exact hp.conjU (hp.cross q.symm _)
lemma diligent (C:ℝ)(p:RealWidth K f m C): RealWidth K (CarrierF a d n f) m (C^(4*n)):=by
 have he:= p.camp a d n; have ht:=(he.reflected a 0).mule he; have hu:=ht.mule (ht.reflected a (proceed K n d)); rw [show C^(4*n)=C^n * C^n * (C^n*C^n) from ?_]; exact hu
 rw [show 4*n=n+n+(n+n) from by omega]; simp only [pow_add]

local notation "ν"=> Ran K (d:=d) (T:=T)
local notation "R" k:max=> openQ K a d k f x
variable {K m S}
variable {L:Loom (K.c m)}{X:W K→ₗ[ℂ]ℂ}{D B:ℝ}(E:Equity K m L X D)
local notation "Ω" k:max=> Fold K a 0 (R k) (R k)
include E
variable (t:Ahead a 0 K.ℓ T)(p:Locator K f S) (u:Locator K x T) (r:Studio a 0 (yard K d) K.ℓ S)(F:PaidSpan K m d n)
   (g:endurance K (Ran K (d:=d) (T:=T)) ≤ (K.c m).val)
include t p u r F g
lemma onboard (j:ℕ)(q:j≤ n): role K m a 0 (openQ K a d j f x):=by
 apply role_loc K m a 0 (open_loc K a d j _ _ p u); apply (go_roll K m a F t r ?_ q).later (by omega); unfold endurance canal at g; omega

lemma Equity.lastCost (w:RealWidth K x m B) : ‖X (Fold K a 0 (openQ K a d n f x) (openQ K a d n f x))‖^2 ≤ ‖X (CarrierF a d n f)‖* (TellerC (Ran K (d:=d) (T:=T)) K D*((B*B)*(B*B))) := by
 let y:= Train K a d f n; let x':= wagon K a d n x; let R₀:= Fold K a 0 x' x'
 have he : Ω n= Jacket a d n f * R₀:= by
    change fire K a 0 (y*x')*(y*x')= _; rw [ice_join]; exact Commute.mul_mul_mul_comm (b:= fire K a 0 x') (commW _ _ _) _ _ -- first ice_join.
 have ht := E.separated K m a ↑(proceed K n d) X (proceedLevel K d n) (blanket_flight a d n S f p) (helve_loc a (loc_tic K T a (d*(n+2):ℕ) u) (loc_tic K T a (d*(n+2):ℕ) u)) (blanket_on a d n S r F.lower) (rear_ahead K m a F t (by unfold endurance canal at g; omega))
 have hp' := E.convoy a F t u w g; dsimp only at hp'
 rw [he]; exact ht.trans (mul_le_mul_of_nonneg_left hp' (norm_nonneg _))
lemma Equity.travel (w:RealWidth K x m B){C:ℝ}(z: ‖X (CarrierF a d n f)‖ ≤ C):
    (n:ℝ) * ((X (Ω 1)).re - (X (Ω 0)).re) ≤ C*(TellerC (Ran K (d:=d) (T:=T)) K D*(B*B*(B*B)))+1:= by
 have he:= E.slope K m a X d n f x (fun j=> onboard a d n T x f E t p u r F g j); have ht:= C |> (fun _=>Equity.lastCost a d n T _ _ E t p u r F g w); let z':= TellerC V K D *((B*B)*(B*B)); have hv:0 ≤ z':= mul_nonneg (Real.exp_pos _).le (mul_self_nonneg _); have hp:= mul_le_mul_of_nonneg_right z hv; have h:= ht.trans hp; have hw:‖X (Ω n)‖ ≤ C*z'+1:=by nlinarith
 exact he.trans ((Complex.re_le_norm _).trans hw)
#print axioms Equity.travel
omit E t p u r F g

-- price envelope (not the ONLY price that could be used). no reliance on TellerC previously. all periods. Budget after 3 spatial repetitions only
private lemma goldi {x y:ℕ} (p:0<y) (t:y ≤ x): ∃ k:ℕ, 2^k*y ≤ x ∧ x ≤ 2*(2^k)*y := by
  have he : x < 2^x*y:= lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.le_mul_of_pos_right _ p)
  let P(k:ℕ):= x ≤ 2*(2^k)*y
  have ht: ∃ k,P k:=⟨x,by unfold P; linarith⟩
  refine ⟨Nat.find ht,?_,Nat.find_spec ht⟩
  generalize e:Nat.find ht=k
  cases k with
  | zero=> simpa using t
  | succ k=> have h:=Nat.find_min ht (by omega : k < Nat.find ht); change ¬ x ≤ 2*2^k*y at h; rw [pow_succ']; omega
variable {X':Mark (K.c m)→ℂ}
abbrev booth (K:Calibration)(S:Finset Cover):=2*wall S+addgap K
abbrev heightL (K:Calibration)(S:Finset Cover)(d:ℕ):ℕ:= (2*booth K S)^3*(4*yard K d)
lemma weighJ {d p n:ℕ}(h:(K.c m).val ≤ p*(2*booth K S))(e:PaidSpan K m d n)(t:n≠0): (m.val)^4≤ p^3*(heightL K S d*n):=by
 let q:= 2*booth K S; let Q1:= yard K d
 have hp:= (side_lower K (m:=m)).trans h; have hc:= (side_lower K (m:=m)).trans e.upper; unfold proceed at hc -- he
 have ht: Q1≤Q1*n:=Nat.le_mul_of_pos_right Q1 (by omega)
 have hu: m.val≤ 4*yard K d*n:= hc.trans (by change 2*(Q1*n)+2*Q1≤ _*Q1*n; nlinarith)
 rw [pow_succ m.val 3]; refine le_trans (Nat.mul_le_mul (Nat.pow_le_pow_left hp 3) hu) ?_; unfold heightL; exact le_of_eq (by ring)
include p F in
lemma Equity.coachD {u':Mark (K.c m)→ℂ} (d0:D=D) -- binder
    (V':Metered K m L u' D)(h':booth K S ≤ (K.c m).val)(z:n≠0) :
    ‖u' ((CarrierF a d n f).val m)‖ ≤ Real.exp (D * (heightL K S d:ℝ)*n)*cash L ((CarrierF a d n f).val m):= by
 let w:= CarrierF a d n f; let i:=booth K S; obtain ⟨k,ht,e⟩:= goldi (lt_of_lt_of_le addgap_pos (show addgap K≤booth K S from by unfold booth; omega)) h'; let J:= (2^k)^3
 have j(v:Axis)(q:v∈univ.erase a) : rest K m (region (terrace (K:=K) a d n S) (K.c m)) v (2*wall S):= (permitV K m a d n S v (mem_erase.mp q).1).ledger
 obtain ⟨y,T',b,V''⟩:= V'.brush k ht (univ.erase a) j ((vigilant a d n S f p).support m); have c: (univ.erase a).card=3:= by rw [card_erase_of_mem (mem_univ _), card_fin]
 have hz:Metered.Flare J (w.val m) y u' L:= by rw [c] at V''; exact V''
 have hw := weighJ (p:=2^k) (m:=m) (d:=d) (S:=S) (show _ from e.trans (le_of_eq (by ring))) F z; have h':(m.val:ℝ)^4≤ (J:ℕ)*(heightL K S d:ℝ)*n:=by push_cast; change _≤ _; rw [mul_assoc]; exact_mod_cast hw
 apply (pow_le_pow_iff_left₀ (norm_nonneg _) (mul_nonneg (Real.exp_pos _).le (cash_nonneg ..)) (n:=J) (by unfold J; positivity)).1
 refine hz.value.trans ((V'.tally y b.env).trans ?_); rw [mul_pow, ← Real.exp_nat_mul]; refine mul_le_mul (Real.exp_le_exp_of_le ?_) hz.cost (cash_nonneg ..) (Real.exp_pos _).le; exact le_trans (mul_le_mul_of_nonneg_left h' V'.positive) (le_of_eq (by ring))

abbrev drift (K:Calibration)(S:Finset Cover)(d:ℕ)(D:ℝ):= Real.exp (- (D * (heightL K S d:ℝ)))
include E F p
lemma Equity.chariot (z:n≠ 0)(w:booth K S ≤ (K.c m).val)(h':RealWidth K f m (drift K S d D)): ‖X (CarrierF a d n f)‖≤ 1:=by
 let δ:= (D * (heightL K S d:ℝ)); obtain ⟨u',g,v⟩:= E.pays; rw [← v]; have he:= Equity.coachD a d n f p F (u':=u') (D:=D) rfl g w z
 have ht:0 ≤ δ:= mul_nonneg g.positive (Nat.cast_nonneg' _); refine he.trans (le_trans (mul_le_mul_of_nonneg_left (diligent K m a d n f _ h'|>.cashW) (Real.exp_pos _).le) ?_); unfold drift; rw [←Real.exp_nat_mul,← Real.exp_add,Real.exp_le_one_iff]; change δ*_+((4*n:ℕ):ℝ)*(-δ) ≤ 0; rw [Nat.cast_mul, Nat.cast_ofNat]; nlinarith
#print axioms Equity.chariot
end SalonG
end YM.CF.Buffered.Afterglow.Hierarchy
