import YM.SU5.Registration.Reconstruction
import YM.SU5.SatinWard.Resolution.SageTicket
import YM.SU5.Assay.SandCup
set_option maxHeartbeats 180000
noncomputable section
namespace YM.SatinRegistration.LimeWave
open Filter Function MeasureTheory Spectral Set
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace ComplexOrder Classical
open OS OS.Semigroup SatinEdge.RealSheet Boundary Probe Multiplier Roy CF.Buffered.Afterglow.Hierarchy.Seld
open Grading UnpadTicket
variable {H:Hilbert}{i:Axis}(S: OS.Semigroup H i) (ℓ:ℕ→ℝ)(K:ℝ→ℝ→H.Op)(A:ℕ→ℝ→ℝ→H.Op)
/-! Keep prices all heights together after buying pads greater than the width-currency. Frame calibrated to any basis variant/op/family. ℓ here such that 2ℓ used for both fields. -/
structure Post (z:ℕ):Prop where
 credits (v:ℕ)(h:z≤v) : S.Credits (ℓ v) (A v)
 lim (l r:ℝ)(u:0<l)(v:0<r): Tendsto (fun v=>A v l r) atTop (𝓝 (K l r))
 pos (v:ℕ):0<ℓ v
 zero : Tendsto ℓ atTop (𝓝 0)
 threshold (v:ℕ)(h:z≤v): ℓ v≤ (1/2:ℝ)^(v-z)*ℓ z
 funds : ∃ D C:ℝ,1 ≤ D∧0 ≤ C∧Climbed ℓ z A D C
#check @Post
abbrev montage (v:ℕ):= A v (2*ℓ v) (2*ℓ v)
abbrev funded (T:H.Op) (x:ℝ≥0) := S.E x*T*S.E x
abbrev image (x:ℝ≥0):= K x x
variable {K S ℓ A}{z:ℕ}(W:Post S ℓ K A z)
local notation "B"=> montage ℓ A
local notation "Q★"=> funded S
local notation "U★" => image K
include W
lemma Post.recallQ {v:ℕ}(h:z≤v)(l r:ℝ)(w:0≤l)(p:0≤r): A v (2*ℓ v+l) (2*ℓ v+r)= S.sand (B v) l r:=by
 have x:ℓ v < 2*ℓ v:=by linarith [W.pos v]
 unfold montage; rw [W.credits v h x x (le_add_of_nonneg_right w) (le_add_of_nonneg_right p),add_sub_cancel_left,add_sub_cancel_left]
lemma Post.leaned {v:ℕ}(h:z≤v) (t:ℝ≥0): Q★ (B v) t= A v (2*ℓ v+t) (2*ℓ v+t):=by rw [W.recallQ h (↑t) (↑t) t.coe_nonneg t.coe_nonneg]; simp [wax, sand, funded]
lemma Post.onlySlide (t:ℝ≥0)(u:0<t): Tendsto (fun v=> Q★ (B v) t) atTop (𝓝 (U★ t)):=by
 have h:Tendsto (fun v:ℕ=>2*ℓ v+(t:ℝ)) atTop (𝓝 (t:ℝ)):=by simpa only [mul_zero,zero_add] using Tendsto.add_const _ (W.zero.const_mul (2:ℝ))
 refine (Credits.norm_on W.zero ( (eventually_ge_atTop z).mono (fun v=> W.credits v)) (fun _ u _ v=> W.lim _ _ u v) (show (0:ℝ)<t from u) (show (0:ℝ)<t from u) h h).congr' ((eventually_ge_atTop z).mono (fun v u=> (W.leaned u t).symm))
lemma Post.creditTurn : S.Credits 0 K:=Credits.paid W.zero ((eventually_ge_atTop z).mono (fun v=>W.credits v)) (fun _ x _ y=> W.lim _ _ x y)
lemma Post.soundQ : Sound S (image K):=by
 intro t e r; unfold image
 have h: (t:ℝ) ≤ ((t+r:ℝ≥0):ℝ):=by simpa using r.property
 rw [W.creditTurn (show (0:ℝ)<t from e) (show (0:ℝ)<t from e) h h]; simp only [sand,NNReal.coe_add,add_sub_cancel_left,wax,Real.toNNReal_coe] -- variable field names check
lemma Post.fundsAll : ∃ k C, 0≤ C ∧ PadBound (U★) k C ∧ ∀ v, z ≤ v → PadBound (Q★ (B v)) k C:= by
 obtain ⟨D,c,d,p,f⟩:= W.funds; obtain ⟨k,F,h,T⟩:= beaming d (W.pos _) W.zero W.threshold; have hv(v)(u:z≤v) : PadBound (Q★ (B v)) k (c* F):=by
    intro t x y; rw [W.leaned u t]; obtain ⟨s,r,l,y⟩:= T t x y; have e:ℓ (min s v)≤2*ℓ v+t:=by rcases le_total s v with w|w <;> simp only [min_eq_left, min_eq_right,w] <;> linarith [ t.property,W.pos v] -- same shadow
    calc
        _ ≤ (t:ℝ)^k * (c* D^s):= mul_le_mul_of_nonneg_left (f s v r u _ _ e e) (by positivity)
        _ = c*((t:ℝ)^k*D^s):=by ring
        _ ≤ _:= mul_le_mul_of_nonneg_left y p
 refine ⟨k,c*F,mul_nonneg p h.le,fun t x y=> le_of_tendsto ((W.onlySlide t x).norm.const_mul ((t:ℝ)^k)) ((eventually_ge_atTop z).mono fun v u=> hv v u t x y),hv⟩
#print axioms Post.fundsAll
lemma Post.payQ : PadPaid (U★):=let ⟨k,c,h,p,_⟩:=W.fundsAll; ⟨k,c,h,p⟩
omit W
variable (S)
lemma warmMeter (X:H.Op) : Sound S (funded S X):= by intro u p v; unfold funded; nth_rw 1 [add_comm]; rw [S.time,S.time]; change S.E v * S.E u * X * (S.E u * S.E v)=_; rw [mul_assoc (S.E v), ←mul_assoc _ _ (S.E v), mul_assoc (S.E v) (S.E u * X)]
lemma warmingIs (T:H.Op) : rawBlocks S (funded S T)= (bands S).dissect T:=by
 unfold rawBlocks dissect; congr 1; ext1 m; funext n; change rewarm S 1 m * (S.E 1*T*S.E 1)* rewarm S 1 n= cell S m*T*cell S n; let p i : rewarm S 1 i * S.E 1 = cell S i:= ((rewarm_reads S 1 i).jointly (costT S 1)).eq.trans (forward_cell S 1 i); simp only [mul_assoc,forward_cell]; rw [←mul_assoc,p]
variable {S}
include W
lemma Post.blocksPrice : let B':=(bands S); ∃ k C, 0≤C ∧ PowerPrice S (rawBlocks S U★) k C ∧ ∀ v,z ≤ v→ PowerPrice S (B'.dissect (B v)) k C:=by
 intro B'; obtain ⟨k,c,h₀,h,w⟩:= W.fundsAll; refine ⟨k,_,mul_nonneg (mul_nonneg (Real.exp_nonneg _) h₀) (Real.exp_nonneg _), cold_price S _ h W.soundQ,fun v h=>?_⟩
 unfold B'; rw [←warmingIs]; exact cold_price S _ (w _ h) (warmMeter S _)
lemma Post.tendsto_blocks (m n:ℕ): Tendsto (fun v=>((bands S).dissect (B v)).op m n) atTop (𝓝 ((rawBlocks S U★).op m n)):=by simp_rw [←warmingIs]; exact ((W.onlySlide 1 zero_lt_one).const_mul (rewarm S 1 m)).mul_const (rewarm S 1 n)
lemma Post.warmth (f:Test4){x:radial S}{U:ℕ→ radial S}(p:(bands S).Approaches atTop U x) : (bands S).Approaches atTop (fun v=> warm S (B v) f (U v)) (field S (image K) W.soundQ W.payQ f x):=by
 obtain ⟨k,c,A,pB,t⟩:= W.blocksPrice; refine enact_approach S (rawBlocks S _) (cold_paid S U★ W.payQ W.soundQ) atTop (fun i=> (bands S).dissect (B i)) (fun i=> dissect_paid S _) A pB ((eventually_ge_atTop z).mono (fun i=> t i)) (fun m n x=>?_) f p
 -- shadow A accidental
 exact (((ContinuousLinearMap.apply ℂ H) x).continuous.tendsto _).comp (W.tendsto_blocks m n)
#print axioms Post.warmth
end YM.SatinRegistration.LimeWave
