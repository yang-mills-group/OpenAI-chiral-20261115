import YM.CF.BPress.Wealth.Groves
import YM.CF.BPress.Pine.Boss
/-! eq:B-Apri and PL reuse. Halo 8 on mask reads. Incl pi tags all auth bits. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Spark
open Function NormedSpace Finset Filter Lattice Branch Push.AbsoluteSums Grid RG Ledger Pine --
open scoped Topology BigOperators Classical
variable {s : Side}
def prec (B:ℕ):ℕ:= 17^4*(B+B+1)^4
variable (B:ℕ)
def dorm0 (X:Support s) := halo B (coverNumber_realized B X).choose
def dorm (X:Support s) := halo 8 (dorm0 B X)
lemma dorm_sub (X:Support s): X ⊆ dorm B X:= (coverNumber_realized B X).choose_spec.1.1.trans (halo_subset ..)
lemma dorm_hit (X:Support s)(p:X.Nonempty): Grove (field 4 s) (dorm B X):=by
 obtain ⟨i,u⟩:=p; have ht:= (coverNumber_realized B X).choose_spec.1; exact Wealth.halo_g 8 (Branch.trunk (ht.1 u) (fun x v=> ht.2 i (ht.1 u) x v))
lemma wake {X Y:Support s} (t:X⊆Y): inspected X⊆ dorm B Y:= by intro i p; obtain ⟨z,t',h⟩:= Extra.Iteration.Shapes.inspect_dist X p; refine halo_spec.mpr ⟨z, (coverNumber_realized B Y).choose_spec.1.1 (t t'),(separation_comm ..).le.trans h⟩
lemma dorm_n (X:Support s): (dorm B X).card ≤ prec B * coverNumber B X:=by refine (Corona.halo_size ..).trans ((Nat.mul_le_mul_right (17^4) (Corona.halo_size ..)).trans ?_); rw [(coverNumber_realized B X).choose_spec.2]; unfold prec; exact Eq.le (by ring)
def δPort(B:ℕ):ℝ:= 1/(2*(prec B:ℝ))
lemma beam_x : 0<(prec B:ℝ):=by unfold prec; positivity
lemma beam_p : 0<δPort B:=by have hp:=beam_x B; unfold δPort; positivity
lemma honorP (B:ℕ)(A: Support s) (w:ℝ)(p:0≤w) : rent (δPort B) (dorm B A)*w ≤ Real.exp (-(1:ℝ)/2*(coverNumber B A:ℝ))* (Real.exp (coverNumber B A)*w):=by
 rw [←mul_assoc,←Real.exp_add]; apply mul_le_mul_of_nonneg_right _ p; apply Real.exp_monotone; have he: _ :=Nat.cast_le (α:=ℝ).mpr (dorm_n B A); rw [Nat.cast_mul] at he; calc -- placeholder tune
    _ ≤ _ := mul_le_mul_of_nonneg_left he (beam_p B).le
    _ = _ := by have hn:=beam_x B; unfold δPort; field_simp; ring
def τPort:=∑' i:ℕ, Real.exp (-(1:ℝ)/2*(i:ℝ))*(((i:ℝ)+1)^4)
abbrev αPort(B:ℕ):ℝ:=( (2* prec B :ℕ) +1 : ℕ) -- cast tune
abbrev aPort(B:ℕ)(x:ℝ):= αPort B^4*x*τPort
lemma τPort_pos:0 < τPort:=by
 have ht: Summable (fun i:ℕ=> Real.exp (-(1:ℝ)/2*(i:ℝ))*(((i:ℝ)+1)^4)):=by simpa only [one_mul] using fund_hit 1 1 zero_lt_one zero_le_one
 exact ht.tsum_pos (fun i=>by positivity) 0 (by norm_num)
lemma βPol: PL (fun x=> ((δPort (Pressure.radiusB x))⁻¹))∧ PL (fun x=> αPort (Pressure.radiusB x)):=by
 have h:PL (fun x=>(Pressure.radiusB x:ℝ)):= PL.scale.mono (Eventually.of_forall fun x=>by rw [abs_of_nonneg (by positivity : (0:ℝ)≤ (Pressure.radiusB x:ℝ)),abs_of_nonneg (zero_le_one.trans (lscale_one _))]; unfold lscale; linarith)
 have hp:PL (fun x=>(prec (Pressure.radiusB x):ℝ)):=by unfold prec; push_cast; exact (PL.const _).mul (((h.add h).add (PL.const _)).pow _)
 have ht:PL (fun x=>2*(prec (Pressure.radiusB x):ℝ)):= (PL.const 2).mul hp
 unfold δPort αPort; simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat, Nat.cast_one,one_div,inv_inv]; exact ⟨ht,ht.add (PL.const 1)⟩
lemma scope (B:ℕ)(x:Site s)(t:ℕ): ((halo (prec B*t) {x}).card:ℝ)≤αPort B^4*((t:ℝ)+1)^4:= by apply (Nat.cast_le.mpr (Wealth.halo_size x _)).trans; rw [←mul_pow]; exact_mod_cast (show (2*(prec B*t)+1)^4≤((2*prec B+1)*(t+1))^4 from pow_le_pow_left' (by rw [add_mul  (2*prec B) 1, mul_add, mul_assoc 2,one_mul]; omega) 4)
end YM.CF.BPress.Spark
