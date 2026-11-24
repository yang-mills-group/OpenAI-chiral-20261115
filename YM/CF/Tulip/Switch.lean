import YM.CF.Tulip.Dew
set_option autoImplicit false
noncomputable section
namespace YM.CF.Tulip
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir WilsonFrame
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {N:Side}
def stepper (v:Axis)(a:SpinIdx)(x:Chin N):Op (Single N):= ∑ i:Site N,panel (i,a) ((i+step v:Site N),a) ((seam (anticut N) i v) • (track x (node i) [posDir v,posDir v]).1)
def trackM (v:Axis)(x:Chin N):Op (Single N):=∑ a:SpinIdx, stepper v a x
lemma step_live (v:Axis)(a:SpinIdx): Lively (fun (_:Unit) N x=> @stepper N v a x):=by
  let W:ℝ:=(2+1)*(1+1)^ (2:ℕ); have hw:0≤W:=by norm_num [W]
  refine certify (show 0<(1:ℝ) by norm_num) (show 0<(1:ℝ) by norm_num) (v:=0) (r:=Fintype.card Slot*(Real.exp 3 *W)) (fun i N hp=>?_)
  let f(u:Site N):= (u,a); let g(u:Site N):=(u+step v,a); let B:Walk:=[posDir v,posDir v]; let R (x:Site N):= traceP (node x) B
  let C (x):= reed (f x) (g x) W
  have hx(i:Site N) : Suite (badge _) (bail N 1) (bail N 1) (R i) (C i) (fun x=> panel (i,a) ((i+step v:Site N),a) ((seam (anticut N) i v) • (track x.val (node i) B).1)) :=by
    have he:=gage 1 zero_lt_one (f i) (g i) B (after i v|>.symm) (seam (anticut N) i v) le_rfl
    dsimp only at he; rw [seam_norm,mul_one,show B.length= (2:ℕ) from rfl, Nat.cast_ofNat] at he; exact he
  let K:=fun i:Site N=> rent 1 (R i)*W
  have hm(i:Site N): K i≤Real.exp 3 *W:=by
    unfold K; apply mul_le_mul_of_nonneg_right _ hw; unfold rent; apply Real.exp_monotone; rw [one_mul]; exact_mod_cast (show (R i).card≤3 from trace_k ..)
  have hh(i j k): rent 1 (R i)*C i j k= reed (f i) (g i) (K i) j k := by simp [C,K,reed, mul_ite]
  refine Crown.absorb R _ C _ (by positivity) _ hx (fun _=>rfl) (fun i=>?_) (fun i=>?_)
  · simp_rw [hh]; exact wheel _ (fun _ _ e=> congr_arg Prod.fst e) _ _ _ hm (by positivity) _
  simp_rw [hh]
  have he (j) (x y:Single N): reed (f j) (g j) (K j) x y=reed (g j) (f j) (K j) y x:=by simp only [reed,and_comm]
  simp_rw [he]; exact wheel _ (fun _ _ h=>add_right_cancel (congr_arg Prod.fst h)) _ _ _ hm (by positivity) _
lemma step_profile (U:Bkg (More N))(i:Axis): trackM i (profile U)=love N ((frame matter (links U) (anticut N)).T i):=by
  have h(x:Site N): (track (profile U) (node x) [posDir i,posDir i]).1=(matter (links U (x,i))).val:=by rw [track_pr]; simp only [travel,mul_one,Step.pos_read,Step.vec_pos]; rfl
  ext ⟨⟨x,a⟩,u⟩ ⟨⟨y,b⟩,t⟩
  rw [trackM, Matrix.sum_apply]; change _=shift matter (links U) (anticut N) i (x,a,u) (y,b,t)
  rw [Finset.sum_eq_single a]; swap
  · intro d _ hd; simp [stepper,panel,Matrix.sum_apply, Ne.symm hd]
  swap; simp
  simp only [stepper,Matrix.sum_apply]; rw [Finset.sum_eq_single x]; swap
  · intro y _ hg; simp [panel,Ne.symm hg]
  swap; simp
  simp only [panel,Matrix.of_apply,shift, jump_apply,hop,color, Matrix.smul_apply,smul_eq_mul,h]; by_cases he:x+step i=y <;> by_cases h:b=a <;> simp [Equiv.coe_fn_mk,advance,he,h,eq_comm, Matrix.one_apply] <;> grind

def rock (i:Op SpinIdx)(x:Chin N) : Op (Single N):=love N (spin N Slot i)
lemma granite (b a:SpinIdx)(c:ℂ) (x:Chin N): slider N 0 1 b a c x= ∑ y:Site N, panel (y,b) (y,a) (c • 1):=by
  unfold slider; apply sum_congr rfl; intro i _
  have hv:leap 0 1=[]:=by unfold leap; simp
  have ht: Rush.wind i 0=1:=by
    have he:=freq_advance (0:Site N) i 0; simp only [map_zero,add_zero,mode_zero,mul_one] at he
    have hh: frequency (0:Site N) i≠0:=by intro h; simpa [h] using frequency_unit 0 i
    exact mul_right_cancel₀ hh (by rw [one_mul]; exact he)
  rw [ht,hv]; simp [track]
lemma rock_live (G:Op SpinIdx): Lively (fun (_:Unit) N=> @rock N G) :=by
  have hx (i a: SpinIdx): Lively (fun (_:Unit) N=>slider N 0 1 i a (G i a)):=by
    have ht:leap 0 1=[]:= by unfold leap; simp
    apply certify one_pos one_pos (v:=0) (a:=1) (e:=1) (r:= Fintype.card Slot*(Real.exp 1 *‖G i a‖)); intro _ N hp
    exact stride N _ _ _ _ _ _ _ _ zero_lt_one le_rfl zero_le_one (by simp [ht])
  have he:= allsum Finset.univ _ (fun b _=> allsum Finset.univ _ (fun i _=> hx b i))
  convert he using 1
  ext _ N x ⟨⟨y,a⟩,u⟩ ⟨⟨z,b⟩,v⟩: 5
  change spin N Slot G (y,a,u) (z,b,v)=(∑ i:SpinIdx,∑ j:SpinIdx, slider N 0 1 i j (G i j) x) _ _
  simp only [granite, Matrix.sum_apply, spin,jump_apply]; by_cases h:y=z <;> simp [panel,h,and_left_comm,and_assoc,ite_and] <;> grind
end YM.CF.Tulip
