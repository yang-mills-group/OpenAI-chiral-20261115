import YM.CF.Tulip.Swatch
set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Tulip
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable (N:Side)
def leap (f:Cover)(r:Lattice.Order):=route 0 (2 • f) r
def slider (z:Cover)(o:Lattice.Order)(b a:SpinIdx)(c:ℂ)(x:Chin N) := ∑ i:Site N,panel (i,b) (i+wrap N z,a) ((wind i z*c) • (track x (node i) (leap z o)).1)
lemma leap_end (x:Site N)(z:Cover)(o:Lattice.Order): stop (node x) (leap z o)=node (x+wrap N z):=by
  let y:= lift (node x); let W:=leap z o; have hp:node x=wrap _ y:=(wrap_lift _).symm
  change stop (node x) W=_
  rw [hp, ← wrap_stop_cover, ← add_zero y,stop_trans, show stop (0:Cover) W=2 • z from route_end .., map_add, ← hp]; unfold node; rw [map_add,(assembly N).root_embed (wrap N z), Ratio.embed_wrap]; change _=(_+wrap _ (2 • z))+1; abel
lemma leap_dim (z:Cover)(o:Lattice.Order): (leap z o).length ≤ 8*Laurent.size z:=by
  rw [show 8*_=4*(2*Laurent.size z) by ring]; refine route_size _ _ _ _ (fun i=>?_)
  have he:(z i).natAbs ≤ Laurent.size z:= Finset.single_le_sum (f:=fun i : Axis=> (z i).natAbs) (fun i _=> Nat.zero_le _) (Finset.mem_univ i)
  simpa [Int.natAbs_mul] using Nat.mul_le_mul_left 2 he
lemma wheel {I Y:Type*} [DecidableEq I] [Fintype I][Fintype Y][DecidableEq Y] (f:I→Y)(p:Injective f)(g:I→Y)(A:I→ℝ)(R:ℝ)(h:∀ i,A i≤R)(hp:0≤R) (u:Y × Slot):
  ∑ v:Y×Slot,∑ i:I, reed (f i) (g i) (A i) u v ≤ Fintype.card Slot*R:=by
  rw [Finset.sum_comm]; have he (i): ∑ v:Y×Slot, reed (f i) (g i) (A i) u v=(if u.1=f i then Fintype.card Slot*A i else 0) := by
    rw [Fintype.sum_prod_type]; unfold reed; by_cases hx:u.1=f i; swap; simp [hx]
    rw [if_pos hx,Finset.sum_eq_single (g i)]; simp [hx]; intro b _ hb; simp [hb]; simp
  simp_rw [he]
  by_cases hx:∃ i,f i=u.1
  · obtain ⟨i,hi⟩:=hx; rw [Finset.sum_eq_single i]; rw [hi,if_pos rfl]; exact mul_le_mul_of_nonneg_left (h i) (by positivity); intro j _ hj; rw [if_neg (by intro hb; exact hj (p (hb.symm.trans hi.symm)))]; simp
  push Not at hx; simp only [if_neg (Ne.symm (hx _)), Finset.sum_const_zero]; positivity
lemma stride (z:Cover)(o:Lattice.Order)(b a:SpinIdx)(c:ℂ)(δ:ℝ)(e d:ℝ)(hp:0<e)(hs:e≤1)(hd:0≤d)(H: let p:=(leap z o).length;
    (Fintype.card Slot:ℝ)*(Real.exp (d*(p+1:ℕ)) * ((p+1:ℝ)*((1+e)^p)*‖c‖))≤δ): Solo d δ (slider N z o b a c) e:=by
  let p:= (leap z o).length
  let R(i:Site N):= traceP (node i) (leap z o); let s (i:Site N):=(i,b); let t (i:Site N):=(i+wrap N z,a)
  let V:=(p+1:ℝ)*(1+e)^p*‖c‖; have hv:0≤V:=by unfold V; positivity
  let T:= fun i:Site N=> reed (s i) (t i) V
  have hh(i:Site N): Suite (badge _) (bail N e) (bail N e) (R i) (T i) (fun x=> panel (s i) (t i) ((wind i z*c) • (track (x.val:Chin N) (node i) (leap z o)).1)):=by
    have ht:=gage e hp (s i) (t i) (leap z o) (leap_end N i z o) (wind i z*c) hs
    simp only [norm_mul, wind, fee_norm,one_mul] at ht; exact ht
  let K(i):=rent d (R i); let M:= Real.exp (d*(p+1:ℕ))
  have hm(i): K i ≤ M := Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast trace_k (node i) (leap z o)) hd)
  have hc i j k: K i * T i j k= reed (s i) (t i) (K i* V) j k:=by simp [reed,T,mul_ite]
  have hy:0≤M*V:=by unfold M; positivity
  have hk(i): K i*V≤ M*V:=mul_le_mul_of_nonneg_right (hm i) hv; change ↑(Fintype.card Slot)*(M*V)≤ δ at H
  refine Crown.absorb R _ T d ((mul_nonneg (by positivity) hy).trans H) _ hh (fun _=> rfl) (fun i=>?_) (fun i=>?_)
  · change ∑ _,∑ _, K _* _ ≤ _; simp_rw [hc]; exact (wheel s (fun _ _ h=> (congr_arg Prod.fst h)) t _ _ hk hy i).trans H
  change ∑ j:Single N, ∑ i₁:Site N,K i₁*T i₁ j i ≤ _
  have hx (j:Single N)(y:Site N): K y*T y j i= reed (t y) (s y) (K y*V) i j:=by rw [hc]; unfold reed; simp only [and_comm]
  simp_rw [hx]; exact (wheel t (fun _ _ h=>add_right_cancel (congr_arg Prod.fst h)) s _ _ hk hy i).trans H
end YM.CF.Tulip
