import YM.CF.Peaks.Yarn
set_option autoImplicit false
noncomputable section
namespace YM.CF.Peaks
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator Kronecker
attribute [local instance] opCStarAlgebra
variable {N P:Side}(G: Ratio N P)
variable (u v:Bool)
def runD(L:Side)(r t:St L)(k:Cover)(o:Lattice.Order):Walk:=route 0 (2 • (L.val • k)+traceU v t-traceU u r) o
def drag (r t:St G.count)(k:Cover)(c:ℂ)(o:Lattice.Order)(x:Coil N P) := ∑ i:Site N, panel (i,r) (i+wrap N k,t) ((Rush.wind i k*c) • (track x.1 (touch G u (i,r)) (runD u v G.count r t k o)).1)
lemma worn (ho:Odd G.count.val)(r t:St G.count)(k:Cover)(o:Lattice.Order)(x:Site N): stop (touch G u (x,r)) (runD u v G.count r t k o)=touch G v (x+wrap N k,t):=by
  rw [right_to,runD,route_end,turnMap G v ho,turnMap G u ho]; have hh: portico G (x+wrap N k,t)=portico G (x,r)+wrap _ (2 • (G.count.val • k)):=by
    change (ratio G).embed ((assembly N).root (x+wrap N k)+1)= (ratio G).embed (_+1)+ _
    rw [map_add,add_right_comm ((assembly N).root x),← Ratio.root_embed,map_add,Ratio.root_embed,(assembly N).root_embed (wrap N k),(assembly N).embed_wrap,Ratio.root_embed, Ratio.root_embed,Ratio.embed_wrap]; change _+wrap _ (G.count.val • (2 • k))=_; rw [smul_comm G.count.val (2:ℕ)]
  rw [hh]; simp only [map_add,map_sub]; abel
lemma run_len (L:Side)(r t:St L)(k:Cover)(o:Lattice.Order): (runD u v L r t k o).length ≤ (16*L.val+8*L.val*size k) :=by
  let D (v:Bool)(r:St L):= traceU v r
  apply le_trans (route_size _ _ _ (4*L.val+2*L.val*size k) ?_) (le_of_eq (by ring))
  intro i
  have he (v:Bool)(r:St L) : ((traceU v r) i).natAbs ≤2*L.val:=by
    cases v
    · simp [traceU]
    obtain ⟨h,g⟩:= lift_centers r.1 i; simp [traceU]; omega
  have hh:(k i).natAbs≤ size k:= Finset.single_le_sum (f:=fun j=> (k j).natAbs) (fun _ _=>Nat.zero_le _) (mem_univ i)
  have hx:( (2:ℤ)* (L.val*(k i))).natAbs≤2*L.val*size k:=by simp only [Int.natAbs_mul,Int.natAbs_natCast]; exact le_trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hh)) (le_of_eq (by rw [← Nat.mul_assoc]; rfl))
  simp only [Pi.add_apply,Pi.sub_apply,Pi.zero_apply,Pi.smul_apply,nsmul_eq_mul,sub_zero,Nat.cast_ofNat]
  apply (Int.natAbs_sub_le ..).trans; exact (Nat.add_le_add ((Int.natAbs_add_le ..).trans (Nat.add_le_add hx (he v t))) (he u r)).trans (by omega)
lemma swipe (ho:Odd G.count.val)(r t:St G.count)(z: Cover)(c:ℂ)(o:Lattice.Order)(e d δ:ℝ)(hh:0<e)(he:e≤1)(hd:0≤d)
    (H: let ℓ:=(runD u v G.count r t z o).length; ↑(Fintype.card Slot)*(Real.exp (d*(((ℓ+16*G.count.val+3:ℕ):ℝ))) *(((ℓ+1:ℝ)*(1+e)^ℓ)*‖c‖))≤δ):
    Crown (badge _) (parcel G u e) (parcel G v e) d δ (fun x=> drag G u v r t z c o x.val):=by
  let f(x:Site N):=(x,r); let g(x:Site N):=(x+wrap N z,t); let p:=runD u v G.count r t z o; let ℓ:=p.length; let W:=( (ℓ+1:ℝ)*(1+e)^ℓ) * ‖c‖; let R(x):=conduit G u v (f x) (g x) p; let T(x):=reed (f x) (g x) W
  let M:=Real.exp (d*(((ℓ+16*G.count.val+3:ℕ):ℝ)))
  have hW :0≤W:=by unfold W; positivity
  have hP:0≤ M*W:=mul_nonneg (Real.exp_pos _).le hW; change ↑(Fintype.card Slot)*(M*W)≤δ at H
  have ht(x): rent d (R x)≤M:=Real.exp_monotone (mul_le_mul_of_nonneg_left (by exact_mod_cast conduits G u v (f x) (g x) p) hd)
  have hy (x:Site N): Suite (badge _) (parcel G u e) (parcel G v e) (R x) (T x) (fun i=>panel (x,r) (x+wrap N z,t) ((Rush.wind x z*c) • (track i.val.1 (touch G u (x,r)) p).1)):=by
    have hw:= cord G u v (p:=p) ho (f x) (g x) (Rush.wind x z*c) e hh he (worn G u v ho r t z o x)
    dsimp only at hw; rw [norm_mul,Rush.wind,fee_norm,one_mul] at hw; exact hw
  let K(x):=rent d (R x)*W; have hk(x): K x≤M*W:=mul_le_mul_of_nonneg_right (ht x) hW
  have h1(x i j): rent d (R x)*T x i j=reed (f x) (g x) (K x) i j:=by simp only [K,T,reed,mul_ite,mul_zero]
  refine Crown.absorb R _ _ d ((mul_nonneg (by positivity) hP).trans H) _ hy (fun _=>rfl) (fun i=>?_) (fun i=>?_)
  · simp_rw [h1]; exact (wheel _ (fun _ _ h=>congr_arg Prod.fst h) _ _ _ hk hP _).trans H
  have h2(x j k): reed (f x) (g x) (K x) j k=reed (g x) (f x) (K x) k j:=by simp only [reed,and_comm]
  simp_rw [h1,h2]; exact (wheel _ (fun _ _ h=>add_right_cancel (congr_arg Prod.fst h)) _ _ _ hk hP _).trans H
end YM.CF.Peaks
