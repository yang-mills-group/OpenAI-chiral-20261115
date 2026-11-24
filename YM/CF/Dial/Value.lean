import YM.CF.Dial.Port
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Dial
open Function Filter Lattice Laurent Bloch Next.Free Metric Lat Finset Branch Cube Tenant SU Rush Drapes Fir Tulip Fock Peaks
open scoped Topology Matrix MatrixOrder BigOperators Matrix.Norms.L2Operator Kronecker InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {N P:Side}(G:Ratio N P)
variable {ι:Type*}{L:Side}{u v:AxisT}{A B:Chop ι}{a r e s c:ℝ}{k:ℕ}
omit G
lemma liquidity (h:BoxD L u u A)(hc:0<c)(hq:c<1) (H:∀ i {N P:Side}(G: Ratio N P),G.count=L→ k≤N.val→ ‖A i G (vacancyY N P)‖ ≤ c):BoxD L u u (fun i _ _ G x=>(1-A i G x)⁻¹) ∧ Interest L (fun i _ _ G x=>1-A i G x):=by
  obtain ⟨a,r,e,ha,hr,he,l,S⟩:=h
  obtain ⟨d,m,K,C,hp,g,-,hk,hC,hl,t,hT⟩:= awaken (A:=A) (k:=max k l) (fun i _ _ G hx t=> S i G hx ((le_max_right ..).trans t)) ha hr he hc hq (fun i _ _ G hz v=> H i G hz ((le_max_left ..).trans v))
  let F(n:ℕ):= K*C^n; have hF:Summable F:= (summable_geometric_of_lt_one hC.le hl).mul_left _
  have hh(i){N P:Side}(G: Ratio N P)(he:G.count=L)(hv:t≤N.val)(x: zoneP G m):
       (1-A i G x.val) * (∑' j:ℕ,A i G x.val^j)=1:= by apply Summable.one_sub_mul_tsum_pow; exact hF.of_norm_bounded fun b=> (hT b i G he hv).lib.boundOp hp.le x
  constructor
  · apply boxify (a:=d) (C:=∑' i,F i) (k:=t) ?_ hp g
    intro i N P G he ht
    have hA (x:TopK G m) : (1-A i G x.val)⁻¹=∑' j:ℕ,A i G x.val^j:= Matrix.inv_eq_right_inv (hh i G he ht _)
    have hx : Crown (badge _) (rope G u m) (rope G u m) d (∑' j,F j) (fun x=>∑' j:ℕ,A i G x.val^j):= Crown.tsK _ (fun n=> hT n i G he ht) hp.le hF
    convert hx using 1; funext x; exact hA x
  exact ⟨m,g,t,fun i _ _ G he hv x hz=> live_of (hh i G he hv ⟨x,hz⟩)⟩
section
variable {J:Type*}[DecidableEq J][Fintype J][Nonempty J]
lemma seal_up {a b:Op J}(h:a≤b)(v:Op J):v*a*star v≤ v*b*star v:=by
  apply sub_nonneg.mp; rw [←sub_mul,←mul_sub]; exact star_right_conjugate_nonneg (sub_nonneg.mpr h) v
lemma gainS (t v:Op J)(L: ℝ)(h:t*v=1)(hc:‖v‖≤L)(hr:0<L): (L*L)⁻¹ • (1:Op J)≤ t * star t:=by
  have he : v*star v ≤ (L*L) • (1:Op J):=by
    apply (op_le_norm_one (show IsSelfAdjoint (v*star v) from by rw [isSelfAdjoint_iff,star_mul,star_star])).trans (smul_le_smul_of_nonneg_right _ zero_le_one)
    apply (norm_mul_le ..).trans; rw [norm_star]; exact mul_le_mul hc hc (norm_nonneg _) hr.le
  have hx:=seal_up he t; rw [←mul_assoc t, h,one_mul,←star_mul,h, star_one,Algebra.mul_smul_comm,mul_one, Algebra.smul_mul_assoc] at hx -- check `star v*star t=star (t*v)`
  exact (smul_le_smul_of_nonneg_left hx (show 0≤(L*L)⁻¹ by positivity)).trans_eq (inv_smul_smul₀ (mul_pos hr hr |>.ne') _)
lemma spreadK (t v:Op J)(L:ℝ)(h:t*v=1)(g:‖v‖ ≤ L)(e:2≤L)(q:‖t‖ ≤ L): ‖1 - (↑((L*L)⁻¹):ℂ) • (t*star t)‖ ≤ 1-(L*L)⁻¹*(L*L)⁻¹:=by
  have hp: 0<L:= by linarith
  let M:=L*L; have hh:1<M:=by unfold M; nlinarith; -- inspect
  have he:0<M⁻¹:= inv_pos.mpr (zero_lt_one.trans hh); have hk:M⁻¹<1:=inv_lt_one_of_one_lt₀ hh
  let A:=t*star t; let X:=1-M⁻¹ • A
  have hv:0≤X:=sub_nonneg.mpr (by
    have hA :‖A‖≤M :=(norm_mul_le ..).trans (by rw [norm_star]; exact mul_le_mul q q (norm_nonneg _) hp.le)
    have hB: A≤ M • (1:Op J):=(op_le_norm_one (IsSelfAdjoint.mul_star_self _)).trans (smul_le_smul_of_nonneg_right hA zero_le_one)
    exact (smul_le_smul_of_nonneg_left hB he.le).trans (le_of_eq (inv_smul_smul₀ (ne_of_gt (zero_lt_one.trans hh)) _)))
  have hK:= gainS t v L h g hp; have hr: X ≤ (1-M⁻¹*M⁻¹) • (1:Op J) :=by
    rw [sub_smul, one_smul,mul_smul]; exact sub_le_sub_left (smul_le_smul_of_nonneg_left hK he.le) _
  have hm : 0<1-M⁻¹*M⁻¹:=by nlinarith
  rw [show (↑((L*L)⁻¹):ℂ) • (t*star t) = M⁻¹ • A by ext; simp [M,A,Complex.real_smul]]; change ‖X‖≤_; apply (CStarAlgebra.norm_le_iff_le_algebraMap _ hm.le hv).mpr; rwa [Algebra.algebraMap_eq_smul_one]
end
/-- Invert with vacuum data only. -/
lemma ocean (h:BoxD L u v A)(r:ℝ)(H:∀ i {N P:Side}(G: Ratio N P),G.count=L→ k≤N.val→∃ X, A i G (vacancyY N P)*X=1∧ ‖X‖ ≤ r): BoxD L v u (fun i _ _ G x=> (A i G x)⁻¹) ∧ Interest L A:=by
  have hb:=h
  obtain ⟨a,c,e,ha,hc,he,n,V⟩:=h
  let M:ℝ:=max (max c r) 2; have hp:2 ≤ M := le_max_right ..; have hM:0<M:=by linarith
  let t:ℝ:=(M*M)⁻¹; have ht:0<t:=by unfold t; positivity
  let F:Chop ι:=fun i _ _ G x=> (t:ℂ) • star (A i G (chargeB x))
  have hF:BoxD L v u F:= hb.balm.scale (fun _=> ↑t) _ (fun i=>le_rfl)
  let P0:Chop ι:=fun i _ _ G x=> 1-A i G x*F i G x; have hx:BoxD L u u P0:= BoxD.one.sub (hb.chain hF)
  have hg:t<1:=by unfold t; apply inv_lt_one_of_one_lt₀; nlinarith [hp]
  have h1:0<1-t*t:=by nlinarith
  have h2:1-t*t<1:=by nlinarith
  have hQ(i){N P:Side}(G: Ratio N P)(hu:G.count=L)(hv:max k n≤N.val):‖P0 i G (vacancyY N P)‖ ≤ 1-t*t:=by
    unfold P0 F; rw [show chargeB (vacancyY N P)=_ from charge_p _]; rw [Algebra.mul_smul_comm]
    obtain ⟨X,h,hK⟩:= H i G hu ((le_max_left ..).trans hv)
    apply spreadK _ X M h (hK.trans ((le_max_right ..).trans (le_max_left ..))) hp
    exact ((V i G hu ((le_max_right ..).trans hv)).lib.boundOp ha.le ⟨_, vacant G e he⟩).trans ((le_max_left c r).trans (le_max_left ..)) -- tune
  obtain ⟨hT,p,l,y,H'⟩:= liquidity hx h1 h2 @hQ
  have hz(i){N P:Side}(G: Ratio N P)(hu:G.count=L)(hv:y≤N.val){x}(h:x∈zoneP G p): A i G x*(F i G x*(1-P0 i G x)⁻¹)=1:=by rw [←mul_assoc,show A i G x*F i G x=1-P0 i G x from (sub_sub_cancel 1 _).symm]; exact (live (H' i G hu hv _ h)).1
  refine ⟨?_,p,l,y, fun i _ _ G he hv x h=>live_of (hz i G he hv h)⟩
  obtain ⟨d,R,m,s,Q,w,W,H⟩:= hF.chain hT
  refine boxify (k:=max W y) (C:=R) ?_ s (lt_min w l); intro i N P G he hv
  convert neck (lt_min w l) (min_le_left ..) H i G he ((le_max_left ..).trans hv) using 1; funext x; exact Matrix.inv_eq_right_inv (hz i G he ((le_max_right ..).trans hv) (portland G x.property (min_le_right m p))) -- tune defeq
end YM.CF.Dial
