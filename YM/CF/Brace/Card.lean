import YM.CF.Brace.Arcuate
set_option autoImplicit false
noncomputable section
namespace YM.CF.Brace
open Function Filter Lattice Metric Lat Finset Cube Tenant SU Fock Dial Phase
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {m B : Side}{U:Skin m B}{s:ArrayF m}{X:Sheen m B}
-- v unnormalized at top, t ramps linearly
-- normalize. gauge covariance at active points; fallback invalid
def box (x:Vect): Ballot:= if h:x=0 then apex else ⟨ren x,by simp [Sphere,ren_norm x h]⟩
lemma box_u {x:Vect}(h:x≠0):(box x).val=ren x:=by simp [Brace.box,h] -- `box` ambig
lemma box_cont {x:Vect}(h:x≠0):ContinuousAt box x:=by
  apply Topology.IsInducing.continuousAt_iff (g:=fun x:Ballot=>x.val) ⟨rfl⟩ |>.mpr; refine (ren_cont x h).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ne_fun continuous_id continuous_const|>.mem_nhds (show id x≠0 from h)] with i p; exact (box_u (show i≠0 from p)) -- direction

def ark (m B:Side)(U:Skin m B)(s:ArrayF m)(X:Sheen m B)(t:ℝ)(q:Sq): Sheen m B:=fun i=> box (roofV m B U s X t q i)
structure Foil (m B : Side)(e p:ℝ)(r:Zone)(s:ArrayF m)(X:Sheen m B)(U:Skin m B) : Prop where
 flag : Attested m B U s (insert 0 r)
 tags : Tags s X
 guard : Guard U e
 slowX : Slow U (hook X) p
 nonzero : 0∉r
structure Guide(B:Side)(e p d:ℝ) : Prop where
 pPositive : 0<p
 curvature : 0≤e
 residual : pot B e*7+7*(4*B.val*p)≤ low/2
 expense : 4/low*(14*(1/(width B:ℝ)+3*pot B e)+p) < d
 vote : e≤d

variable {e p d:ℝ}
lemma resolve(d:ℝ)(h:0<d): ∃ n:ℕ,∀ B:Side,n≤B.val→ ∃ e p:ℝ,0<e ∧ Guide B e p d:=by
  obtain ⟨n,H⟩:= scalable _ h; refine ⟨n,fun B hc=>?_⟩
  obtain ⟨a,t,W⟩:= H B hc; have hp:4/low*(14*(1/(width B:ℝ)+3*pot B 0)+0)<d:=by rw [add_zero]; exact (W 0 t.le).2
  let f(u:ℝ):=pot B u*7+7*(4*B.val*u); let g(u:ℝ):=4/low*(14*(1/(width B:ℝ)+3*pot B u)+u)
  have hf:Continuous f:=by unfold f pot; fun_prop
  have hg:Continuous g:=by unfold g pot; fun_prop
  have he: f 0<low/2:=by simp [f,pot,low_p]
  have hx:∀ᶠ i in 𝓝[>] (0:ℝ), f i<low/2 ∧ g i< d ∧ i<d:=by
    apply Eventually.filter_mono nhdsWithin_le_nhds; exact Eventually.and (hf.continuousAt (gt_mem_nhds he)) (Eventually.and (hg.continuousAt (gt_mem_nhds hp)) (gt_mem_nhds h)) -- tune type
  obtain ⟨w,hw,p,v,x⟩:= ((show ∀ᶠ i in 𝓝[>] (0:ℝ), i∈Set.Ioi 0 from self_mem_nhdsWithin).and hx).exists
  change 0<w at hw; exact ⟨w,w,hw,hw,hw.le,p.le,v,x.le⟩
lemma Guide.pull (h:Guide B e p d){k:ℝ}(l:0≤k)(u:k≤e):Guide B k p d:=by
  have he := h.curvature; have hx:pot B k≤pot B e:=mul_le_mul_of_nonneg_left u (by positivity)
  refine ⟨h.pPositive,l,?_,lt_of_le_of_lt ?_ h.expense, u.trans h.vote⟩
  · apply le_trans _ h.residual; gcongr
  have ht : 0≤4/low:=div_nonneg (by norm_num) low_p.le; gcongr
  -- `gcongr` vs residual use
variable {r:Zone}(h:Foil m B e p r s X U)(g:Guide B e p d)
include h g
lemma angel(q:Sq)(hq:q∈zone r)(t:ℝ)(ht:t∈Set.Icc 0 1)(z): low/2≤ ‖roofV m B U s X t q z‖:= atHome hq.1 g.curvature h.guard h.tags g.pPositive h.slowX r hq h.nonzero h.flag g.residual t ht _
lemma ark_u(q:Sq)(hq:q∈zone r)(t:ℝ)(ht:t∈Set.Icc 0 1)(z): hook (ark m B U s X t q) z= ren (roofV m B U s X t q z):= box_u (norm_pos_iff.mp ((half_pos low_p).trans_le (angel h g q hq t ht z)))
lemma ark_bound(q:Sq)(hq:q∈zone r)(t:ℝ)(ht:t∈Set.Icc 0 1):Slow U (hook (ark m B U s X t q)) d:=by
  have hn:0≤t:=ht.1; have ht':t≤1:=ht.2
  intro z i; rw [ark_u h g q hq t ht,ark_u h g q hq t ht,turn_ren];
  apply lt_of_le_of_lt ((ren_near (by rw [turn_norm]; exact angel h g _ hq _ ht _) (angel h g _ hq _ ht _)).trans (mul_le_mul_of_nonneg_left ?_ (div_nonneg (by norm_num) low_p.le))) g.expense
  let k:=U (z,i); rw [roofV,roofV,show ∀ (i j:Vect),turn k (i+j)=turn k i+turn k j from fun i j=>map_add (spinV k) i j,turn_mul,turn_mul,add_sub_add_comm,←smul_sub,←smul_sub]
  apply (norm_add_le ..).trans; rw [norm_smul,norm_smul, Real.norm_of_nonneg hn, Real.norm_of_nonneg (sub_nonneg.mpr ht')];
  apply add_le_add ((mul_le_of_le_one_left (norm_nonneg _) ht').trans (paint_gap m B s hq.1 z g.curvature h.guard i)) ((mul_le_of_le_one_left (norm_nonneg _) (sub_le_self _ hn)).trans (h.slowX z i).le)
lemma canvas (q:Sq)(hq:q∈zone r)(x y:ℝ)(hx:x∈Set.Icc 0 1)(hy:y∈Set.Icc 0 1)(z):
 ‖hook (ark m B U s X x q) z-hook (ark m B U s X y q) z‖ ≤ 4/low*(2* |x-y|):=by
 rw [ark_u h g q hq x hx,ark_u h g q hq y hy]; apply (ren_near (angel h g _ hq _ hx _) (angel h g _ hq _ hy _)).trans
 apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) low_p.le)
 unfold roofV; rw [add_sub_add_comm,←sub_smul,←sub_smul, sub_sub_sub_cancel_left]; apply (norm_add_le ..).trans; rw [norm_smul,norm_smul,hookN, mul_one,norm_sub_rev y,Real.norm_eq_abs,two_mul]; exact add_le_add_left (mul_le_of_le_one_right (abs_nonneg _) (paint_bound m B s hq.1 _)) _
end YM.CF.Brace
