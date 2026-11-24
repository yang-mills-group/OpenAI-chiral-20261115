import YM.CF.Laic.Broke
set_option autoImplicit false
noncomputable section
namespace YM.CF.Laic
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Lat Rush Cube Scroll SU Peaks Dial Fock Thera Nacre Branch Drapes Tulip Paige Spire Vault Font Kennel Planned.JetPort Push.Uniform
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {n:Side}{ι κ:Type}[Fintype ι][Fintype κ][LinearOrder κ]{k:ℕ}{l:ι→Site n}{u:κ→Site n}{F:Positions ι→ Op κ}{x:Positions ι}{a b c d:ℝ}
lemma wire_one(l:ι→Site n)(u:κ→Site n)(ha:0<a): CableM l u u a k (fun _: Positions ι=> (1:Op κ)) x 1:=by
 refine ledger (fun _ _=>contDiffAt_const) fun i j=> ?_
 have he:= (allows_const (n:=k) x (le_refl ‖(1:Op κ) i j‖)).beacon (r:=0) (s:=Set.univ) (l:=l) (y:=u i) (fun _ _ _ _ _=>rfl) univ_mem ha.le
 refine he.mono ?_
 rw [Matrix.one_apply]; split; next hv=> simp [hv,Push.Uniform.Decay]
 next hv=> simp [Push.Uniform.Decay]; positivity
lemma wire_zero(l:ι→Site n)(u:κ→Site n)(ha:0<a): CableM l u u a k (fun _:Positions ι=>(0:Op κ)) x 1:=by
 refine ledger (fun _ _=>contDiffAt_const) fun i j=>?_ ; apply (Allows.beacon (allows_const (n:=k) x (le_refl ‖(0:Op κ) i j‖)) (r:=0) (s:=Set.univ) (fun _ _ _ _ _=>rfl) univ_mem ha.le).mono; simp [Push.Uniform.Decay]; positivity
-- cost deterministic L
lemma pow_bill(ha:0<a)(p:0<c)(Y k N:ℕ) : ∃ d b:ℝ,0<d ∧ d≤a ∧ 0<b∧∀ {ι κ:Type}[Fintype ι][Fintype κ][LinearOrder κ]{n:Side}{l:ι→Site n}{u:κ→Site n}{x}{F:Positions ι→Op κ}, ContDiffAt ℝ ω F x→CableM l u u a k F x c → Multiplicity u Y→ CableM l u u d k (fun y=>F y^N) x b:=by
 induction N with
 | zero=> refine ⟨a,1,ha,le_rfl,zero_lt_one,?_⟩; intro ι κ _ _ _ n l u x F h p v; simp_rw [pow_zero]; exact wire_one l u ha
 | succ i ih=>
    obtain ⟨d,b,h,hc,hb,M⟩:=ih; have hs := slip_pos k h; let V:=b*c*conductor k Y d
    have hp:0<V:=mul_pos (mul_pos hb p) (conductor_pos k Y h); refine ⟨slip k d,V+V,hs,(slip_le k h.le).trans hc,by linarith,?_⟩; intro ι κ _ _ _ n l u x F he hv hy; simp_rw [pow_succ]; exact wire_mul (Nacre.tort.mp (he.pow i)) (Nacre.tort.mp he) (M he hv hy) (hv.mild hc p.le) h hb p hy
lemma skim_bill(ha:0<a)(p:0<c)(Y k N:ℕ): ∃ d b:ℝ,0<d∧d≤a∧ 0<b ∧ ∀ {ι κ:Type}[Fintype ι][Fintype κ][LinearOrder κ]{n:Side}{l:ι→Site n}{u:κ→Site n}{x} {F:Positions ι→Op κ},ContDiffAt ℝ ω F x→CableM l u u a k F x c→ Multiplicity u Y→ CableM l u u d k (fun y=> ∑ i∈ Finset.range N,F y^i) x b:=by
 induction N with
 | zero=>refine ⟨a,1,ha,le_rfl,zero_lt_one,?_⟩; intro ι κ _ _ _ n l u x F h p v; simp only [range_zero,sum_empty]; exact wire_zero _ _ ha
 | succ i ih=>
   obtain ⟨d,b,h,hp,hb,H⟩:=ih; obtain ⟨e,s,t,w,y,W⟩:=pow_bill ha p Y k i; refine ⟨min d e,b+s,lt_min h t,(min_le_left ..).trans hp,by linarith,?_⟩
   intro ι κ _ _ _ n l u x F h m p; simp_rw [sum_range_succ]; refine inkP (Nacre.tort.mp (ContDiffAt.sum (s:=Finset.range i) (f:=fun i x=>F x^i) fun i _=>h.pow i)) (Nacre.tort.mp (h.pow i)) ((H h m p).mild (min_le_left ..) hb.le) ((W h m p).mild (min_le_right ..) y.le)
lemma lineG (v:Positions ι)(k:ℕ)(h:ContDiffAt ℝ ω F 0)(p:F 0=0): ∃ a:Op κ,Tendsto (fun t:ℝ=> (t^k)⁻¹ • (F (t • v))^k) (𝓝[≠] 0) (𝓝 a):=by
 let x:=Nacre.trim 1 F v; have he: Tendsto (fun t:ℝ=> t⁻¹ • F (t • v)) (𝓝[≠] 0) (𝓝 x):=by
    have hp : cFoot 1 F:=by intro i e; rw [show i=0 from by omega]; ext; simp only [iteratedFDeriv_zero_apply,p]; rfl
    simpa only [pow_one] using (argent (h.of_le le_top)).mp hp v
 refine ⟨x^k, (he.pow k).congr (fun t=>?_)⟩; rw [smul_pow,inv_pow]
lemma arcK (h:ContDiffAt ℝ ω F 0)(p:F 0=0): cFoot (k+1) (fun y=> (1-F y)⁻¹ -∑ i∈ Finset.range (k+1), F y^i):=by
 let V(y):= (1-F y); let f(y):=(V y)⁻¹; have hp:V 0=1:=by simp [V,p]
 have ht: ContDiffAt ℝ ω f 0:=(inv_p (t:= (show IsUnit (V 0) from hp.symm ▸ isUnit_one))).comp _ (contDiffAt_const.sub h); let g(y:Positions ι):= ∑ i∈Finset.range (k+1), F y^i; apply nextF (f:=fun y=> f y-g y) ((ht.sub (ContDiffAt.sum (f:=fun i y=> F y^i) (s:= Finset.range (k+1)) fun i _=>h.pow i)).of_le le_top)
 intro x; obtain ⟨a,hh⟩:=lineG x k h p; let v(t:ℝ):= t • x; let K:=𝓝[≠] (0:ℝ); have hv:Tendsto v K (𝓝 0):=(Hull.ray_home x).mono_left nhdsWithin_le_nhds
 have hy:= h.continuousAt.tendsto.comp hv; rw [p] at hy; have hs:= (ht.continuousAt.tendsto.comp hv).mul (hh.mul hy); rw [mul_zero,mul_zero] at hs; refine hs.congr' ?_
 have hz: ∀ᶠ y in 𝓝 0, f y - g y=f y * (F y)^(k+1):=by
    have ht:Tendsto V _ (𝓝 (V 0)):= (contDiffAt_const.sub h).continuousAt.tendsto; rw [hp] at ht; filter_upwards [ht.eventually (Units.isOpen.mem_nhds (show (1:Op κ)∈{x| IsUnit x} from isUnit_one))] with i hi; have hh :V i*g i=1-F i^(k+1):=by
       unfold V g; rw [← neg_sub (F i),neg_mul,mul_geom_sum,neg_sub]
    apply hi.mul_left_cancel; rw [mul_sub,←mul_assoc,show V i*f i=1 from (live hi).1,hh,one_mul,sub_sub_cancel]
 filter_upwards [hv.eventually hz] with t h; change f _* (((t^k)⁻¹ • F _^k) * F (v t))= _; rw [Matrix.smul_mul, Matrix.mul_smul,←pow_succ,←h]
lemma sameV {D:Positions ι→Op κ}(h:ContDiffAt ℝ ω D 0)(p:ContDiffAt ℝ ω F 0)(v:cFoot (k+1) (F-D))(t:CableM l u u a k D 0 c):CableM l u u a k F 0 c:=by
 intro r i j b e q; let L:Op κ→L[ℝ]ℝ:= (matte r).comp ((show Op κ→ₗ[ℝ] ℂ from ⟨⟨fun p=> p i j,fun a b=>rfl⟩,fun a b=>rfl⟩).toContinuousLinearMap)
 have he:iteratedFDeriv ℝ b F 0=iteratedFDeriv ℝ b D 0:=sub_eq_zero.mp ((iteratedFDeriv_sub_apply (p.of_le le_top) (h.of_le le_top)).symm.trans (v _ (by omega))); have ht: iteratedFDeriv ℝ b (L ∘ F) 0=iteratedFDeriv ℝ b (L ∘ D) 0:=by rw [L.iteratedFDeriv_comp_left h le_top,L.iteratedFDeriv_comp_left p le_top,he];
 change ‖iteratedFDeriv ℝ b (L ∘ F) 0 _‖≤_; rw [ht]; exact t r i j b e q
lemma ventB(ha:0<a)(p:0<c)(k Y:ℕ) : ∃ b u:ℝ,0<b ∧ b≤a ∧ 0<u ∧ ∀ {n:Side}{ι κ:Type}[Fintype ι][Fintype κ][LinearOrder κ]{l:ι→ Site n}{m:κ→ Site n}{F:Positions ι→Op κ}, Multiplicity m Y→ ContDiffAt ℝ ω F 0→ F 0=0 → CableM l m m a k F 0 c→ CableM l m m b k (fun x=> (1+F x)⁻¹) 0 u:=by
 obtain ⟨b,u,r,h,w,H⟩:=skim_bill ha p Y k (k+1); refine ⟨b,u,r,h,w,?_⟩; intro n ι κ _ _ _ l m F q t hp hx; have hs:=arcK (k:=k) t.neg (by simp [hp]); simp only [sub_neg_eq_add] at hs; refine sameV (ContDiffAt.sum (s:=Finset.range (k+1)) (f:=fun i x=>(-F x)^i) fun i _=>t.neg.pow _) ((inv_p (show IsUnit (1+F 0) by rw [hp]; simp)).comp (f:=fun x=>1+F x) _ (contDiffAt_const.add t)) hs (H t.neg (inkN (Nacre.tort.mp t) hx) q)
end YM.CF.Laic
