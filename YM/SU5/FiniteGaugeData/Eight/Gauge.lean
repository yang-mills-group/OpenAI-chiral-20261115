import YM.SU5.FiniteGaugeData.Brique.Vesta
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Eight
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
variable {N M:Side} {S:Support (More N)} {b:Bool}{C:ℝ}
local notation "F"=>FC (Single N)
local notation "H"=>Seat N→ SU.E
abbrev areaG(N:Side) : Measure (Seat N→ SU.E):= Measure.pi fun _=> SU.group.probHaar
example(N:Side) : Measure.IsMulLeftInvariant (areaG N):= by infer_instance
variable (g h:Seat N→SU.E){x y:Mark N}
abbrev actionG(N:Side)(x:Mark N)(g:Seat N→ SU.E) : Mark N:= fun y=> flipsP g (x (simultaneous g⁻¹ y))
lemma seqG (p:Fields N) : simultaneous g (simultaneous h p)= simultaneous (g*h) p:= Prod.ext (he p.1) (he p.2)
where he(v:Pane N) : Lattice.gauge g (Lattice.gauge h v)= Lattice.gauge (g*h) v:=by funext i; unfold Lattice.gauge; rw [Pi.mul_apply,Pi.mul_apply]; group
lemma idG (p:Fields N) : simultaneous (1 : H) p=p:=Prod.ext (he p.1) (he p.2)
where he(v:Pane N): Lattice.gauge (1 : Seat N→ SU.E) v=v:= by funext i; simp [Lattice.gauge]
private lemma actionG_id (p:Fields N): simultaneous g⁻¹ (simultaneous g p)=p:= by rw [seqG,inv_mul_cancel,idG]
lemma dew_f (N:Side):Continuous (fun y:(Seat N→SU.E)×FC (Single N)=> flipsP y.1 y.2):= by
    simp_rw [flipsP, twist_formula, quantU]; have v:= quant_cont.comp ((shade_cont N).comp (continuous_fst (Y:=FC (Single N)))); exact (v.mul continuous_snd).mul v.star -- syntax
lemma dew_y (N:Side):Continuous (fun y:(Seat N→SU.E) × Fields N=> simultaneous y.1⁻¹ y.2):=by
 change Continuous (fun y:(Seat N→SU.E) × Fields N=> (Lattice.gauge y.1⁻¹ y.2.1,Lattice.gauge y.1⁻¹ y.2.2)); unfold Lattice.gauge; fun_prop
theorem Dew (t:AtSupport b S x) : Measurable (fun y:(Seat N→SU.E) × Fields N=> actionG N x y.1 y.2):=by
 have hx: Measurable (fun y:(Seat N→SU.E) × Fields N => (y.1,x (simultaneous y.1⁻¹ y.2))) := measurable_fst.prodMk (t.env.meas.comp (dew_y N).measurable)
 change Measurable ((fun y:(Seat N→ SU.E)× FC (Single N)=> flipsP y.1 y.2)∘fun y:(Seat N→ SU.E) × Fields N=> (y.1, x (simultaneous y.1⁻¹ y.2))); exact (dew_f N).measurable.comp hx
theorem peso (q:∀ y:Fields N,‖x y‖≤ C) (i:Fields N): ‖actionG N x g i‖ ≤ C:= (twist_norm ..).trans_le (q _)
theorem epochG (t:AtSupport b S x) : AtSupport b S (actionG N x g):=by
 let W:= t.env.cost; refine ⟨⟨?a,W.choose,peso g W.choose_spec⟩,fun u v x' e=> ?_,fun i=> windFine _ (t.allV _)⟩
 case a => exact Measurable.of_uncurry_left (Dew t) -- tune
 exact congrArg (flipsP g) (t.dep _ _ (Skye.tied S u.1 v.1 g⁻¹ g⁻¹ x' fun i _=>rfl) (Skye.tied S u.2 v.2 g⁻¹ g⁻¹ e fun i _=>rfl))
def dewG (N:Side)(x:Mark N): Mark N:=fun y=>∫ g:(Seat N→SU.E), actionG N x g y ∂areaG N
instance (N : Side) : IsProbabilityMeasure (areaG N) := inferInstanceAs (IsProbabilityMeasure (Measure.pi fun i:Seat N=> SU.group.probHaar)) -- redundancy okay?
lemma massG (p:AtSupport b S x)(i:Fields N) : Integrable (fun g=> actionG N x g i) (areaG N):=by
 let W:= p.env.cost; exact Integrable.of_bound (((Dew p).comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable) W.choose (Eventually.of_forall fun g=> peso g W.choose_spec i)
lemma dewBound (q:∀ y: Fields N, ‖x y‖≤ C)(y:Fields N): ‖dewG N x y‖ ≤ C:= le_trans (norm_integral_le_of_norm_le (integrable_const C) (Eventually.of_forall fun g=> peso g q y)) (by simp)
lemma dewSupport(p:AtSupport b S x) : AtSupport b S (dewG N x):=by
 let W:=p.env.cost; exact ⟨⟨(Dew p).stronglyMeasurable.integral_prod_left.measurable,W.choose,dewBound W.choose_spec⟩,fun y z t s=> integral_congr_ae (Eventually.of_forall fun g=>(epochG g p).dep _ _ t s), fun i=> fine_integral (Eventually.of_forall fun g=>(epochG g p).allV _)⟩
lemma dewAdd (p:AtSupport b S x)(u:AtSupport b S y) : dewG N (x+y)=dewG N x+dewG N y:=by funext i; unfold dewG; simp_rw [actionG,Pi.add_apply,map_add]; exact integral_add (massG p i) (massG u i)
lemma dewScale (z:ℂ)(x:Mark N) : dewG N (z•x)= z • dewG N x:=by funext i; simp_rw [dewG,actionG, Pi.smul_apply,flipsP,twist_scalar,integral_smul]; rfl
lemma dewMult (x:Mark N)(t:covariant x)(y:Mark N){p: AtSupport false S y} : dewG N (x*y)= x* dewG N y:=by
 -- integral_payload.Multiply matrices.G/S.real
 funext i; have h(g:Seat N→ SU.E) : flipsP g (x (simultaneous g⁻¹ i))= x i:=by rw [show x (simultaneous g⁻¹ i)=_ from t _ _,←wind_join, mul_inv_cancel,flips_identity]
 unfold dewG; simp_rw [actionG,Pi.mul_apply,map_mul,h]; exact integral_const_mul_of_integrable (massG p i)
lemma dewFrozen (x:Mark N)(p:covariant x) : dewG N x=x:=by
 funext i; have h(g:Seat N→ SU.E): actionG N x g i=x i:=by rw [actionG,show x (simultaneous g⁻¹ i)= _ from p _ _,←wind_join,mul_inv_cancel,flips_identity]
 simp_rw [dewG,h]; simp
lemma dewNatur (p:AtSupport b S x) : covariant (dewG N x):= by
 intro k W
 let y:= simultaneous k W; let f(g:Seat N→SU.E):= actionG N x g y
 let V:F→L[ℝ]F := ⟨(flipsP k).toAlgEquiv.toLinearMap,Fock.breeze _⟩
 change (∫ h,f h ∂areaG N)= V (dewG N x W)
 have h(g:Seat N→SU.E): V (actionG N x g W)= f (k*g):=by change flipsP k (flipsP g (x (simultaneous g⁻¹ W)))= flipsP (k*g) (x (simultaneous (k*g)⁻¹ (simultaneous k W))); rw [←wind_join, mul_inv_rev, ←seqG,actionG_id] -- unfold y
 unfold dewG; rw [←V.integral_comp_comm (massG p W)]; simp_rw [h]; exact (integral_mul_left_eq_self f k).symm -- tune
#print axioms dewNatur
section mildew
open Fock.Brique Girt Nacre Mir Phase RP
variable {Z:Peg N}{c C t v u r e:ℝ}{w n:ℕ}
lemma Neighbor_right {A:Op (Single N)}(p:Neighbor w A) : Neighbor w (twist (tradew N g⁻¹) A):=by
 let U:= tradew N g⁻¹; let T:= twist U
 intro S V h; let B:= cutM (modesIn N S); let Q:= cutM (modesIn N V); change B*T A * Q=B*T A; nth_rw 1 [← (show T B=B from shifter g⁻¹ S), ←(show T Q=Q from shifter g⁻¹ V)]; rw [←map_mul,←map_mul,(show B*A* Q=_ from p S V h),map_mul,show T B=B from shifter g⁻¹ S] -- syntax nth_rw including two
lemma Crater_right (L:Casing N Z.e (Z.Ft false) c C t)(p:Crater w v u Z S x n false): Crater w v u Z S (actionG N x g) n false:=by
 let U:= tradew N g; let W:= twist U; let V:= Z.Ft false; constructor; intro i h Hx; let I':=simultaneous g⁻¹ i
 have hi':Guard I'.2 Z.e:=h.cov _
 obtain ⟨A,k,T,X,y,z,Y,hq⟩:=p.once I' hi' (show x I'≠0 from fun u=> Hx (by unfold actionG; rw [u,map_zero]))
 refine ⟨W A,rot _ k _, T,X,y.twist_t _ (shifter g _),(trace_twist ..).trans z,by rw [actionG,shafted g]; exact twist_tap0 Y g,?_⟩
 intro L' hg ht
 let Q:= tradew N g⁻¹; let M:= twist Q; have hu: ‖M L'-V I'.2‖ ≤ v:= by rw [show V I'.2= M (V i.2) from L.coloredWT i.2 h g⁻¹,←map_sub, (show ‖M (L'-V i.2)‖= ‖_‖ from twist_norm ..)]; exact ht
 have hv: W (M L')=L':= by unfold W M Q U; rw [Mono_tradew]; exact (by let a:=twist_inv (star (tradew N g)) L'; rwa [star_star] at a)
 exact (by nth_rw 1 [←hv]; rw [←map_mul,(show ‖W (A*M L')‖= ‖_‖ from twist_norm ..)]; exact hq (M L') (Neighbor_right g hg) hu)
lemma drawGraft (g:Seat N→SU.E){R:Loom N}{d:ℕ}(u:Roof N c C d R) (x:Orbit N) : simultaneous g (drawn R x)= drawn R (gird g x):=Prod.ext rfl (u.rev x.1 x.2 g).symm
#print axioms Crater_right
end mildew
end YM.CF.Buffered.Afterglow.Hierarchy.Eight
