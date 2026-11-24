import YM.CF.Nacre.Dice
set_option autoImplicit false
noncomputable section
namespace YM.CF.Nacre
open Function Filter Metric Lattice Wilson Laurent Precision Tree Finset Exterior Extra Bloch Fock NormedSpace Lat Rush Cube Scroll SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Font
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
variable {G:Gauge}{m:ℕ}{n:Side}
section core
variable {E:Type*}[NormedAddCommGroup E][NormedSpace ℝ E]
def coordL {k:Type*}[Fintype k][DecidableEq k] : Op k≃L[ℝ] (k→k→ℂ):=
 (show Op k≃ₗ[ℝ] _ from { toFun:=fun x i j=> x i j, invFun:=Matrix.of,left_inv:=fun _=>rfl,right_inv:=fun _=>rfl,map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }).toContinuousLinearEquiv
lemma tort {k:Type*}[Fintype k][DecidableEq k]{x:E}{f:E→ Op k}: ContDiffAt ℝ ω f x ↔ ∀ i j,ContDiffAt ℝ ω (fun x=> f x i j) x:=by
 let L:= coordL (k:=k); have hv: ContDiffAt ℝ ω (L ∘ f) x ↔ ∀ i j,ContDiffAt ℝ ω (fun x=> f x i j) x:= by rw [contDiffAt_pi]; simp_rw [contDiffAt_pi]; rfl
 rw [←hv]; constructor; exact fun h=> L.contDiff.contDiffAt.comp x h; exact fun h=> L.symm.contDiff.contDiffAt.comp x h
lemma sent_f (x:E)(U:E→Config G n)(H:∀ e,ContDiffAt ℝ ω (fun t=> G.mat (U t e)) x)(z:Site n)(w:Walk):ContDiffAt ℝ ω (fun t=> G.mat (travel (U t) z w)) x:=by
 induction w generalizing z with
 | nil=>exact contDiffAt_const
 | cons d w ih=>
    simp_rw [travel,G.mat_mul]; refine ContDiffAt.mul ?_ (ih (z+d.vec)); unfold Step.read; split
    · simp_rw [G.mat_inv]; exact (show _ from (((starL ℝ : G.Mat≃L[ℝ] G.Mat).contDiff).contDiffAt.comp x (H _)))
    exact H _
lemma rent_f (x:E)(U:E→Config G n)(H:∀ e,ContDiffAt ℝ ω (fun t=> G.mat (U t e)) x)(z:Site n)(w:Wind n):ContDiffAt ℝ ω (fun t=> silt z w (U t)) x:=by
 have hx:= sent_f x U H z (boot z w); unfold silt Gauge.curvature; simp_rw [G.mat_inv]; exact G.projectColor.toContinuousLinearMap.contDiff.contDiffAt.comp x (ContDiffAt.smul (f:=fun _=> (1/2:ℝ)) contDiffAt_const (hx.sub (((starL ℝ : G.Mat≃L[ℝ] G.Mat).contDiff).contDiffAt.comp x hx))) -- tune
lemma face_b (x:E)(f:E→SU.E)(h:ContDiffAt ℝ ω (fund ∘ f) x): ContDiffAt ℝ ω (fun i=>(matter (f i)).val) x:=by
 apply tort.2
 simp_rw [matter_matrix,triple];
 rintro ⟨i,a⟩ ⟨j,b⟩; simp only [Matrix.kronecker_apply]; refine ContDiffAt.mul contDiffAt_const ?_; have he i j : ContDiffAt ℝ ω (fun a=> fund (f a) i j) x:=tort.mp h i j
 cases a with
 | inl a=> cases b with
    | inl b=> simp_rw [each,Join.both,Matrix.fromBlocks_apply₁₁, ExTwo.wedge_entry]; exact ((he _ _).mul (he _ _)).sub ((he _ _).mul (he _ _))
    | inr b=> exact contDiffAt_const
 | inr a=> cases b with
    | inl b=> exact contDiffAt_const
    | inr b=> exact Complex.conjCLE.contDiff.contDiffAt.comp x (he a b)
lemma mellow (x:E)(P: Toy m n)(u v:HopK n)(i:Trip m n)(V:E→Bkg (More n))(H:∀ e,ContDiffAt ℝ ω (fun t=> group.mat (V t e)) x): ContDiffAt ℝ ω (fun t=> mold P u v i (V t)) x:=by
 apply ContDiffAt.mul; swap; · exact face_b x _ (sent_f x V H _ _)
 refine tort.2 fun a b=>?_; exact (P (u,a) (v,b) i).contDiff.contDiffAt.comp x (contDiffAt_pi.mpr fun j=> rent_f x V H _ _)
lemma cantor (x:E)(P:Toy m n)(V:E→Bkg (More n))(H:∀ e, ContDiffAt ℝ ω (fun i=> group.mat (V i e)) x): ContDiffAt ℝ ω (cavil P ∘ V) x:=by
 refine tort.2 ?_; rintro ⟨u,i⟩ ⟨v,j⟩; exact tort.1 (ContDiffAt.sum (f:=fun i t=> mold P u v i (V t)) (s:=univ) fun i _=> mellow x P u v i V H) i j
end core
-- apply Topo Matrix.OP note HasDerivAt represent lemma under Frobenius, defeq has ContDiff?
lemma repr_m (p:Edge (Site n)):ContDiff ℝ ω (fun y: fieldDir G n 1=> G.mat (represent y p)):=by
 let V: fieldDir G n 1→ G.Color:=fun y=> collect G y p
 have hu(y:fieldDir G n 1): G.mat (represent y p)= exp (G.colorMat (V y)):=by rw [show represent y p=G.lieExp (V y) by simp [V,represent,RG.increment],G.mat_lieExp]
 simp_rw [hu]; apply AnalyticOnNhd.contDiff (𝕜:=ℝ) -- tune exp
 intro y _; have hP:ContDiffAt ℝ ω V y:= (show (fieldDir G n 1 →L[ℝ] G.Color) from ContinuousLinearMap.proj (p.1,coord p.2)).contDiff.contDiffAt; exact (exp_analytic (𝕂:=ℝ) (𝔸:=G.Mat) (G.colorMat (V y))).comp (f:=fun t=>G.colorMat (V t)) ((G.colorMat.toContinuousLinearMap.contDiff.contDiffAt.comp y hP).analyticAt)

lemma peak_e(x:fieldDir group (More n) 1)(P:Toy m n) : Tendsto (fun t:ℝ=> (t^m)⁻¹ • cavil P (represent (t • x))) (𝓝[≠] 0) (𝓝 (pyre P x)):=by
 let W(t:ℝ):Config group (More n):= represent (t • x)
 let L:= coordL (k:=Single n); have hu: W 0=1:=by simp [W]
 have he (v u:HopK n)(r:Trip m n)(i j:Slot): Tendsto (fun t:ℝ=> (t^m)⁻¹ • mold P u v r (W t) i j) (𝓝[≠] 0) (𝓝 (P (u,i) (v,j) r (fun l=>heat (terse u) (collect group x) (r l)))):=by
    let A(z):=halo P u v r (fun l=> silt (terse u) (r l) (W z)); let G(z):=walkB u v (W z)
    let B:= halo P u v r (fun l=>heat (terse u) (collect group x) (r l))
    have hx:Tendsto (fun z:ℝ=> (z^m)⁻¹ • A z) (𝓝[≠] 0) (𝓝 B):=by
       have hp(i j:Slot):Tendsto (fun z=>(z^m)⁻¹ • A z i j) (𝓝[≠] 0) (𝓝 (B i j)):=by
          let f:= P (u,i) (v,j) r
          have he:= (show Continuous f from f.contDiff (n:=ω) |>.continuous).continuousAt |>.tendsto.comp (show Tendsto (fun z:ℝ=> fun l:Fin m=> z⁻¹ • silt (terse u) (r l) (W z)) (𝓝[≠] (0:ℝ)) (𝓝 fun l:Fin m=> heat (terse u) (collect group x) (r l)) from tendsto_pi_nhds.mpr fun l=>pulled_l _ _ x)
          convert he using 1; ext1 z; change (z^m)⁻¹ • f _= f _; rw [f.map_smul_univ (fun _=>z⁻¹)]; simp
          rfl
       let L:=coordL (k:=Slot); have hh:Tendsto (fun z:ℝ=>L ((z^m)⁻¹ • A z)) (𝓝[≠] 0) (𝓝 (L B)):=tendsto_pi_nhds.mpr fun i=>tendsto_pi_nhds.mpr fun j=> hp i j; exact (L.symm.continuous.tendsto _).comp hh
    have hk : Tendsto G (𝓝[≠] 0) (𝓝 1):=by
       have ht:ContDiffAt ℝ ω G 0:=by apply face_b 0 _ _; apply sent_f 0 W; intro i; apply (repr_m (G:=group) i).contDiffAt.comp; fun_prop -- tune
       have hp:G 0=1:=by unfold G walkB W; rw [zero_smul, show travel (represent (0:fieldDir group (More n) 1)) _ _=1 from Push.stroll_zero ..,map_one]; rfl
       rw [←hp]; exact ht.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hy := ((coordL (k:=Slot)).continuous.tendsto _).comp (hx.mul hk); rw [mul_one] at hy; have hl:= tendsto_pi_nhds.mp (tendsto_pi_nhds.mp hy i) j; refine hl.congr ?_; intro z; change (((z^m)⁻¹ • A z)*G z) i j=_; rw [Matrix.smul_mul]; rfl
 let f(t:ℝ):=(t^m)⁻¹ • cavil P (represent (t • x)); have hp:Tendsto (L ∘ f) (𝓝[≠] (0:ℝ)) (𝓝 (L (pyre P x))):=by
    refine tendsto_pi_nhds.mpr fun i=> tendsto_pi_nhds.mpr fun j=>?_
    obtain ⟨u,i⟩:=i; obtain ⟨v,j⟩:=j
    change Tendsto (fun z:ℝ=> (z^m)⁻¹ • cavil P (W z) (u,i) (v,j)) _ _
    simp_rw [cavil,Matrix.of_apply,Matrix.sum_apply,Finset.smul_sum]; exact tendsto_finsetSum _ fun _ _=>he ..
 exact (L.symm.continuous.tendsto _).comp hp
end YM.CF.Nacre
