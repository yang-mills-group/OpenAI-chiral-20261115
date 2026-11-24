import GaugeFieldConstruction.Loomcost
import YM.AnalyticBridge.SECTOR_AFFINE_JETS.Point
import YM.CF.Buffered.Facades
import YM.CF.Reef.Ice
/-! # X3 - Face price gradient/gate cost including derivatives at roots. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 160000
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson AnalyticBridge.SectorAffine Laurent Finset MeasureTheory Gauge RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix.Norms.Frobenius Classical
open Push.Uniform Buffered.Region FlightFlux Work Tensor
variable {E F Z:Type} [NormedAddCommGroup E][NormedSpace ℝ E][NormedAddCommGroup F][NormedSpace ℝ F][NormedAddCommGroup Z][NormedSpace ℝ Z] {K d v t r u c:ℝ}{j k:ℕ}{n:Side}{G:Gauge}
namespace Shield
lemma packs (L:E→L[ℝ] F)(f:F→Z)(h:Allows k f 0 c)(p:‖L‖≤1): Allows k (f ∘ L) 0 c:=by
 have he:L 0=0:=map_zero _
 have hp: ContDiffAt ℝ ω f (L 0):= by rw [he]; exact h.analytic
 refine ⟨hp.comp 0 L.contDiff.contDiffAt,fun i u=>?_⟩; rw [Next.Foundations.jets_linear L (h.analytic.of_le le_top)]
 exact (ContinuousMultilinearMap.norm_compContinuousLinearMap_le ..).trans ((mul_le_of_le_one_right (norm_nonneg _) (Finset.prod_le_one (fun i _=>norm_nonneg _) (fun i _=>p))).trans (h.norm_le i u))
lemma pool(f:E→F)(h:Allows k f 0 c)(s:‖f 0‖ ≤ d*t)(p:0<t)(q:t≤1)(e:c≤d): Allows k (fun i=> f (t • i)) 0 (d*t):=by
 refine ⟨(show ContDiffAt ℝ ω (f ∘ fun i:E=> t • i) (0:E) from ContDiffAt.comp _ ((show t • (0:E)=0 from smul_zero t)|>.symm ▸ h.analytic) (contDiffAt_id.const_smul _)), ((Offset.Through.control h).contract p.le q s (mul_le_mul_of_nonneg_right e p.le)).pay⟩ -- tune proof
lemma minus_B {f g:E→F}(h:Allows k f 0 c)(p: Allows k g 0 K): Allows k (fun i=> f i -g i) 0 (c+K):=by simpa [sub_eq_add_neg] using h.add (p.smul (-1))
abbrev tandem (G:Gauge)(n:Side):= Directions G n × Directions G n
def βten (t:ℝ)(U:Config G n)(i:tandem G n):=increment (increment U (t • i.1)) (t • i.2)
lemma tenor0 (t:ℝ)(U:Config G n): βten t U 0=U:=by unfold βten; simp
lemma tenorS (t:ℝ)(U:Config G n)(i:tandem G n):βten 1 U (t • i)=βten t U i:=by unfold βten; simp
lemma sparkLeft(f:E→F)(h:Allows k f 0 c): Allows k (fun x:E×E=>f x.1) 0 c:=packs (ContinuousLinearMap.fst ℝ E E) f h (ContinuousLinearMap.norm_fst_le ..)
lemma sparkR(f:E→F)(h:Allows k f 0 c): Allows k (fun x:E×E=>f x.2) 0 c:=packs (ContinuousLinearMap.snd ℝ E E) f h (ContinuousLinearMap.norm_snd_le ..)
lemma tinder(G:Gauge)(k:ℕ):∃ D:ℝ,0≤D∧∀ {n:Side}(U:Config G n)(i:Face (Per n)),Allows k (fun x:tandem G n=> G.mat (faceValue (βten 1 U x) i)) 0 D:=by
 obtain ⟨C,c,H⟩:= linkage_v G k; let B:ℝ:=2^k*C*C; let D:= travelCost G k 4 B; refine ⟨max D 0,le_max_right ..,@fun n U i=>?_⟩; change Allows k _ 0 _
 have hr(e:Edge (Site n)): Allows k (fun x:tandem G n=> G.mat ((βten 1 U x) e)) 0 B:=by
    let v(q: tandem G n):=(βten 1 U q) e; let z(q:tandem G n):=increment (1:Config G n) q.2 e; let h(q:tandem G n):=increment U q.1 e
    have hv: v=fun q=> z q*h q:=funext fun q=>by unfold v z h; simp [βten,increment]
    have hz:Allows k (fun i=> G.mat (z i)) 0 C:= sparkR (E:=Directions G n) (F:=G.Mat) (fun i=> G.mat (increment (1:Config G n) i e)) (c:=C) (H n e 1)
    have hh:Allows k (fun i=> G.mat (h i)) 0 C:= sparkLeft (E:=Directions G n) (F:=G.Mat) (fun i=> G.mat (increment U i e)) (c:=C) (H n e U)
    change Allows k (fun i=>G.mat (v i)) 0 B; rw [hv]; exact Allows.times (x:=(0:tandem G n)) (f:=z) (g:=h) hz hh
 exact (travel_jets (U:=fun i:tandem G n=>βten 1 U i) hr i.1 (w:=square i.2.val.1 i.2.val.2) (show (square i.2.val.1 i.2.val.2).length≤4 from le_rfl)).mono (le_max_left ..)
-- tune universe Face index. Through arm
lemma bone (G:Gauge)(k:ℕ):∃ e v:ℝ,0≤e∧0≤v ∧∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](W:E→ G.El)(t:ℝ),0<t→t≤1→ (G.chord (W 0)≤t) → Allows k (fun i=> G.mat (W i)-1) 0 (d*t) → Allows k (fun i=> ‖G.curvature (W i)‖^2) 0 (e*t^2)∧ Allows k (fun i=> diagonal (fourth G) (G.curvature (W i))) 0 (v*t^2):=by
 -- d implicit. curvature projection linear on diff. fourth via hom scaling and jet on ball. 
 let Q:=curvatureL G
 have hq(x:G.El): Q (G.mat x-1)= G.curvature x:=by
    change G.projectColor ((1/2:ℝ) • ((G.mat x-1)-star (G.mat x-1)))= _; rw [curvature, mat_inv,star_sub,star_one, sub_sub_sub_cancel_right]
 let J:= curvatureCost G*|d|; have hj:0≤J:= mul_nonneg (curvature_nn _) (abs_nonneg _)
 let y(x:G.Color):=‖x‖^2; let L(x:G.Color):= diagonal (fourth G) x
 obtain ⟨M,h,H⟩:= exists_allows (f:=y) (isCompact_closedBall (0:G.Color) J) (fun x _=> (contDiff_norm_sq ℝ|>.contDiffAt)) k
 obtain ⟨X,m,V⟩:= exists_allows (f:=L) (isCompact_closedBall (0:G.Color) J) (fun x _=> ((fourth G).contDiff.comp (contDiff_pi.mpr (fun _=>contDiff_id))).contDiffAt) k
 let N:=composeCost k M J; let T:=composeCost k X J; have hN:0≤N:=by unfold N composeCost; positivity
 have hT:0 ≤ T:=by unfold T composeCost; positivity
 refine ⟨N,T,hN,hT,@fun E _ _ W t h p _ k'=>?_⟩
 let f(i):=t⁻¹ • G.curvature (W i); have hu: Allows k f 0 J:=by
    unfold f; simp_rw [← hq] -- tune unfold f
    apply Allows.mono ((Allows.linear Q (K:=curvatureCost G) (k'.mono (mul_le_mul_of_nonneg_right (le_abs_self _) h.le)) le_rfl).smul t⁻¹); unfold J; rw [abs_of_pos (by positivity)]; apply le_of_eq; field_simp
 have he:f 0∈closedBall 0 J:= mem_closedBall_zero_iff.mpr hu.value
 have ha(i): G.curvature (W i)= t • f i:= (smul_inv_smul₀ h.ne' _).symm
 have hv: (fun i=> y (G.curvature (W i)))=fun i=> t^2 • y (f i):=funext fun i=>by unfold y; rw [ha,norm_smul,Real.norm_of_nonneg h.le,mul_pow]; rfl
 have hp:(fun i=> L (G.curvature (W i)))=fun i=> t^4 • L (f i):=funext fun i=>by unfold L; rw [ha]; apply homogeneous
 constructor
 · change Allows k (fun i=> y _) _ _; rw [hv]; convert (((H _ he).comp hu).smul (t^2)) using 1; rw [abs_of_pos (by positivity)]; apply mul_comm
 change Allows k (fun i=>L _) _ _; rw [hp]; apply Allows.mono (((V _ he).comp hu).smul (t^4)); change _*T≤T*_; rw [mul_comm T,abs_of_pos (by positivity)]; exact mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one h.le p (by decide)) hT
section
lemma capSize1 {G:Gauge}(k:ℕ):∃ v:ℝ,0≤v∧∀ {n:Side}(U:Config G n)(f: Face (Per n))(t:ℝ),0<t→t≤1→G.chord (faceValue U f)≤t→ Allows k (fun x:tandem G n=> G.mat (faceValue (βten t U x) f)-1) 0 (v*t):=by
 obtain ⟨C,H,w⟩:= tinder G k; let a:= C+‖(1:G.Mat)‖; let s:= G.colorScale; have hs:0<s:=G.colorScale_pos; refine ⟨max s a, hs.le.trans (le_max_left ..),@fun n U f t p h e=>?_⟩; let z(q: tandem G n):= G.mat (faceValue (βten 1 U q) f)-1; have hx: Allows k z 0 a:= minus_B (w U f) (allows_const _ (show ‖(1:G.Mat)‖ ≤_ from le_refl _))
 refine (pool z hx ?_ p h (le_max_right ..)).germ (Eventually.of_forall fun x=> (show z _=_ by unfold z; rw [tenorS]))
 unfold z; rw [tenor0]; apply le_trans _ (mul_le_mul_of_nonneg_right (le_max_left ..) p.le); rw [mul_comm]; exact (div_le_iff₀ hs).mp e
lemma corePrice (G:Gauge)(k:ℕ) (v:ℝ)(q:Clip):∃ C:ℝ,0≤C∧∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E](W:E→ G.El)(t:ℝ),0<t→t≤1→ (G.chord (W 0)≤ t) → Allows k (fun i=>G.mat (W i)-1) 0 (v*t) → Allows k (fun i=>G.price (W i)) 0 (C*t^2)∧Allows k (fun i=>Design.bulk q*surplus (G:=G) (W i)) 0 (C*t^2):=by
 -- reuse packed norm squared
 obtain ⟨X,Y,hx,hy,h⟩:= bone (d:=v) G k
 let s:= G.colorScale; let y(g:G.Mat):=‖g‖^2
 -- choose bound on G.Mat -1; explicit lemma via compact from register with frobInner
 have he: ContDiff ℝ ω y:=by
    letI := (Gauge.frobInner G.repDim); exact contDiff_norm_sq ℝ
 obtain ⟨R,v',H⟩:= exists_allows (f:=y) (isCompact_closedBall (0:G.Mat) (|v|)) (fun _ _=> he.contDiffAt) k
 let B:=composeCost k R |v|; let z:= ((s^2*2)⁻¹ :ℝ); let c₀:= |z| * B; let c₁:= c₀+1/2*X+Y; let P:=Design.bulk q; have hb:0≤B:=by unfold B composeCost; positivity
 refine ⟨max c₀ (|P| *c₁),(mul_nonneg (abs_nonneg _) hb).trans (le_max_left ..),@fun E _ _ W t p m e g=>?_⟩; have hk:= g.mono (show v*t ≤ |v| *t from mul_le_mul_of_nonneg_right (le_abs_self _) p.le); let J (i:E):= G.mat (W i)-1; let F(i:E):= t⁻¹ • J i
 have hu: Allows k F 0 |v|:=by
    apply Allows.mono (hk.smul t⁻¹); rw [abs_of_pos (by positivity)]; apply le_of_eq; field_simp
 have hf:F 0 ∈Metric.closedBall 0 |v|:= mem_closedBall_zero_iff.mpr hu.value -- tune
 have hp:Allows k (fun i=>G.price (W i)) 0 (c₀*t^2):=by
    have hz(i):z • (t^2 • y (F i))= G.price (W i):=by
       have hv:J i=t • F i:=(smul_inv_smul₀ p.ne' _).symm
       have hs:s≠0:=G.colorScale_pos.ne'; have hi: (‖J i‖/s)^2=2*G.price (W i):=G.chord_price _
       rw [hv,norm_smul,Real.norm_of_nonneg p.le] at hi; unfold y z; simp only [smul_eq_mul]; field_simp at hi ⊢; nlinarith only [hi]
    apply Allows.mono ((((H _ hf).comp hu).smul (t^2)).smul z|>.germ (Eventually.of_forall hz)); unfold c₀ B; rw [abs_of_pos (show 0<t^2 by positivity)]; apply le_of_eq; ring
 refine ⟨hp.mono (mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity)),?_⟩; obtain ⟨a,b⟩:= h W t p m e g; have hK: Allows k (fun i=>surplus (G:=G) (W i)) 0 (c₁*t^2):=by
    let Q(i):= (‖G.curvature (W i)‖^2)/2; have hh:Allows k Q 0 (1/2*X*t^2):=by
        refine Allows.mono ((a.smul (1/2)).germ (Eventually.of_forall fun i=>?_)) ?_
        · change 1/2* _= _/2; ring
        norm_num; exact le_of_eq (by ring) -- may no goals
    apply Allows.mono (minus_B (minus_B hp hh) b); apply le_of_eq; unfold c₁; ring
 apply Allows.mono (hK.smul P); rw [←mul_assoc]; exact mul_le_mul_of_nonneg_right (le_max_right ..) (sq_nonneg _)
abbrev faire (G:Gauge){n:Side}(q:Config G n)(f:Face (Per n)):= G.chord (faceValue q f)
private lemma orbiterZ(k:ℕ)(v:E→SU.group.El)(s:Allows k (fun i=> SU.group.mat (v i)-1) 0 c): Allows k (fun i=>SU.group.mat (Reef.qG (v i))-1) 0 c:=by
 let L:=Reef.chill
 have hh: Allows k (fun i=> L (SU.group.mat (v i)-1)) 0 (1*c):= s.linear L.toContinuousLinearMap L.norm_toContinuousLinearMap_le -- tune
 rw [one_mul] at hh; refine hh.germ (Eventually.of_forall fun i=>?_); change L _= _; rw [map_sub,show L 1 = 1 from cc_one]; rfl
lemma carves(k:ℕ)(q:Clip):∃ v:ℝ,0≤v∧∀ {n:Side}(U:Config SU.group n)(f:Face (Per n))(t:ℝ),0<t→t≤1→faire _ U f≤t→ Allows k (fun x: tandem SU.group n=> coinF q (faceValue (βten t U x) f)) 0 (v*t^2) ∧ Allows k (fun x:tandem SU.group n=> faire SU.group (βten t U x) f ^2) 0 (v*t^2):=by
 obtain ⟨v,H,K⟩:= capSize1 (G:=SU.group) k; obtain ⟨A,hB,P⟩:= corePrice SU.group k v q; let B:= A+A; refine ⟨B,add_nonneg hB hB,@fun n U f t p h q'=>?_⟩; let W(x:tandem SU.group n):= faceValue (βten t U x) f; let V(x:tandem SU.group n):= Reef.qG (W x); have he:SU.group.chord (W 0) ≤ t:=by unfold W; rw [tenor0]; exact q'
 have hx:SU.group.chord (V 0) ≤t:= by unfold V; rw [Reef.cool]; exact he
 have hz:=K U f t p h q'; obtain ⟨w,y⟩:=P W t p h he hz; obtain ⟨w',y'⟩:=P V t p h hx (orbiterZ k W hz); let z:= (minus_B w y).add (minus_B w' y'); constructor
 · refine Allows.mono ((z.smul (1/2)).germ (Eventually.of_forall (fun i=>?_))) ?_
   · change 1/2* (energyF q (W i) + energyF q (V i))= _/2; unfold V W; ring
   unfold B; rw [abs_of_pos (by norm_num)]; exact le_of_eq (by ring)
 refine Allows.mono ((w.smul 2).germ (Eventually.of_forall (fun i=>?_))) ?_
 · exact (SU.group.chord_price (W i)).symm
 unfold B; rw [abs_of_pos (by norm_num)]; apply le_of_eq; ring
end
end Shield
end YM.CF.XGarden
end
