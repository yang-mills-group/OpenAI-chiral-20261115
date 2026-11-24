import YM.SU5.FiniteGaugeData.Eight.Gauge
import YM.SU5.FiniteGaugeData.Mirage.Retina
import YM.SU5.FiniteGaugeData.Steam.Contest
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
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
open Heat Quest Fock.Brique
section
-- order: resource concept to track paying in Full AND Empty channels, transposes under reflection. Documentary for others too (Glints). money represented at Leaf only.
structure Literature (N:Side) where
 quota: ℕ→ℕ→Support (More N)→ Mark N→Prop
 ice : ∀ a z {n m S x},quota n m S x→ quota m n (S.image ((Buffered.plane a z).anon _)) (Buffered.reflMark a z x)
 melt: ∀ {n m u v S T x y}, quota n m S x→quota u v T y→AtSupport false S x→ AtSupport false T y→Disjoint S T→quota (n+u) (m+v) (S∪ T) (x*y)
 scale: ∀ {n m S x}, quota n m S x→∀ c:ℂ, quota n m S (c•x)
 monoP: ∀ {n m S x}, quota n m S x→∀ T, S⊆ T→quota n m T x
 unit:∀ S, quota 0 0 S 1
private lemma scale_C {n w:ℕ}{z c:ℝ}{T:Peg N}{b:Bool}{x:Mark N}(p:Crater w z c T S x n b)(k:ℂ): Crater w z c T S (k•x) n b:= ⟨fun i t h=>by
   obtain ⟨A,y,S',v,g,j,xn,D⟩:= p.once i t (fun e=>h (by rw [Pi.smul_apply,e,smul_zero])); refine ⟨A,y,S',v,g,j,fun t x'=>?_,D⟩; rw [Pi.smul_apply,star_smul,act_smul,map_smul,xn _ x',smul_zero]⟩
private lemma more_C {n w:ℕ}{z c:ℝ}{T:Peg N}{b:Bool}{x:Mark N}(p:Crater w z c T S x n b){U:Support (More N)}(v:S⊆U):Crater w z c T U x n b:= ⟨fun i t h=>by
   obtain ⟨A,y,S',u,f,g,z⟩:= p.once i t h; exact ⟨A,y,S',u.trans v,f,g,z⟩⟩
def novella (w:ℕ)(z c:ℝ)(V:Peg N)(p:0≤c): Literature N where
 quota n m S x:= Crater w z c V S x n false ∧ Crater w z c V S x m true
 ice a z {n m S x} v:= ⟨v.2.reflects a z,v.1.reflects a z⟩ -- implicit pattern syntax issue _? usually supports implicit binder?
 melt {n m u v S T x y} v w x y h:= ⟨(v.1.merger x w.1 y h),(v.2.merger x w.2 y h)⟩
 scale {n m S x} v z:= ⟨scale_C v.1 z,scale_C v.2 z⟩
 monoP {n m S x} v T u:= ⟨more_C v.1 u,more_C v.2 u⟩
 unit _:=⟨Crater.trivial p 1,Crater.trivial p 1⟩
private lemma glintPlus {z:ℝ} {n m:ℕ} {T:Support (More N)}{x y:Mark N}(p:Glints n S z x)(q:Glints m T z y)(v:Disjoint S T):Glints (n+m) (S∪ T) z (x*y):=by
 intro i t; let a(R:Support (More N)):=glitches R z i.1; let b:=a S; let c:=a T
 have he: Disjoint b c:= by
    refine Finset.disjoint_left.mpr (fun i e f=> Finset.disjoint_left.mp v (((mem_filter.mp e).2) (Work.E01.base_touched _)) (((mem_filter.mp f).2) (Work.E01.base_touched _)))
 have hx(B S:Support (More N))(u:B⊆ S):a B⊆a S:= fun i h=>mem_filter.mpr ⟨(mem_filter.mp h).1,Subset.trans ((mem_filter.mp h).2) u⟩
 calc
 _ ≤ b.card+c.card:= Nat.add_le_add (p i (left_ne_zero_of_mul t)) (q i (right_ne_zero_of_mul t))
 _ ≤ _:= by rw [← Finset.card_union_of_disjoint he]; exact card_le_card (union_subset (hx _ _ subset_union_left) (hx _ _ subset_union_right))

def fairy (z:ℝ)(N:Side): Literature N where
 quota n m S x:=Glints (n+m) S z x
 ice a s {n m S x} p:=by
    rw [add_comm m n]; intro i h; exact (p (reflFields a s i) (fun e=> h (by unfold reflMark; rw [e,theta_zero]))).trans (glint_gloss ..)
 melt {n m u v S T x y} a b _ _ t:= (show n+u+(m+v)=n+m+(u+v) by omega) ▸ glintPlus a b t
 scale {n m S x} v z:=fun i t=> v i (fun e=>t (by rw [Pi.smul_apply,e,smul_zero]))
 monoP {n m S x} v T u := fun i t=> (v i t).trans (card_le_card (show glitches S z i.1⊆ glitches T z i.1 from fun i h=>mem_filter.mpr ⟨(mem_filter.mp h).1,Subset.trans ((mem_filter.mp h).2) u⟩))
 unit _ _ _:= Nat.zero_le _

variable {d n m j t r:ℕ} {X:Type}[MeasurableSpace X]{μ:Measure X}[IsProbabilityMeasure μ]{a: X→ Mark N}
private lemma pay_B (q:Measurable (uncurry a))(t:∀ i z, ‖a i z‖ ≤ C)(z:Fields N): Integrable (fun x=> a x z) μ:= Integrable.of_bound q.of_uncurry_right.aestronglyMeasurable C (Eventually.of_forall fun x=> t x z)
-- Hull on AE of actual LUT dual Fields only (projection issue).
structure Hull (P:Loom N)(V: Literature N)(n m:ℕ)(C:ℝ)(S: Support (More N))(x:Mark N) : Prop where
 coast: ∃ (X:Type)(_ : MeasurableSpace X)(μ:Measure X)(_ : IsProbabilityMeasure μ)(a:X→ Mark N), Measurable (uncurry a) ∧ (∀ i z, ‖a i z‖ ≤ C) ∧ (∀ i,AtSupport false S (a i) ∧ V.quota n m S (a i)) ∧ ∀ᵐ i∂city N, x (drawn P i)= ∫ j,a j (drawn P i)∂μ
variable {P:Loom N}{V:Literature N}{k v y c:ℝ}{x g:Mark N}
protected lemma Hull.trig (tV:V.quota n m S x) (u:AtSupport false S x)(p:∀ i, ‖x i‖ ≤ C):Hull P V n m C S x:=by
 let μ:Measure Unit:=Measure.dirac (); haveI: IsProbabilityMeasure μ:= by unfold μ; infer_instance
 exact ⟨⟨Unit,inferInstance,μ,inferInstance,(fun _:Unit=>x),u.env.meas.comp measurable_snd,(fun _=>p), (fun _=>⟨u,tV⟩),Eventually.of_forall (fun i=> by simp only [integral_const,probReal_univ,one_smul])⟩⟩
lemma Hull.base (S:Support (More N)): Hull P V 0 0 1 S 1:=by
 apply Hull.trig (x:=1) (V.unit _) (.oneM _) (fun x=> by change ‖(1:FC _)‖ ≤ _; rw [norm_one])
lemma Hull.dew (t':0≤ v){a:ℕ}{T: Peg N}{x_x x_v:ℝ}(p:Casing N T.e (T.Ft false) c C y)(K₀:Roof N x_x x_v r P) -- c₀ different
 (u:Crater a k v T S x n false)(e: (∀ i: Orbit N, x (drawn P i)=g (drawn P i))) (p':AtSupport false S x){M:ℝ} (q:∀ i, ‖x i‖≤M):Hull P (novella a k v T t') n 0 M S (dewG N g):=by
 refine ⟨⟨_,_,areaG N,inferInstance,actionG N x,Dew p',fun h=>peso h q,fun h=> ⟨epochG h p',Crater_right h p u,Crater.trivial t' _⟩,?_⟩⟩
 apply Eventually.of_forall; intro i; unfold dewG; apply integral_congr_ae; filter_upwards with j; simp_rw [actionG,drawGraft j⁻¹ K₀ i, e]
-- warnings different cost params & Roof bounds. need separate.
lemma Hull.scale (q:Hull P V n m C S x)(z:ℂ) : Hull P V n m (‖z‖*C) S (z•x):= by
 obtain ⟨X,i,μ,J,a,A,u,g,w⟩:=q.coast; refine ⟨⟨X,i,μ,J,fun t=>z • a t, (measurable_const.smul A), (fun i p=> (norm_smul z (a i p)).trans_le (mul_le_mul_of_nonneg_left (u i p) (norm_nonneg z))), fun t=> ⟨(g t).1.smulM z,V.scale (g t).2 z⟩, w.mono (fun i hx=>?_ )⟩⟩ -- DSP
 simp_rw [Pi.smul_apply,hx,integral_smul]
lemma Hull.expand (q: Hull P V n m C S x)(T:Support (More N))(v:S⊆ T): Hull P V n m C T x:=by
 obtain ⟨X,i,μ,J,a,A,u,f,w⟩:=q.coast; exact ⟨⟨X,i,μ,J,a,A,u,(fun i=> ⟨(f i).1.mono v,V.monoP (f i).2 T v⟩), w⟩⟩
private def Tht (a:Axis)(z:ℤ)(N: Side):FC (Single N)→L[ℝ]FC (Single N):= LinearMap.toContinuousLinearMap (⟨⟨theta (carR a z N),theta_add _⟩, fun c t=> theta_rsmul (carR a z N) t c⟩ : FC (Single N)→ₗ[ℝ]FC (Single N))
lemma Hull.turn (e:Roof N c k r P) (w:Axis)(h:ℤ)(p:Hull P V n m C S x): Hull P V m n C (S.image ((Buffered.plane w h).anon N)) (Buffered.reflMark w h x):=by
 let B:= Tht w h N; obtain ⟨X,i,μ,J,a,A,u,g,Hw⟩:=p.coast; have hx: Measurable (fun i:X × Fields N=> a i.1 (reflFields w h i.2)) := A.comp (measurable_fst.prodMk ((Continuous.measurable (Continuous.prodMap (fling_cont (n:=N) w h) (fling_cont (n:=N) w h))).comp measurable_snd))
 refine ⟨⟨X,i,μ,J,fun t=> Buffered.reflMark w h (a t), B.continuous.measurable.comp hx,fun t y=> (theta_fee ..).trans_le (u t _), fun t=>⟨(g t).1.refl w h,V.ice _ _ (g t).2⟩,?_⟩⟩
 filter_upwards [roof_move P w h e,(reflOrbit_mp (N:=N) w h).quasiMeasurePreserving.ae Hw] with η z L
 let K:= reflFields w h (drawn P η); change B (x K)=∫ i, B (a i K) ∂μ; change drawn P _= K at z; rw [←z, (show x _= _ from L),ContinuousLinearMap.integral_comp_comm B (pay_B A u _)] -- orientation
lemma Hull.join {T:Support (More N)}(q:Hull P V n m C S x)(t':Hull P V j t v T g)(e:0≤C)(d:0≤v)(W: Disjoint S T): Hull P V (n+j) (m+t) (C*v) (S∪ T) (x*g):=by
 obtain ⟨X,i,μ,J,a,A,u,f,w⟩:=q.coast; obtain ⟨Y,i',ν,J',b,bK,y,f',w'⟩:= t'.coast; let G: X×Y→ Mark N:= fun t=> a t.1 *b t.2
 have hG: Measurable (uncurry G):= by
    refine (show Measurable (fun i:(X×Y)×Fields N=> a i.1.1 i.2 * b i.1.2 i.2) from Measurable.mul (A.comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)) (bK.comp ((measurable_snd.comp measurable_fst).prodMk measurable_snd))) -- tune
 have tG(i:X×Y)(z:Fields N):‖G i z‖ ≤ C*v:= (norm_mul_le ..).trans (mul_le_mul (u i.1 z) (y i.2 z) (norm_nonneg _) e)
 refine ⟨⟨X×Y,inferInstance,(μ.prod ν),inferInstance,G,hG,tG,fun i=> ⟨((f i.1).1.mono subset_union_left).mulM ((f' i.2).1.mono subset_union_right), V.melt (f i.1).2 (f' i.2).2 (f i.1).1 (f' i.2).1 W⟩,?_⟩⟩
 filter_upwards [w,w'] with t ht ht'; let Z:=drawn P t; have he:= pay_B (μ:=μ.prod ν) hG tG Z
 rw [integral_prod _ he,Pi.mul_apply,ht,ht']; change _=∫ x, (∫ y,(a x Z*b y Z)∂ν) ∂μ; simp_rw [integral_const_mul_of_integrable (pay_B (μ:=ν) bK y Z), integral_mul_const_of_integrable (pay_B (μ:=μ) A u Z)]; rfl -- tune
end
#print axioms Hull.join
#print axioms Hull.dew
section
variable {n j k r d w u:ℕ} {x y:Mark N}{c v:ℝ}{Z:Loom N}{V: Literature N}{T:Support (More N)}{s B:Side}
lemma Hull_mirror (p:Roof N c v d Z)(y':Margin s r k w u)(h:Mirror B u N S x T y n)(v:0 ≤ C)(g:Hull Z V j j C S x): Hull Z V (n*j) (n*j) (C^n) T y:= by
 induction h generalizing j C with
 | self => simpa using g
 | @grow S F a z b=>
   let T:= Heat.gaugeShift B z; have he:Disjoint (S.image ((Buffered.plane a T).anon N)) S:= by
      refine Finset.disjoint_left.mpr ?_; intro y e f; have he:= margin_separate a T y' y y (Finset.image_subset_image (f:=(Buffered.plane a T).anon N) b e) (b f); simp at he
   rw [two_mul,pow_two]; exact (g.turn p a T).join g v v he
 | @trans _ _ _ _ _ _ m s e h a b => rw [pow_mul,show m*s*j=s*(m*j) from (by ring)]; exact b (pow_nonneg v _) (a v g)
end
open Journey Py Py.Rate LocalLimit Preparation FullBill Steam Vale
private def right_B (Y:Phys N) : FC (Single N) →L[ℝ] ℂ := by
 let H : FC (Single N)→ₗ[ℂ]ℂ:=⟨⟨fun v=>letterRead v Y,fun a b=>by simp only [letterRead, ContinuousLinearMap.comp_apply]; rw [act_add,map_add] ⟩,fun c t=>by simp only [letterRead,ContinuousLinearMap.comp_apply]; rw [act_smul,map_smul]; rfl⟩
 exact H.toContinuousLinearMap.restrictScalars ℝ
lemma integrateB (P:Loom N)(Q:Orbit N→Phys N)(U: Literature N)(t:Measurable (drawn P)) (f:Envelope Q){x:Mark N} {n m:ℕ}(p:Hull P U n m C S x){D:ℂ}{a:ℝ}(X:∀ (g:Mark N), (∀ i, ‖g i‖ ≤ C) → AtSupport false S g→ U.quota n m S g → ‖markedRead g P Q / D‖≤ a) : ‖markedRead x P Q / D‖≤ a := by
 obtain ⟨Y,j,μ,J,A,g,v,y,z⟩:=p.coast; let V(i:Y×Orbit N):= letterRead (A i.1 (drawn P i.2)) (Q i.2); have ht: Integrable V (μ.prod (city N)):=by
    refine Env.integrableX (env_letterRead ⟨g.comp (measurable_fst.prodMk (t.comp measurable_snd)),C,(fun i:Y×Orbit N=> v _ _)⟩ (Env.along f measurable_snd)) _
 have hw: markedRead x P Q /D=∫ i:Y, (markedRead (A i) P Q /D) ∂μ:=by
    unfold markedRead; rw [integral_div]; change _=(∫ i,∫ j,V (i,j)∂city N ∂μ)/D; rw [←integral_prod V ht,integral_prod_symm V ht]; refine congrArg (fun v:ℂ=> v /D) (integral_congr_ae (z.mono fun i t=>?_)); change right_B (Q i) (x (drawn P i))=_; rw [t,← ContinuousLinearMap.integral_comp_comm _ (pay_B g v (drawn P i))]; rfl
 rw [hw]; exact (norm_integral_le_of_norm_le (integrable_const a) (Eventually.of_forall fun i=> X (A i) (v i) (y i).1 (y i).2)).trans (by simp)
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(s i k:ℕ)
local notation "ℓ"=> side Y i s
local notation "Q"=> (Y.voyage i).CapeT s
local notation "Ψ"=> Journey.compass Y i k s
variable {U:Literature (side Y i s)} {θ:ℝ}{x:Mark (side Y i s)}{T:Support (More (side Y i s))} {n m:ℕ}
lemma supply (e:MarkGate Y s i k)(p:Hull ((Y.voyage i).CapeT s) U n m C T x)(w:∀ (x:Mark (side Y i s)), (∀ i,‖x i‖ ≤ C) → AtSupport false T x → U.quota n m T x → ‖(Ψ) x‖ ≤ θ): ‖(Ψ) x‖ ≤ θ:=by
 let h:= (Y.each_level i k s e.1 e.2); exact integrateB Q _ U (drawn_m _ ((Y.voyage i).ownership s).paid.bill) h.permits p (D:= partitionZ (((Y.voyage i).X (Y.uv k)).gram s) Λ.U Q) w -- α if unused E autoparam drop
#print axioms supply
end YM.CF.Buffered.Afterglow.Hierarchy.Eight
