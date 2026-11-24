import Anomaly.Cover.Collection
import YM.SU5.FiniteGaugeData.Tower.Baggage
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option maxHeartbeats 500000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tapestry.StageW
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open CF.Swell Rill CF.Swell.Sonar
open Py Py.Rate LocalLimit Preparation Journey Vale FullBill
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) (H:Real.exp 1≤Λ.x) (s i:ℕ)
variable (S:Finset Cover) (K:Calibration) {f:Family K}{N:Side}{g:Mark N}
def Licor (S:Finset Cover)(K:Calibration)(f:Family K): Prop:=∃ φ:LinksC→ℂ,Coeff true S (φ ∘ Prod.fst) ∧ f=scalar K (φ ∘ Prod.fst)
def spotless {N:Side}(g:Mark N):Prop:=∃ φ:Pane N→ℂ, ∀ x:Fields N,g x=φ x.1 • 1
lemma spotlessD (u:Licor S K f)(N:Side):spotless (f N):=by obtain ⟨p,_,v⟩:=u; rw [v]; exact ⟨p ∘ onC _,fun _=>rfl⟩
lemma symbolP (i:Finset (Single N))(u:spotless g)(x:Fields N): g x=g (x.1,1) i i • 1:=by obtain ⟨φ,v⟩:=u; rw [v (x.1,1),v x]; apply congrArg (fun z:ℂ=> z • _); simp
lemma spotless_license (m:Side)(p:InTest K true S false f)(t:Roomy S (K.c m))(u:spotless (f m)): Licor S K f:=by
 let G:=f m; let N:=K.c m; let i:Finset (Single N):= ∅
 let V(X:Pane N):Fields N:=(X,1); let Tip(A:FC (Single N)):= A i i; let h:=p.support m
 let Φ:= Tip ∘ G ∘ V ∘ graft S N
 have hx:Envelope (Φ∘Prod.fst (β:=LinksC)):= Env.along (Env.along (Girt.pole_w (Y:=ℂ) G Tip (by unfold Tip; fun_prop) h.env) (show Measurable (V∘ graft S N) from ((by unfold V; fun_prop : Measurable V).comp (graft_b ..)))) measurable_fst -- params tune
 have hΦ:Coeff true S (Φ ∘ Prod.fst):=⟨fun _=>by contradiction,hx,fun i j hi _=>?_⟩; rotate_left 1
 · exact congrArg Tip (h.dep (V (graft S N i.1)) (V (graft S N j.1)) (tack S N t _ _ hi) (fun i _ _=>rfl))
 refine ⟨Φ,hΦ,looksLike (m:=m) (Roomy.seats t) p (InTest.seed hΦ) (?_)⟩
 funext x; change G x=Φ (onC _ x.1) • _; rw [show G x=G (V x.1) i i •1 from symbolP _ u _]; exact congrArg (fun x=> Tip x •1) (h.dep (V x.1) (V (graft S N (onC N x.1))) (fun i l m=> (untack S N (Roomy.seats t) x.1 i l m).symm) (fun i _ _=>rfl))
 -- tactic to fill hx
 all_goals first| exact (continuous_apply _).comp _ | exact ((by fun_prop : Measurable V).comp (graft_b S N))
variable {K S}
lemma heirs {m n:Side} (p:m=n)(f:Mark m)(v:spotless (arrange _ _ p f)): spotless f:=by subst_vars; exact v
lemma fresh_S {x:Family (tent Y H)}(p: Roomy S (side Y i s))(w:InTest (tent Y H) true S false x)(t:spotless (exhibit Y H s i x)):Licor S (tent Y H) x:= spotless_license _ _ (momentm Y i s) w ((terrain Y H (Y.ir i) s).symm ▸ p) (heirs (terrain ..) _ t) -- tune inference sees p.sizes
open Tower Tower.SlabMark
lemma queue_V (K:Calibration){F:ℕ→Swatch S}{f:Swatch S}(h:Tendsto F atTop (𝓝 f)):BQueue S (fun i=>render S K (F i)) (render S K f):=by
 let u:=‖f‖+1; have hu:‖f‖<u:= lt_add_one _; let S':=spread S+1; have h0:0≤ spread S:=Nat.cast_nonneg _; have hp:spread S < S':=lt_add_one _; have hS:0<S':=h0.trans_lt hp; refine ⟨fun i=>texture ..,texture ..,⟨S'*u,mul_pos hS ((norm_nonneg _).trans_lt hu),fun m x=>(renderLe ..).trans (mul_le_mul hp.le hu.le (norm_nonneg _) hS.le), (h.norm.eventually (ge_mem_nhds hu)).mono fun i v m x=>(renderLe ..).trans (mul_le_mul hp.le v (norm_nonneg _) hS.le)⟩,fun ε e=> ?_⟩
 filter_upwards [Metric.tendsto_nhds.mp h _ (div_pos e hS)] with i hi m x; change ‖((render S K) _-_) m x‖≤ _; rw [←map_sub]; rw [dist_eq_norm] at hi; exact (renderLe ..).trans ((mul_le_mul hp.le hi.le (norm_nonneg _) hS.le).trans_eq (by field_simp))
lemma carriesC {F:ℕ→Family K}{f:Family K}(u:BQueue S F f)(m:Side)(x:Fields (K.c m)):Tendsto (fun i=>F i m x) atTop (𝓝 (f m x)):=Metric.tendsto_nhds.mpr fun ε e=> (u.saved (ε/2) (half_pos e)).mono fun i p=> (dist_eq_norm ..).trans_lt ((p m x).trans_lt (half_lt_self e))
lemma licor_q {F:ℕ→Family K}{f:Family K}(u:BQueue S F f)(h:∀ i,Licor S K (F i)): Licor S K f:=by
 obtain ⟨n,t⟩:= ((separates K (tips S)).mono fun i p=> (show Roomy S (K.c i) from ⟨p⟩)).exists
 refine spotless_license _ _ n u.landing t ⟨fun y=>f n (y,1) ∅ ∅,fun x=> ?_⟩
 have hc:Continuous (fun Y:FC (Single (K.c n))=>Y ∅ ∅ • (1:FC (Single (K.c n)))):=by fun_prop
 exact tendsto_nhds_unique_of_eventuallyEq (carriesC u n x) (hc.continuousAt.tendsto.comp (carriesC u n (x.1,1))) (Eventually.of_forall fun i=>symbolP _ (spotlessD S K (h i) n) x)
end YM.CF.Buffered.Afterglow.Tapestry.StageW
