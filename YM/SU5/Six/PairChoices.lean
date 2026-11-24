import YM.SU5.Six.SplitPredict
set_option autoImplicit false
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 300000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Six
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder ENNReal Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock
open Satin
attribute [local instance] opCStarAlgebra
open Mir Haro Tap Dial Cascade Girt Pastry
open Afterglow Tapestry Tower
variable (K:Calibration)
local notation "Ω"=> Dome K
/-!
Comparators given not as prices X but FROM arbitrary raw marginals.
Turn them into factoring predictions evaluated on the whole stencil, without
assuming any auxiliary linear extension compatibility hypothesis. (No claim
of lifting positivity/time dynamics.)
-/
lemma gauge_scaling(x:Ω)(c:ℂ)(p:PureGauge K x):PureGauge K (c • x):=by
 obtain ⟨S,f,g,t⟩:=p
 refine ⟨S,c • f,?_,?_⟩
 · exact ⟨fun t=>by contradiction,Girt.pole_w f (fun (x:ℂ)=> c • x) (by simp_rw [smul_eq_mul]; fun_prop) g.env,fun a x u p=>congrArg (fun x:ℂ=>c • x) (g.locus _ _ u p)⟩
 change c • x.val =_
 rw [t]; funext n w
 simp only [scalar,Pi.smul_apply,smul_smul,smul_eq_mul]
lemma gauge_plus(x y:Ω)(p:PureGauge K x)(q:PureGauge K y):PureGauge K (x+y):=by
 obtain ⟨S,f,g,t⟩:=p; obtain ⟨T,F,h,u⟩:=q
 refine ⟨S∪T,f+F,?_,?_⟩
 ·
   exact ⟨fun e=>by contradiction,Girt.kitE f F (·+·) (by fun_prop) g.env h.env,fun a b i j=>congrArg₂ (fun (x y:ℂ)=>x+y) ((g.mono subset_union_left).locus _ _ i j) ((h.mono subset_union_right).locus _ _ i j)⟩
 change x.val+y.val=_; rw [t,u]; funext n w
 simp only [scalar,Pi.add_apply,add_smul]
def gaugePlane : Submodule ℂ Ω where
 carrier :={x|PureGauge K x}
 zero_mem':= by apply (show (0:ℂ) • (1:Ω)=0 from zero_smul ℂ _) ▸ gauge_scaling K 1 0 (pure_unit K).1
 smul_mem' x y:= gauge_scaling K y x
 add_mem' {x y}:= gauge_plus K x y
def matterPlane : Submodule ℂ Ω where
 carrier:={x|PureMatter K x}
 zero_mem':=LinkIndependent.zero'
 add_mem' {x y} (h:LinkIndependent K x.val) (p:LinkIndependent K y.val):=h.plus' p
 smul_mem' x y (p:LinkIndependent K y.val):=p.scale' x

lemma onlyScalars {x:Ω} (h:PureGauge K x)(p:PureMatter K x): ∃ t:ℂ,x=t • 1:=by
 obtain ⟨S,f,h,w⟩:=h
 obtain ⟨m,e⟩:= (separates K S).exists
 let z:Fields (K.c m):=(1,1); let c:=f (onC (K.c m) z.1, onC (K.c m) z.2)
 have hg: InTest K true S false x.val:=w ▸ InTest.seed h
 have hv: x.val=c • (1:Buffered.Family K):= box_ext K S hg (InTest.smul c InTest.one) (m:=m) ⟨e⟩ (funext (fun t=>by
    rw [p m t z]
    rw [w]
    rfl))
 exact ⟨c,Subtype.ext hv⟩

private lemma linear_together (Y:Type)[AddCommGroup Y][Module ℂ Y]
    (U V:Submodule ℂ Y)(u:U→ₗ[ℂ]ℂ)(v:V→ₗ[ℂ]ℂ)(p:∀ (x:U)(y:V),x.val=y.val→u x=v y):
    ∃ W:Y→ₗ[ℂ]ℂ,W.comp U.subtype=u∧ W.comp V.subtype=v:=by
 let X:= U.subtype.coprod V.subtype; let Z:= u.coprod v; let T:=X.range; let f:=X.rangeRestrict
 obtain ⟨Y',w⟩:= LinearMap.exists_rightInverse_of_surjective f X.range_rangeRestrict
 obtain ⟨G,t⟩:= LinearMap.exists_leftInverse_of_injective T.subtype T.ker_subtype
 let W:= Z.comp (Y'.comp G)
 have he (z: U × V): W (X z)=Z z:= by
    have h (g: U × V)(e:X g=0): Z g=0:=by
       change u g.1 + v g.2= 0
       rw [p g.1 (-g.2) (eq_neg_of_add_eq_zero_left e),map_neg]; exact neg_add_cancel _
    have hp:T.subtype (f (Y' (G (X z))))=T.subtype (G (X z)):=congrArg T.subtype (LinearMap.congr_fun w (G (X z)))
    have hv:X (Y' (G (X z)))=X z:= hp.trans (congrArg Subtype.val (LinearMap.congr_fun t (f z)))
    have e:= h (Y' (G (X z))-z) (by rw [map_sub,hv,sub_self]); rw [map_sub] at e
    exact sub_eq_zero.mp e
 refine ⟨W, LinearMap.ext (fun i=>?_ ), LinearMap.ext (fun j=>?_)⟩
 · have h: W (U.subtype i+V.subtype 0)=u i + v 0:= he (i,0); simpa using h
 have h: W (U.subtype 0 + V.subtype j)=u 0+v j:= he (0,j); simpa using h

lemma any_marginal_pair
    (G:↥(gaugePlane K)→ₗ[ℂ]ℂ) (M:↥(matterPlane K)→ₗ[ℂ]ℂ)
    (p:G ⟨1,(pure_unit K).1⟩=1)(q:M ⟨1,(pure_unit K).2⟩=1):
    ∃ (X:Dome K→ₗ[ℂ]ℂ),X 1=1∧ X.comp (gaugePlane K).subtype=G ∧ X.comp (matterPlane K).subtype=M ∧ Factors K X:=by
 have h (x:gaugePlane K)(y:matterPlane K)(h:x.val=y.val): G x=M y:= by
   obtain ⟨t,v⟩:= onlyScalars K x.property (show PureMatter K x.val from Eq.mpr (congrArg (PureMatter K) h) y.property)
   have ht:x=t • (⟨1,(pure_unit K).1⟩: gaugePlane K):=Subtype.ext v; have hu:y=t • (⟨1,(pure_unit K).2⟩: matterPlane K):=Subtype.ext (h.symm.trans v)
   rw [ht,hu,map_smul,map_smul,p,q]
 obtain ⟨W,u,v⟩:= linear_together _ _ _ G M h
 have hx:W 1=1:= (LinearMap.congr_fun u (⟨1,(pure_unit K).1⟩: gaugePlane K)).trans p
 obtain ⟨X,e⟩:= comparison_exists K W hx
 exact ⟨X,e.unit K W hx,LinearMap.ext (fun i=>(e.link _ i.property).trans (LinearMap.congr_fun u i)),LinearMap.ext (fun i=>(e.matter _ i.property).trans (LinearMap.congr_fun v i)),e.factors⟩
-- Discrete cover Ward used in ReturnsSix on the prediction is exactly a test of these pure marginals.
lemma marginal_matter {X:Dome K →ₗ[ℂ]ℂ} (M:↥(matterPlane K)→ₗ[ℂ]ℂ)(h:X.comp (matterPlane K).subtype=M): MatterWard K X ↔
    ∀ (v:Cover→SU.E)(k:matterPlane K), M ⟨pennant K v k.val,ward_preserves_matter K v k.val k.property⟩=M k:= by
 subst M; constructor
 · intro p v k; exact p v k.val k.property
 exact fun p v k g=> p v ⟨k,g⟩
lemma marginal_gauge {X:Dome K →ₗ[ℂ]ℂ} (M:↥(gaugePlane K)→ₗ[ℂ]ℂ)(h:X.comp (gaugePlane K).subtype=M): GaugeWard K X ↔
    ∀ (v:Cover→SU.E)(k:gaugePlane K), M ⟨pennant K v k.val,pennantPure K v k.property⟩=M k:= by
 subst M; constructor
 · intro p v k; exact p v k.val k.property
 exact fun p v k g=> p v ⟨k,g⟩
#print axioms any_marginal_pair
end YM.CF.Buffered.Afterglow.Six
