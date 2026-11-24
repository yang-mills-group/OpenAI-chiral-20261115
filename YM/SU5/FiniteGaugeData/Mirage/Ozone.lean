import YM.SU5.FiniteGaugeData.Mirage.Parole
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 380000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Quest
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Heat Brique Window.Brique Journey Py Py.Rate LocalLimit Preparation FullBill Steam Vale
namespace Chaperone
open Tint
variable {K:Calibration}{σ τ:Window.Family}{U V S:Finset Cover}{F:Family K}{t:List Cover}
-- a key uses U for remover; still all Roomy; List repeats≤2 EXACTLY from physically transplanted marker. helper includes one-gen.
structure StencilB (K:Calibration)(σ τ :Window.Family)(U S:Finset Cover) (t:List Cover)(F:Family K):Prop where
 rear : U⊆ S
 front : ∀ x∈ t,nodeC x∈S
 walk : t≠[]
 access(x):t.count x≤2
 distant (x0: Cover)(p:x0∈t): nodeC x0∉U
 output : Seria K σ τ U S t F
 kin : Tint.Durable K F
namespace StencilB
variable {i:Axis} {l:ℕ} (c:StencilB K σ τ U S t F)
include c
lemma tierB : InTest K false S false F:= c.output.tier c.rear c.front
lemma availableB : F∈ Charm.well K:=⟨⟨⟨_,c.tierB.widen⟩,by simp⟩,c.kin⟩
omit c
lemma podia (p:Seria K σ τ U S t F)(u:S⊆V): Seria K σ τ U V t F:=by induction p with | ident=> exact .ident| zero t=> exact .zero _| add _ _ a b=> exact a.add b| scale _ _ a=> exact a.scale _| gauge _ W c a=> exact a.gauge W (c.mono u) | pair _ x y z i j a b q h e g ih=> exact ih.pair x y z i j a b q h e g
include c
lemma expanded (v:S⊆ V) : StencilB K σ τ U V t F:= {c with rear:= c.rear.trans v,front:= fun x p=> v (c.front x p), output:=podia c.output v}
omit c
lemma vista_from (p: Tableau K σ U S t F): Seria K σ σ U S t F:=by induction p with| ident=> exact .ident| zero t=> exact .zero _ | add _ _ a b=> exact a.add b| scale _ _ a=> exact a.scale _| gauge _ W c a=> exact a.gauge W c | pair _ x y z i j a b q h e g ih=> exact ih.pair x y z i j a b q h e g
lemma fromCopse (p:Copse K S U σ t F): StencilB K σ σ U S t F:= ⟨p.rear,p.front,p.walk,fun i=>(List.nodup_iff_count_le_one.mp p.strand _).trans (by decide),p.gap,vista_from p.output,p.coin⟩ -- tune API
private lemma count_map {V U:Type*}[DecidableEq V][DecidableEq U](t:List V)(x:V)(f:V→U)(h:∀ i∈ t,i≠x→ f i≠f x): (t.map f).count (f x)=t.count x:=by
 induction t with
 | nil=> simp
 | cons a t ih=> rw [List.map_cons,List.count_cons,List.count_cons,ih (fun i t u=> h i (List.mem_cons_of_mem a t) u)]; by_cases t:x=a; simp [t]; simp [t, Ne.symm t, h a List.mem_cons_self (Ne.symm t)] -- tune
include c
lemma light {n:Side} (h: Hosp S (K.c n))(y:Cover)(p:y∈t) (V:Fields (K.c n)): F n (simultaneous (lamp (wrap (K.c n) y)) V)=(SU.z^(powerS σ))^(t.count y) • F n V:=by
 rw [c.kin n]; let N:=K.c n; let f:=wrap N; let i:=f y; let A:= t.map f
 have hp(x:Cover)(x':x∈ t)(v:x≠y): f x≠ f y:=fun z=> v (nodeC_inj (h.seat_ (c.front x x') (c.front y p) ((node_of N x).symm.trans ((congrArg node z).trans (node_of ..)))))
 have hx:node i∉region U N:=by rw [node_of]; intro p'; obtain ⟨x,u,z⟩:= mem_image.mp p'; exact c.distant y p (h.seat_ (c.rear u) (c.front y p) z ▸ u)
 change flipsP (lamp i) _ =_; exact ((c.output.native n V).centerP i hx).trans (by rw [show A.count i=t.count y from count_map t y f hp]) -- tune
lemma rules {x:Cover} (p:x∈t) : (SU.z^(powerS σ))^(t.count x)≠1:= by
 intro v; rw [←pow_mul] at v; let V:= t.count x; have he:5∣powerS σ *V:= SU.z_prim.dvd_of_pow_eq_one _ v; unfold powerS at he; have hv:0<V:= List.count_pos_iff.mpr p; have hu:V≤ 2:= c.access _; split at he <;> omega
lemma anti (ν: ContinuousMap LinksC ℂ→ₗ[ℂ]ℂ)(s:Solitary S ν){n:Side}(p:Roomy S (K.c n))(M:FC (Single (K.c n))→ₗ[ℂ]ℂ): ν (soloC K S n F c.tierB M) = 0 := by
 obtain ⟨x,z⟩ := List.exists_mem_of_ne_nil _ c.walk; let N:= K.c n; let V:= soloC K S n F c.tierB M; let g:= lamp (wrap N x); let W:= fun a=> g (wrap (More N) a); let u:= (SU.z^(powerS σ))^(t.count x); let f:= F n; let h:= (InTest.support c.tierB n).dep; let p':=roomy_hosp _ p
 have he: Lattice.LocalOn S V:= by intro a b v; exact congrArg M (h (replant S N (a,a)) (replant S N (b,b)) (graft_agrees S p v) (graft_agrees S p v))
 have hv(a:LinksC): V (gauge W a)= u * V a:= by
    let b:= Satin.graft S N a; let b':= Satin.graft S N (gauge W a); have hb: Agrees (region S N) b' (gauge g b):=by
       rintro ⟨i,d⟩ r _; obtain ⟨j,k,rfl⟩:= mem_image.mp r; unfold b' b; rw [graft_at S p' _ k]; unfold Lattice.gauge; rw [graft_at S p' _ k]; unfold W; rw [map_add,wrap_step]
    change M (f (b',b')) = u * M (f (b,b)); rw [show f (b',b')= F n (simultaneous g (b,b)) from h _ _ hb hb,c.light p' x z,map_smul]; rfl
 change ν V=0; by_contra k; have hx:ν (u • V)=ν V:= s.shift W V _ he (fun v=>(hv v).symm); rw [map_smul,smul_eq_mul] at hx; apply c.rules z (mul_right_cancel₀ k (hx.trans (one_mul _).symm)) -- rewrite localon
end StencilB
-- boolean dyad genus (different flavor). output allow linear combos with same upper or lower own species.Challenges use same-generation α for persistent measurement, mixed 0,1. only same Weight.Actually predicate upper `σ` always.
inductive Haze (K:Calibration)(σ τ:Window.Family)(S:Finset Cover): Family K → Prop where
| oneB {F:Family K}{U:Finset Cover}{t:List Cover} : StencilB K σ σ U S t F → Haze K σ τ S F
| twoB {F:Family K}{U:Finset Cover}{t:List Cover} : StencilB K σ τ U S t F → Haze K σ τ S F
| plus {F G:Family K}: Haze K σ τ S F→ Haze K σ τ S G→Haze K σ τ S (F+G)
| mul {F:Family K}: Haze K σ τ S F→∀ z:ℂ,Haze K σ τ S (z•F)
-- cost.S.Reinterpretation.
namespace Haze
variable (c:Haze K σ τ S F)
include c
lemma funds : InTest K false S false F:=by induction c with| oneB c=> exact c.tierB| twoB c=>exact c.tierB| plus _ _ a b=> exact .add a b | mul _ _ a=> exact .smul _ a
lemma glow : Tint.Durable K F:=by induction c with| oneB c=> exact c.kin| twoB c=>exact c.kin | plus _ _ a b=> intro m g x; change _+_= twist _ ( _ + _); rw [a,b,map_add]| mul _ i a=> intro m g x; change i • _= twist _ (i • _); rw [a,twist_scalar]
lemma fits : F∈ Charm.well K:= ⟨⟨⟨_,c.funds.widen⟩,by simp⟩,c.glow⟩
lemma solos (ν: ContinuousMap LinksC ℂ→ₗ[ℂ]ℂ)(s:Solitary S ν){n:Side}(p:Roomy S (K.c n))(M:FC (Single (K.c n))→ₗ[ℂ]ℂ): ν (soloC K S n F c.funds M)=0:=by
 induction c with
 | oneB c=> exact c.anti ν s p M
 | twoB c=> exact c.anti ν s p M
 | @plus F Y a b ha hb=> rw [show soloC K S n _ _ M= (soloC K S n F a.funds M)+(soloC K S n Y b.funds M) from ?_,map_add, ha,hb,add_zero]; ext1 i; exact map_add M _ _
 | @mul F a z h=> rw [show soloC K S n _ _ M=z • (soloC K S n F a.funds M) from ?_, map_smul,h,smul_zero]; ext1 i; exact map_smul M _ _
end Haze
end Chaperone
end YM.CF.Buffered.Afterglow.Hierarchy.Quest
