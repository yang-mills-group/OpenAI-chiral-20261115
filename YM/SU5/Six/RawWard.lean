import YM.SU5.Six.CoverLetters
import YM.SU5.FiniteGaugeData.Tapestry.Oriflamme
/-! # Exactly which factorization is tested

Use pure raw *both Pane* scalar marks, and the pure even matter-word
polynomials on the Dome (including their linear extension). Ward on either
pure algebra suffices. These are one-level comparisons, at every fine
consultation; NOT testing factorization in dressed/gauge-fixed variables.
-/
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
local notation "A"=> Dome K

def PureGauge (x:A): Prop := ∃ (S:Finset Cover)(f:PairsC→ℂ), Coeff true S f∧ x.val=scalar K f
def PureMatter (x:A): Prop := LinkIndependent K x.val
lemma pure_unit : PureGauge K 1 ∧ PureMatter K 1:= ⟨⟨∅,_,ice,unitLink.symm⟩, LinkIndependent.one'⟩

-- Identification as the bare (signed-lattice) EVEN matter algebra, no scalar gauge legs.
lemma wordIndependent (L:Chorus): LinkIndependent K (Sound.sing K L):= by
  induction L with
  | nil=>exact LinkIndependent.one'
  | cons i t h=>
    have he:LinkIndependent K (Sound.chord K i):= by unfold Sound.chord; split <;> exact fun _ _ _=>rfl
    exact he.mul' h
lemma linkIndependent_iff (S:Finset Cover){f:Buffered.Family K}(h:InTest K true S false f) :
    LinkIndependent K f ↔ f ∈ Submodule.span ℂ {F|∃ t:Evens S, F= Sound.sing K (tagWord S t.val)} := by
  let P:=Submodule.span ℂ {F| ∃ t:Evens S,F=Sound.sing K (tagWord S t.val)}
  constructor
  · intro v
    obtain ⟨X,e⟩:= circulation S K h
    -- Evaluate all scalars at identity links on every side (same constant).
    let C:=fun t:Evens S=> (X t).val (1,1)
    have hw:f=∑ i:Evens S,C i • Sound.sing K (tagWord S i.val):=by
      funext m x
      calc f m x= f m (1,1):= v m x _
           _ = _:= by
             rw [e]; simp_rw [Finset.sum_apply,note_v]
             apply sum_congr rfl
             intro i _
             have hv := wordIndependent K (tagWord S i.val) m (1,1) x
             have hp (n: Side):Lifted.onC n 1=1:=rfl
             simp only [hv, Prod.map_apply,hp]; rfl
    rw [hw]; exact P.sum_mem fun i _=> P.smul_mem _ (Submodule.subset_span (show _∈ _ from ⟨i,rfl⟩))
  intro p
  refine Submodule.span_induction (p:=fun f _=> LinkIndependent K f) (fun f e=>?_) LinkIndependent.zero' (fun _ _ _ _ p q=> p.plus' q) (fun c _ _ h=> h.scale' c) p
  obtain ⟨t,rfl⟩:=e; exact wordIndependent K _

def Factors (X:A→ₗ[ℂ]ℂ) := ∀ f g:A,PureGauge K f→PureMatter K g→ X (f*g)=X f * X g
def MatterWard (X:A→ₗ[ℂ]ℂ) := ∀ (g:Cover→SU.E)(f:A), PureMatter K f→ X (pennant K g f)=X f
def GaugeWard (X:A→ₗ[ℂ]ℂ) := ∀ (g:Cover→SU.E)(f:A), PureGauge K f→ X (pennant K g f)=X f

variable {x y:Dome K}
lemma gaugePure_mul (h:PureGauge K x)(p:PureGauge K y):PureGauge K (x*y):= by
  obtain ⟨S,f,h,r⟩:=h; obtain ⟨T,g,p,q⟩:=p
  refine ⟨S∪T,f*g,tone (h.mono subset_union_left) (p.mono subset_union_right),?_⟩
  change x.val * y.val = _; rw [r,q]
  funext m z; simp only [Pi.mul_apply,scalar,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,one_mul,smul_smul]; rw [mul_comm]
lemma matterPure_mul (h:PureMatter K x)(p:PureMatter K y) : PureMatter K (x*y):= (show LinkIndependent K x.val from h).mul' p
-- Lift a pure scalar precisely
variable (S:Finset Cover) (g:Cover→SU.E)
lemma pennantPure (p:PureGauge K x):PureGauge K (pennant K g x):= by
  obtain ⟨S,u,p,e⟩:=p
  let W:=fun x:LinksC=> Lattice.gauge g x
  have hw: Continuous W:= by
    unfold W; apply continuous_pi; intro i; unfold Lattice.gauge; fun_prop
  let f:=u ∘ Prod.map W W
  have hg (x y:LinksC)(p:Agrees S x y):Agrees S (W x) (W y) := by intro i q v; unfold W Lattice.gauge; rw [p i q v]
  have he: Coeff true S f :=
    { env:= Env.along p.env (hw.measurable.prodMap hw.measurable)
      narrow:=fun t=>by contradiction
      locus:=fun _ _ a b=> p.locus _ _ (hg _ _ a) (hg _ _ b) }
  let y:A:= ⟨scalar K f, broadCompile K S (.seed he)⟩
  have h: Circular S g x.val y.val := by
    rw [e]
    intro m G h v; change u _ • (1:FC _)=twist (quantU _) (_ • (1:FC _)); rw [twist_scalar,map_one]
    exact congrArg (fun (z:ℂ)=> z • (1:FC _)) (p.locus _ _ (gauge_trace g h v.1) (gauge_trace g h v.2))
  have ht:pennant K g x=y:=appointed K S g x y h (show InTest K true S false y.val from .seed he)
  exact ⟨S,f,he,congrArg Subtype.val ht⟩
lemma fixed_local (r:∀ i∈S,g i=1)(h:x∈bay K S true) : pennant K g x=x:= by
  have he:= pennantTrace K S (1:Cover→SU.E) h; rw [pennantId] at he
  exact appointed K S g x x (fun n b p=> he n b fun i v=> (p i v).trans (r i v)) h

variable (θ:ℂ)
def illuminated : Submodule ℂ A := Submodule.span ℂ {x|∃ f b:A, PureGauge K f ∧ PureMatter K b ∧ pennant K g b=θ • b ∧ x=f*b}
lemma fixed_illumined (r:∀ i∈S,g i=1){f:A}(p:f∈bay K S true) : f∈ illuminated K g 1:=by
  obtain ⟨X,h⟩:=circulation S K ((locates ..).1 p)
  let L(i:Evens S):=tagWord S i.val
  have ht(i:Evens S): InTest K true S false (Sound.sing K (L i)):=i.property ▸ sung K (L i) (Satin.brand S _)
  let b(i:Evens S): A:= ⟨Sound.sing K (L i), broadCompile K S (ht i)⟩
  let a(i:Evens S):A:= ⟨scalar K (X i).val,broadCompile K S (.seed (X i).property)⟩
  let v:=∑ i:Evens S,a i*b i
  have hv:f=v:= by
    apply Subtype.ext
    exact h.trans (map_sum (screenHall K).val (fun i:Evens S=>a i*b i) univ).symm -- argument inference?
  rw [hv]; refine Submodule.sum_mem _ fun i _=>Submodule.subset_span (show _∈_ from ⟨a i,b i,⟨S,(X i).val,(X i).property,rfl⟩,wordIndependent K _,(fixed_local K S g r (x:=b i) (ht i)).trans (one_smul ..).symm,rfl⟩)

lemma illuminated_mul (p:x∈ illuminated K g θ)(h:y∈illuminated K g 1) : x*y∈ illuminated K g θ:=by
  let Q:=illuminated K g θ
  refine Submodule.span_induction (p:=fun x _=>x*y∈Q) (fun x w=>?_) (by rw [zero_mul]; exact Q.zero_mem) (fun _ _ _ _ p q=>by rw [add_mul]; exact Q.add_mem p q) (fun a _ _ p=>by rw [smul_mul_assoc]; exact Q.smul_mem a p) p -- `Algebra.`
  refine Submodule.span_induction (p:=fun y _=>x*y∈Q) (fun y p=>?_) (by rw [mul_zero]; exact Q.zero_mem) (fun _ _ _ _ p q=>by rw [mul_add]; exact Q.add_mem p q) (fun a _ _ p=>by rw [mul_smul_comm]; exact Q.smul_mem a p) h
  obtain ⟨f,b,p,q,s,rfl⟩:=p; obtain ⟨F,B,u,v,t,rfl⟩:=w
  refine Submodule.subset_span (show _∈_ from ⟨F*f,B*b,gaugePure_mul K u p,matterPure_mul K v q,?_,mul_mul_mul_comm ..⟩)
  rw [map_mul,t,s,one_smul,smul_mul_assoc]

section kill
variable (X:Dome K →ₗ[ℂ]ℂ) (F:Factors K X) (h:θ≠1)
include F in
private lemma pays_gauge (W:GaugeWard K X)(p:x∈illuminated K g θ): X (pennant K g x)=θ * X x:= by
  refine Submodule.span_induction (p:=fun x _=> X (pennant K g x)=θ * X x) (fun z h=>?_) (by rw [map_zero,map_zero,mul_zero]) (fun x y _ _ hx hy=>by rw [map_add,map_add,map_add,hx,hy,mul_add]) (fun a v _ e=>by rw [map_smul,map_smul,map_smul,e]; simp only [smul_eq_mul]; ring) p
  obtain ⟨f,b,r,t,e,rfl⟩:=h
  rw [map_mul,e,mul_smul_comm,map_smul,F _ _ (pennantPure K g r) t, F _ _ r t,W _ _ r]; rfl
include F h
lemma marginal_zero (w:MatterWard K X ∨ GaugeWard K X)(p:x∈illuminated K g θ)(t:pennant K g x=x): X x=0:=by
  have he(z:ℂ)(h': θ*z=z) : z=0:= by
    by_contra p; exact h (mul_right_cancel₀ p (h'.trans (one_mul z).symm))
  rcases w with w|w
  · refine Submodule.span_induction (p:=fun x _=> X x=0) (fun z h=>?_) X.map_zero (fun _ _ _ _ x y=>by rw [map_add,x,y,add_zero]) (fun a _ _ h=> by rw [map_smul,h,smul_zero]) p
    obtain ⟨f,b,r,t,e,rfl⟩:=h
    have hv:=w g b t; rw [e,map_smul,smul_eq_mul] at hv; rw [F _ _ r t,he _ hv,mul_zero]
  apply he; exact (pays_gauge K g θ X F w p).symm.trans (congrArg X t)
end kill
end YM.CF.Buffered.Afterglow.Six
