import YM.SU5.Six.RawWard
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
variable (W:Bool)(S T D:Finset Cover)(g:Cover→SU.E)
private lemma cyclic_scale {V:Finset Cover}{x y:Buffered.Family K}(t: Circular V g x y)(z:ℂ) : Circular V g (z • x) (z • y):= t.scale g V z
lemma creation_fixed (w:∀ i∈S,g i=1){f:Buffered.Family K}(p:f∈SinglePocket K W S true): Circular S g f f:= by
  refine Submodule.span_induction (p:=fun f _=> Circular S g f f) (fun f t=>?_) (fun _ _ _ _=>(map_zero _).symm) (fun _ _ _ _ a b=> Circular.add g S a b) (fun z _ _ h=>cyclic_scale K g h z) p
  obtain ⟨y,i,b,u,t,h⟩:=t
  rw [if_pos rfl] at h; obtain ⟨j,rfl⟩:=h
  intro m a h v
  let n:=K.c m; let x:=basisC n y i b
  have hp: acts (tradew n a).val x=x:=by
    unfold x; rw [turn_basisC n a y i b,h _ u,w _ u]
    simp [Matrix.one_apply]
  change create x= twist _ (create x)
  rw [twist_create,hp]
lemma removal_center (w:∀ i∈T,g i= SU.central){f:Buffered.Family K}(p:f∈SinglePocket K W T false) : Circular T g f (phaseName W • f):= by
  refine Submodule.span_induction (p:=fun f _=> Circular T g f (phaseName W • f)) (fun f t=>?_) (by rw [smul_zero]; exact fun _ _ _ _=> (map_zero _).symm) (fun _ _ _ _ a b=>by rw [smul_add]; exact a.add g T b) (fun z f _ h=> by rw [smul_comm (phaseName W) z f]; exact h.scale g T z) p
  obtain ⟨y,i,b,u,t,h⟩:=t
  rw [if_neg Bool.false_ne_true] at h; obtain ⟨j,rfl⟩:=h
  intro m a h v
  let n:= K.c m; let x:=basisC n y i b; let c:=phaseName W
  have he:acts (tradew n a).val x=c • x:= by
    unfold x; rw [turn_basisC n a y i b,h _ u,w _ u,SU.by_charge,sum_eq_single b]
    · rw [Matrix.diagonal_apply_eq,←charge_identity,t]
    · intro i _ v; rw [Matrix.diagonal_apply_ne _ v,zero_smul]
    simp
  change Fock.remove x= twist (quantU _) (c • Fock.remove x); rw [twist_scalar,twist_remove,he]; unfold Fock.remove; rw [map_smul,star_smul,smul_smul,mul_comm c,scale_unit_self (pname_unit W),one_smul]
lemma pocket_charge (u:S∪T⊆D)(a:∀ i∈S,g i=1)(b:∀ i∈T,g i=SU.central){f:Buffered.Family K}(p:f∈ RawPair K W S T): Circular D g f (phaseName W • f):= by
  refine Submodule.span_induction (p:=fun f _=> Circular D g f (phaseName W • f)) (fun z t=>?_) (by rw [smul_zero]; exact fun _ _ _ _=> (map_zero _).symm) (fun _ _ _ _ h r=>by rw [smul_add]; exact h.add g D r) (fun z f _ h=> by rw [smul_comm (phaseName W) z f]; exact h.scale g D z) p
  obtain ⟨x,h,y,t,rfl⟩:= t
  rw [←smul_mul_assoc]
  apply Circular.mul g D (largerGauge (subset_union_right.trans u) (removal_center K W T g b h))
    (largerGauge (subset_union_left.trans u) (creation_fixed K W S g a t)) -- use exact
lemma illuminated_dressed (u:S∪T⊆D)(a:∀ i∈S,g i=1)(b:∀ i∈T,g i=SU.central){f:Ω}(p:f.val∈DressedPair K W S T D): f∈ illuminated K g (phaseName W):= by
  let Q:= illuminated K g (phaseName W)
  let M:= Q.map (screenHall K).val.toLinearMap
  have he:DressedPair K W S T D≤M:=by
    refine Submodule.span_le.mpr ?_
    rintro z ⟨w,t,x,h,rfl⟩
    let c:Ω:=⟨scalar K w,broadCompile K D (.seed t)⟩
    have hx: InTest K true D false x:= (raw_test K W S T h).1.mono u
    let l:Ω:=⟨x,broadCompile K D hx⟩
    have Hc:pennant K g l=phaseName W • l:=appointed K D g _ _ (pocket_charge K W S T D g u a b h) (show InTest K true D false (phaseName W • x) from InTest.smul _ hx)
    exact ⟨c*l,Submodule.subset_span (show _∈_ from ⟨_,_,⟨D,w,t,rfl⟩,(show PureMatter K l from (raw_test K W S T h).2),Hc,rfl⟩),rfl⟩
  obtain ⟨X,h,t⟩:=he p; exact (show X=f from Subtype.ext t) ▸ h

/-- Illuminate just one insertion; all other factors combined in the second
 Dome test, not even required here to be paired probes. -/
lemma ward_price {X:Dome K→ₗ[ℂ]ℂ}(p: Factors K X)(q:MatterWard K X ∨ GaugeWard K X)
    {x y:Ω} (a:x∈enclave K) (e:x.val∈DressedPair K W S T D) (u:S∪T⊆D) (d:Disjoint S T)
    {V:Finset Cover}(s:y∈bay K V true)(t:Disjoint D V) : X (x*y)=0 := by
  let g:Cover→SU.E:=fun i=>if i∈T then SU.central else 1
  have hr:∀ i∈V,g i=1:= fun i v=> if_neg fun h=> Finset.disjoint_left.mp t (u (mem_union_right _ h)) v
  refine marginal_zero K g (phaseName W) _ p (pname_ne W) q
    (illuminated_mul K g _ (illuminated_dressed K W S T D g u ?_ (fun _ v=> if_pos v) e) (fixed_illumined K V g hr s)) ?_
  · exact fun i v=> if_neg fun h=> Finset.disjoint_left.mp d v h
  rw [map_mul,(colorFixed K).1 a g,fixed_local K V g hr s]
end YM.CF.Buffered.Afterglow.Six
