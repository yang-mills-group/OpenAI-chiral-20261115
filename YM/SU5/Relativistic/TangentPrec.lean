import YM.Work.F04.Pairing
import YM.Push.FREE_RESOLVENT.AffineGap
import YM.SU5.Relativistic.JadePins
/-! # determinant/pressure proof. gauge lattice counting coordinates -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Papyrus.GaugeFlux
open Function Finset Filter MeasureTheory Lattice Wilson RG Precision Exterior MinorPins Tree Matrix Bid Laurent
open scoped Matrix BigOperators Matrix.Norms.Frobenius InnerProductSpace ContDiff
open Fixed.Pivots (pivots Active mark)
variable {N:Side}{C:Side}(S:StepData C N)(G:Gauge)
abbrev Ink (N:Side):= Bond N×G.ColorIndex
abbrev Lace (N:Side):= Ink G N→ℝ
abbrev ScrollB (N:Side):=↥(interior G.ColorIndex N)
def brew (N:Side): Ink G N ≃ FreeResolvent.Slot G N 1:= (Equiv.prodCongr (coding N) (.refl G.ColorIndex))|>.trans (Equiv.prodAssoc _ _ _)
def laced {N:Side}(x:Lace G N): Dir G N := FreeResolvent.Affine.decode (x ∘ (brew G N).symm)
def coil{N:Side}(x:Dir G N): Lace G N:= FreeResolvent.flatten x ∘ brew G N
lemma wrap_coil(x:Dir G N):laced G (coil G x)=x:=by unfold laced coil; rw [Function.comp_assoc,Equiv.self_comp_symm,Function.comp_id]; rfl
lemma coil_wrap(x:Lace G N): coil G (laced G x)=x:=by unfold laced coil; rw [FreeResolvent.Affine.flat_decode, Function.comp_assoc,Equiv.symm_comp_self,Function.comp_id]
lemma craft_t(x:Lace G N)(e: Bond N) : collect G (laced G x) e= WithLp.toLp 2 (fun i=>x (e,i)):=by ext i; exact congrFun (coil_wrap G x) (e,i)
lemma craft_coil(x:Dir G N)(e:Bond N)(i:G.ColorIndex): (collect G x e) i = coil G x (e,i):=rfl
lemma cord (x y:Lace G N):dotProduct x y=∑ i:Body 1 N, inner ℝ ((laced G x) i) ((laced G y) i):=by rw [← FreeResolvent.flat_dot]; exact ((Equiv.sum_comp (brew G N).symm (fun i=>x i*y i))).symm
lemma connect (x y:Dir G N): dotProduct (coil G x) (coil G y)=∑ i:Body 1 N,inner ℝ (x i) (y i):=by rw [cord,wrap_coil,wrap_coil]
lemma warp(x y:Dir G N) : coil G (x-y)=coil G x-coil G y:=rfl
variable (B:Bed)
def hess (N:Side):Matrix (Ink G N) (Ink G N) ℝ := (FreeResolvent.tensor G (Precision.K (B.metric.acts N))).submatrix (brew G N) (brew G N)
def fast (N:Side):ScrollB G N ↪ Ink G N:=Embedding.subtype _
def blockD (N:Side) := (hess G B N).submatrix (fast G N) (fast G N)
def costDet (N:Side) := Matrix.det (blockD G B N)
lemma tent_h (x y:Lace G N): dotProduct x ((hess G B N)*ᵥ y) = gaugeFiscal B (laced G x) (laced G y):=by
 let M:= FreeResolvent.tensor G (Precision.K (B.metric.acts N)); let e:=brew G N; let X:=laced G x; let Y:=laced G y
 have he:=FreeResolvent.component_dot (FreeResolvent.flatten X) (M*ᵥ FreeResolvent.flatten Y); unfold gaugeFiscal
 change dotProduct x ((M.submatrix e e)*ᵥ y)=_
 trans dotProduct (FreeResolvent.flatten X) (M*ᵥ FreeResolvent.flatten Y); swap
 · rw [he]; exact Finset.sum_congr rfl fun i _=>congrArg _ (FreeResolvent.component_mul _ _ _)
 unfold dotProduct; rw [←Equiv.sum_comp e]; apply Finset.sum_congr rfl; intro i u
 rw [show (FreeResolvent.flatten X) (e i)=x i from congrFun (coil_wrap G x) i]; congr 1
 unfold mulVec dotProduct; rw [←Equiv.sum_comp e]; exact sum_congr rfl fun j _=> congrArg (fun r=> M (e i) (e j)*r) (congrFun (coil_wrap G y).symm j)
lemma hess_symm {A:Clip}{a b:ℝ}(p:Floor B A N a b): (hess G B N)ᵀ=hess G B N:=by
 have he:(Precision.K (B.metric.acts N))ᵀ= Precision.K (B.metric.acts N):=by unfold Precision.K; rw [←p.roots]; simp only [Matrix.transpose_mul, Matrix.transpose_transpose,Matrix.mul_assoc]
 unfold hess; rw [Matrix.transpose_submatrix, FreeResolvent.tensor_transpose,he] -- name
lemma atCurl (x:Lace G N)(i:G.ColorIndex)(e:Face (Per N)): Work.F03.faceCurl e (laced G x) i=Curl (fun p=> x (p,i)) e:=by
 obtain ⟨w,e⟩:=e; change (d 1 N *ᵥ parts G 1 (laced G x) i) (w,plaquette e)=_; rw [d_plaquettes]
 simp_rw [show ∀ p: Site N,∀ j, parts G 1 (laced G x) i (p,coord j)=x ((p,j),i) from fun p j=>congrFun (coil_wrap G x) ((p,j),i)]; unfold Curl; ring
lemma hess_ker : closedC G.ColorIndex N ≤ LinearMap.ker (hess G B N).mulVecLin:=by
 intro x h; let v:=laced G x; have he(i:G.ColorIndex):d 1 N*ᵥ parts G 1 v i=0:=by
    funext j; obtain ⟨a,b⟩:=j; obtain ⟨j,rfl⟩:= plaqEquiv.surjective b
    change Work.F03.faceCurl (a,j) v i=0; rw [show Work.F03.faceCurl (a,j) v i=_ from atCurl G _ _ _]; exact h i _
 funext i; change (hess G B N *ᵥ x) i = 0; rw [show (hess G B N *ᵥ x) i=dotProduct (Pi.single i 1) (hess G B N *ᵥ x) by simp,tent_h]; change gaugeFiscal B _ v=0
 unfold gaugeFiscal Precision.K; refine sum_eq_zero fun y _=>?_; rw [←mulVec_mulVec,he,Matrix.mulVec_zero]
 simp

lemma cost_billet (x y: Lace G N){p: Clip}{a b r s t:ℝ}{W:PathData G}(h:Floor B p N a b)(u:Attached B W)(v:W.Bounds p r s t)(w:Bid.Sworn B N G) (g:Signed): dotProduct x (hess G B N*ᵥ y)=
    ∑ i : Face (Per N),
      (p.direct * inner ℝ (Work.F03.faceCurl i (pulled (laced G x) g)) (Work.F03.faceCurl i (pulled (laced G y) g))+
       inner ℝ (Work.F03.ellLine W i (pulled (laced G x) g)) (Work.F03.ellLine W i (pulled (laced G y) g))) :=by rw [tent_h,← w g]; exact Work.F03.metric_pair _ v u _ _ h
-- spectral floor.A used many prices
end YM.CF.Papyrus.GaugeFlux
#print axioms YM.CF.Papyrus.GaugeFlux.cost_billet
