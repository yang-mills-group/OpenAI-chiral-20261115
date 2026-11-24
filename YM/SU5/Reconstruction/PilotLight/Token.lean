import YM.SU5.Reconstruction.PilotLight.Position
/-! A Chain is exactly an occupation diagram, earlier and later yes/no flags. Encodes
synchronized pure gauge and Lode pair investigating a genuine mixed-interaction reading.
Retains translations/position currency, in particular NO assertions still at higher levels as a
lifted Pure Gauge / Matter colouring separately!
-/
set_option autoImplicit false
set_option synthInstance.maxSize 29000
set_option maxRecDepth 5500
set_option maxHeartbeats 400000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
open Function Set Filter NormedSpace Lattice Wilson Cube MeasureTheory Reflect Advance
  Scroll Skye Window Journey Satin Tapestry
open Vacancy Selected SatinVerification Py Py.Rate LocalLimit Preparation SlabMark MeshClock
open scoped Topology BigOperators ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open CF.Pannier.Chancel
open Fock Lat Lifted
open SelectionAnalysis

variable {Λ: Preparation}{l:ℕ}(Y: Course Λ (VolumeCape.Dream.Nimbus l))(H: Real.exp 1 ≤ Λ.x)
local notation "K"=>tent Y H
variable {J: Calibration}{x y: Dome J}
variable (s w: ℕ)
def witnessGauge (J: Calibration) (S:Finset Cover)(g:Dome J): Prop:=∃ (F:PairsC→ℂ), Coeff false S F∧ g.val=scalar J F
def witnessLode (J:Calibration)(z:SU.Slot)(S:Finset Cover){n:ℕ}(a:Fin n → Cover)(x:Dome J): Prop := x.val∈ Lode J (Window.family z) a S

inductive Clause (J:Calibration)(z:SU.Slot)(S:Finset Cover){n:ℕ}(a:Fin n → Cover)(w:ℕ) : ℕ→ Bool → Dome J→Dome J→ Prop where
| begin_ : Clause _ _ _ _ _ 0 false 1 1
| later_ {d i g m} (h:Clause J z S a w i d g m): Clause J z S a w (i+1) d (lined J w g) (lined J w m)
| here_ {d i g m x y}(h:witnessGauge J S x)(t:witnessLode J z S a y)(q:Clause J z S a w i d g m): Clause J z S a w (i+1) true (x*lined J w g) (y*lined J w m)

/- The insertion and its normalization. Width on EVERY such book is bAll. -/
noncomputable def layers (J:Calibration)(x:Dome J)(w:ℕ):ℕ→Dome J
| 0=>1
| n+1=>(1+x)*lined J w (layers J x w n)
noncomputable def lantern (J:Calibration)(x:Dome J)(w n:ℕ): Dome J:= layers J x w n-1
@[simp] lemma layer_starts : layers J x w 0=1:=rfl
lemma step_layer (n:ℕ): layers J x w (n+1)=(1+x)*lined J w (layers J x w n):=rfl
lemma step_lantern (n:ℕ): lantern J x w (n+1)= x+lined J w (lantern J x w n) + x*lined J w (lantern J x w n):=by
 rw [lantern,step_layer,show layers J x w n=lantern J x w n+1 from (by unfold lantern; rw [sub_add_cancel]),lined, map_add, reposition_unit]; unfold lined; ring
section span
variable (z:SU.Slot)(S:Finset Cover){L:ℕ}(a:Fin L → Cover)
-- prove Raw Filigree launches coherent Tickets (Dome). In first wide tests. Here no charges ready in general, so no lifting timbre.
local notation "E" q:max=> Filigree J (Window.family z) a S q
lemma bright (p:x.val∈ Filigree J (Window.family z) a S): x∈ Submodule.span ℂ {t:Dome J | ∃ (g m:Dome J), witnessGauge J S g∧ witnessLode J z S a m∧ t=g*m} :=by
 let T:=Submodule.span ℂ {t:Dome J | ∃ (g m:Dome J), witnessGauge J S g∧ witnessLode J z S a m∧ t=g*m}
 refine Submodule.span_induction (p:=fun q _=> ∀ (x:Dome J), x.val=q→x∈ T) ?_ ?_ ?_ ?_ p x rfl
 · rintro _ ⟨m,F,t,h,rfl⟩ x hx; let g: Dome J:= ⟨scalar J F,aux_test ((InTest.seed h : InTest J false S false (scalar J F)).widen)⟩; let m': Dome J:=⟨m,aux_test (Lode_test t|>.widen)⟩
   exact Submodule.subset_span ⟨g,m',⟨F,h,rfl⟩,t,Subtype.ext hx⟩
 · intro x p; rw [show x=0 from Subtype.ext p]; exact T.zero_mem
 · intro v q g m hv h' x l; let x' : Dome J:= ⟨v,aux_test ((FilTest (W:=Window.family z) (b:=a) (S:=S) (by exact g)).widen)⟩; let y' : Dome J:=⟨q,aux_test ((FilTest (W:=Window.family z) (b:=a) (S:=S) (by exact m)).widen)⟩; rw [show x=x'+y' from Subtype.ext l]; exact T.add_mem (hv x' rfl) (h' y' rfl)
 intro b q p h x l; let x' : Dome J:=⟨q,aux_test ((FilTest (W:=Window.family z) (b:=a) (S:=S) (by exact p)).widen)⟩; rw [show x=b • x' from Subtype.ext l]; exact T.smul_mem b (h x' rfl)

def fieldBook (J:Calibration)(w d:ℕ) : Submodule ℂ (Dome J):= Submodule.span ℂ {v:Dome J| ∃ g m:Dome J, Clause J z S a w d true g m ∧ v=g*m}
local notation "F" d:max=> fieldBook z S a J w d
@[simp] lemma fromClause {w n:ℕ}{m g:Dome J}(p: Clause J z S a w n true g m): g*m∈ fieldBook z S a J w n:= Submodule.subset_span ⟨g,m,p,rfl⟩
lemma clause_empty (n:ℕ): Clause J z S a w n false 1 1 := by
 induction n with|zero=> exact .begin_|succ n ih=> simpa only [lined,reposition_unit] using ih.later_
lemma book_closed {m:Dome J}(n:ℕ)(h:m∈ fieldBook z S a J w n): lined J w m∈ F (n+1):=by
 refine Submodule.span_induction (p:=fun y _=> lined J w y∈ F (n+1)) (fun x h=>?_) ?_ ?_ ?_ h
 · obtain ⟨u,q,h,rfl⟩:= h; have h':lined J w (u*q)=lined J w u * lined J w q:=reposition_prod ..; exact h'.symm ▸ fromClause z S a (Clause.later_ h)
 · unfold lined; rw [map_zero]; exact (F (n+1)).zero_mem
 · intro x y _ _ p q; unfold lined; rw [map_add]; exact (F (n+1)).add_mem p q
 intro c y _ h; unfold lined; rw [map_smul]; exact (F (n+1)).smul_mem c h
lemma earliestBook (n:ℕ)(p:x.val∈ Filigree J (Window.family z) a S): x∈F (n+1):=by
 refine Submodule.span_induction (p:=fun x _=> x∈ F (n+1)) ?_ ((F (n+1)).zero_mem) (fun _ _ _ _ h t=> (F (n+1)).add_mem h t) (fun a _ _ h=> (F (n+1)).smul_mem a h) (bright z S a p)
 rintro _ ⟨u,m,p,q,rfl⟩; refine fromClause z S a ?_
 simpa only [lined,reposition_unit,mul_one] using Clause.here_ p q (clause_empty (J:=J) w z S a n)
lemma allIlluminated (n:ℕ)(p:x.val∈ Filigree J (Window.family z) a S): lantern J x w n∈ fieldBook z S a J w n:=by
 induction n with
 | zero=> unfold lantern; rw [layer_starts,sub_self]; exact (F 0).zero_mem
 | succ n ih=>
    rw [step_lantern]; apply (F (n+1)).add_mem ((F (n+1)).add_mem (earliestBook w z S a n p) (book_closed w z S a n ih))
    refine Submodule.span_induction₂ (p:=fun x y _ _=> x*lined J w y∈ F (n+1)) ?_ ?_ ?_ ?_ ?_ ?_ ?_ (bright z S a p) ih
    · rintro _ _ ⟨u,m,p,q,rfl⟩ ⟨v,i,h,rfl⟩; rw [show ((u:Dome J)*m)*lined J w (v*i)=(u*lined J w v)*(m*lined J w i) from (by unfold lined; rw [reposition_prod]; ring)]; exact fromClause z S a (Clause.here_ p q h)
    · intro _ _; rw [zero_mul]; exact (F (n+1)).zero_mem
    · intro _ _; unfold lined; rw [map_zero,mul_zero]; exact (F (n+1)).zero_mem
    · intro _ _ _ _ _ _ h v; rw [add_mul]; exact (F (n+1)).add_mem h v
    · intro _ _ _ _ _ _ h v; unfold lined; rw [map_add,mul_add]; exact (F (n+1)).add_mem h v
    · intro c _ _ _ _ h; rw [Algebra.smul_mul_assoc]; exact (F (n+1)).smul_mem _ h
    intro c _ _ _ _ h; unfold lined; rw [map_smul,Algebra.mul_smul_comm]; exact (F (n+1)).smul_mem _ h
end span
end YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame
#print axioms YM.CF.Buffered.Afterglow.Tower.FirstWindows.ChargeFrame.allIlluminated
