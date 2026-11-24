import YM.SU5.FiniteGaugeData.Tower.Stabilize
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 500000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1≤Λ.x)
local notation "K" => tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
/-!
# Menu on the *upper* Fock panels

Before the upper Fock insertion, keep all the actual tag and transport data.
Output W on chart from upper cover, lower configurations reading everywhere
so simultaneous even with variations or errors on input arguments.
-/
open Next.SectorChange Tree Precision Fock Stencil Tap Tenant
section
variable (S:Finset Cover)(L:Side)(j D:ℕ)(a: LaurentRadius j L D)(o:Odd L.val){X I:Type*}[MeasurableSpace X](N P:I→Side)(h:∀i,(P i).val=(N i).val*L.val)
local notation "G"=> Satin.bead N L P h
variable (M:I→ Male)(Q:I→Op SU.Slot){d:ℝ}(t:∀i,‖Q i‖≤d)
variable (V:X→LinksC)(p:Measurable V)
local notation "W" i:max x:max=> Satin.graft S (P i) (V x)
variable (U:(i:I)→Fields (N i))(q:Chi)(γ:ℝ)(hg:0<γ)(hr:2*γ<firstRadius SU.group)
variable (F:(i:I)→ Forest (ratio (G i)))
section fold
include p
lemma top_deal (Wf:(i:I)→ Forest (ratio (Satin.bead N L P h i))) (x:(i:I)→Seat (P i)):Deal (fun i (w:X)=> (Wf i).foldAt (W i w) (x i) : I→X→SU.E):=by
 unfold Tree.Forest.foldAt; refine (Palette.clip_su (palette_walk P (fun i x=> W i x) ?_ (4*L.val) x _ (fun i=>((Wf i).hike_lower _).trans ((Wf i).bound _)))).post continuous_inv
 exact album_g S P V p
include hg hr
lemma middle_deal (Wf:(i:I)→ Forest (ratio (G i))) (k:(i:I)→Edge (Seat (P i))): Deal (fun i x=> seine (G i) (Wf i) q γ (W i x) (U i).2 (k i) : I→X→ SU.E):=by
 let Wf₀ i x:=(Wf i).foldAt (W i x)
 have H(x:(i:I)→Seat (P i)):Deal (fun i (t:X)=> Wf₀ i t (x i) : I → X → SU.E):= top_deal S L N P h V p Wf x
 let d(i:I)(x:X) : Pane (P i):= gauge (Wf₀ i x) (W i x)
 let K₁(i:I):= (k i).1; let K₂(i:I):= (k i).1+step (k i).2
 have hm{J Y:I→X→SU.E}(m:Deal J)(n:Deal Y):Deal (fun i x=> J i x*Y i x):= (m.prod n).post (continuous_fst.mul continuous_snd)
 have hi{J:I→X→SU.E}(m:Deal J):Deal (fun i x=>(J i x)⁻¹):=m.post continuous_inv
 have hd:Deal (fun i x=> d i x (k i) : I→X→SU.E):=hm (hm (H K₁) (Palette.clip_su (album_g S P V p k))) (hi (H K₂))
 let R:= (fun i=> Precision.replica (ratio (G i)) (show Config SU.group _ from (U i).2) (k i) : I → SU.E)
 have hr':Deal (fun i x=> portU (G i) (Wf i) q γ (W i x) (U i).2 (k i) : I→X→SU.E):=(hd.prod (Deal.pure (T:=fun _=>SU.E) R)).post (show Continuous (fun x:SU.E×SU.E=> knit q γ x.1 x.2) from (SU.group.lieExp_cont.comp ((patched_continuous q hg hr).comp (continuous_fst.mul continuous_snd.inv))).mul continuous_snd)
 exact hm (hm (hi (H K₁)) hr') (hi (hi (H K₂)))
end fold
include p a o t hg hr
-- pay before integrating the level-input fields and β-- so can even use
-- after multiplying hard f on those fields.
lemma fabrics (u:Chorus):Menu (T:=fun i=>FC (Single (P i))) (fun (i:I)(x:X)=> gathered (G i) j (Q i) (M i) o q γ (wholeZ (N i) u) (1,W i x) (U i)):=by
 let J(i:I):=Forest (ratio (G i))
 let s:= Sigma J; let A(α:s):=N α.1; let B(α:s):= P α.1
 refine circle (J:=J) ?_
 refine wool A L B (fun a=>h a.1) j D a o (fun a=> M a.1) (fun a=>Q a.1) (fun a=> t a.1) (fun a x=> middle (G a.1) q γ a.2 (1,W a.1 x) (U a.1)) ?_ u
 intro k
 exact middle_deal S L A B (fun a=>h a.1) V p (fun a=>U a.1) q γ hg hr (fun a=>a.2) k
variable (x:X→PairsC)(hz:Measurable x)
local notation "Z" i:max v:max=>replant S (P i) (x v)
omit p
include hz
lemma knot_purchase (u:Chorus)(f:I→ PairsC→ℂ){C:ℝ}(c:0≤C)(e:∀ i x,‖f i x‖≤C): Menu (T:=fun i=>FC (Single (P i))) (fun (i:I)(k:X)=> gathered (G i) j (Q i) (M i) o q γ (knot (N i) u (f i)) (Z i k) (U i)):=by
 let v(i:I):= Prod.map (onC _) (onC _) (U i)
 let w(i:I):= f i (v i)
 have H:= Menu.cnst (X:=X) (I:=I) (T:=fun _=>ℂ) w c (fun i=> e _ _)
 let d(i:I)(k:X):Fields (P i):=(1,(Z i k).2)
 have he:= H.scale (show Menu (T:=fun i=>FC (Single (P i))) (fun i (k:X)=>gathered (G i) j (Q i) (M i) o q γ (wholeZ (N i) u) (d i k) (U i)) from fabrics S L j D a o N P h M Q t (fun v=>(x v).2) (measurable_snd.comp hz) U q γ hg hr u)
 refine he.congr ?_
 intro i k; unfold gathered avgF Advance.before; simp_rw [wholeZ,Satin.knot,map_smul]; rw [←Finset.smul_sum,smul_comm]; rfl

end
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.knot_purchase
