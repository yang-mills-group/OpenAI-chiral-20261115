import YM.CF.BProof.Seam.Probe
/-! N Mark extension View; depth prices on chosen data. -/
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Seam
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox Mapping House Release hot Gauss Weights Pricing Micro Trek
open Gates Gates.Stage Gates.Stage.Setup Contour Contour.Season Contour.Battery Contour.Tower Cube Cabinet Pods Posts Skye
open scoped Topology BigOperators Classical
local notation "G"=> SU.group
variable {c:Clip}{w R v:ℝ}{S:Gates.Stage c w R v}{L:Side}{a:ℕ}{y:ℝ}{d:ℕ}{N:Side}(Y:S.Setup L a (More N) d y)(P:Entice S L a d y)(T:PathData G)(θ:ℝ)(x:Pod Y)
local notation "mH"=> Y.yard
local notation "B"=> Y.Block
local notation "g₀"=> Y.g
local notation "wB"=>House.Season mH Y.c'
local notation "gE"=>Trek.tag mH
local notation "πX"=> Cabinet.roadB Y
local notation "rawK"=> rawG Y P T θ
local notation "K_"=> Y.hall
open Hero Mark
open Spin Dream Fock Dial -- fix
set_option maxHeartbeats 260000
local notation "Ζ_"=>framesL Y P T θ
local notation "CC"=>Y.yard.long
variable {m:Side}(f:Ratio m (More N))
abbrev wear(x:Pod Y): Script mH:= actual K_ f (rawK x) Y.yard (Ζ_ x) (tool Y x).mood -- Tune
variable {Y P T θ} {i:Y.yard.Index} {μ:Support (More N)}{Λ:Finset (House.Block Y.yard Y.c')}
variable (T': Probe Y P T θ Λ μ)  -- tune b undecl
local notation "Δ_"=> Y.yard.u i
variable (W:Hero.Width f Y.yard.long)(F:4≤m.val)
variable {x} (x':Pod Y)(e:Cabinet.Ready P Y T θ x)(l:Cabinet.Ready P Y T θ x')(vT:Spiced Y Λ x x'){t:Seat N}(t': t∈ Y.yard.band i)(U:Lattice.halo (2*f.count.val) {t}⊆ μ)
-- depth cost from width and chip. true fields, any adjacent within r_body.
include W t' in
lemma depthN (v:t∉ BeltL Δ_ CC){v':Seat N}(h:v'∈ Y.yard.band i)(u:separation t v'≤2*f.count.val): Deep.rise mH (2*Deep.D mH) i (time v'):=by
 obtain ht:= Hero.accord Δ_ CC t' v; obtain hu:= Hero.chip_le Δ_ CC h t' (Trek.wide ..); have he:=Deep.D_le mH; have g:=Y.yard.before_u i (show Y.yard.Band i (time v') from mem_strip.mp h); unfold chip at *; unfold Hero.Width at W; rw [separation_comm] at u; refine ⟨mem_strip.mp h,?_,?_⟩<;> omega -- tune
abbrev ſhi(x:Pod Y) := Mark.XN Δ_ CC K_ f (rawK x) (Ζ_ x i)
variable (uN:¬Y.yard.D i)
namespace Probe
include W F e l vT T' t' U uN
-- uses deep both sides exactly
lemma picksX : ſhi (i:=i) (P:=P) (T:=T) (θ:=θ) f x t=ſhi (i:=i) (P:=P) (T:=T) (θ:=θ) f x' t:=by
 let i₀:Support (More N):= Lattice.halo (2*f.count.val) {t}; let A:= (↑(Y.yard.band i):Set (Seat N)); let E:= {x:Seat N|x∈ A ∧ separation t x≤ 2*f.count.val}; have ht:t∈ E:=⟨t',by simp⟩; have hu(z:Seat N)(v:z∈ E):z∈μ:= U (Lattice.halo_spec.mpr ⟨_,mem_singleton_self _,v.2⟩); unfold ſhi; have h(x₀:Seat N)(v:x₀∈E): seed Δ_ CC (rawK x) (Ζ_ x i) x₀=seed Δ_ CC (rawK x') (Ζ_ x' i) x₀:=congrArg (fun u=> scaledV u⁻¹ apex) (T'.eye x' e uN v.1 vT l (hu x₀ v)) -- order
 by_cases u:t∈ BeltL Δ_ CC; · rw [XN_rim _ _ _ _ _ _ u,XN_rim _ _ _ _ _ _ u]; exact h t ht
 have g(z:Seat N)(v:z∈ E) : Angular.V Δ_ CC K_ (rawK x) (Ζ_ x i) z=Angular.V Δ_ CC K_ (rawK x') (Ζ_ x' i) z := T'.deep x x' e l vT _ z uN (hu z v) (depthN f W t' u v.1 v.2) -- tune
 rw [XN,XN,g t ht]; apply congrArg (scaledV _); unfold XN₀; refine Hero.year_here Δ_ f CC (Angular.hall Δ_ CC K_ (rawK x) (Ζ_ x i)) (Angular.hall Δ_ CC K_ (rawK x') (Ζ_ x' i)) _ _ t t' (Trek.wide ..) F W (fun i v=> ?_) (fun i a b=>?_)
 · unfold Mark.plot; split_ifs; rw [g _ v,h _ v]; rfl
 --
 unfold Angular.hall Lattice.gauge; rw [g i.1 a,g _ b,T'.lawn x x' e l vT i (hu i.1 a) (hu _ b)]
omit uN
lemma spins : (wear Y P T θ f x).X i t=(wear Y P T θ f x').X i t ∧ (wear Y P T θ f x).K i t= (wear Y P T θ f x').K i t:=by
 change winter mH i K_ f _ _ _= winter mH i K_ f _ _ _ ∧ summer mH i K_ f _ _ _=summer mH i K_ f _ _ _; unfold winter summer; split; · exact ⟨rfl,rfl⟩
 rename_i h; have ht:= picksX f T' W F x' e l vT t' U h; refine ⟨ht,?_⟩; unfold HN; split_ifs; · change motion (gownL Y P T θ x i t)⁻¹ ∘ _= _; rw [T'.eye x' e h t' vT l (U (Lattice.halo_subset _ _ (mem_singleton_self t)))]
 exact congrArg (fun v:Ballot=> fun _:ℝ=> Pair.fullM v.val) ht
end Probe
end YM.CF.BProof.Seam
