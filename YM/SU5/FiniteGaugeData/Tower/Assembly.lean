import YM.SU5.FiniteGaugeData.Tower.Weft
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
# Pay Menu OUTPUT side on the actual Course
-/
set_option quotPrecheck false
open Stencil Branch Tap Fock
variable (S:Finset Cover)
local notation "U₀"=> wingspan Λ l S
section chemistry
variable {J:Type*}(n k₀:J→ℕ)(p:∀i: J, legalAt Y s (n i) (k₀ i))
variable (v:Evens S)
local notation "t₀"=> tagWord S v.val
local notation "Z₀" i:max=> Y.voyage (n i)
local notation "Xs" i:max=> ((Z₀ i).X (Y.uv (k₀ i))).gram
local notation "Q₁" i:max => (((Z₀ i).X (Y.uv (k₀ i))).wave s).val
local notation "R₀" i:max=> (Z₀ i).CapeT s
local notation "A₀" i:max=> steps Λ.V (Y.ir (n i)) Λ.block (Y.uv (k₀ i)) s
local notation "μ" i:max t:max=> momentm Y (n i) t
local notation "d" i:max t:max=> side Y (n i) t
local notation "b"=> Λ.R.L
variable (h:∀i:J,Tivoli (wingspan Λ l S) ((tent Y H).c (momentm Y (n i) (s+1))))

lemma patch_sizes(i:J): (d i (s+1)).val=(d i s).val*(b).val:= (apt (Y.ir (n i)) Λ.block Λ.R.L s).exact_size
lemma kernel_sizes(i:J): (More (d i (s+1))).val=(More (d i s)).val*(b).val:= (ratio (apt (Y.ir (n i)) Λ.block Λ.R.L s)).exact_size
local notation "F₀" ξ:max=>fixedStep Λ.R Λ.K.bind (fun i=>d i s) (fun i=>d i (s+1)) (kernel_sizes Y s n) ξ
include k₀
lemma patch_real (i:J):(A₀ i)=(F₀ i):= by
 have he:∀ a c:StepData (More (d i s)) (More (d i (s+1))), a.patch=c.patch→ a.kernel=c.kernel→a=c:=by rintro ⟨p,u,v⟩ ⟨t,r,x⟩ h g; dsimp only at h g; subst_vars; rfl
 exact he _ _ (Y.pilot_steps s ..).1 (Y.pilot_steps s ..).2.1
local notation "mime" i:max=> (Course.beta Y (n i) (k₀ i) s)
include p h
variable (g:J→Purse S){B:ℝ}(u:0≤B)(x:∀ i z,‖(g i).val z‖≤B)
include u x
set_option maxHeartbeats 900000 in
lemma output_deck (a:J→Evens U₀): Menu (T:=fun (_:J)=>ℂ) (fun (i:J)(z:PairsC)=> banner U₀ K (block Y H s (n i) (k₀ i) S (note K (g i).val t₀)) (a i) z):=by
 rcases isEmpty_or_nonempty J with J' | m
 · exact Menu.congr (h:=Menu.zero) fun (i:J)=> isEmptyElim i
 have j₀:= Classical.choice m
 let Z':= Course.ceiling Λ s
 have β(i:J): |mime i|≤ Z':=abs_le.mpr (Y.seated s (n i) (k₀ i) (p i).2)
 let fees:= Λ.R0 (hat (b) Λ.x s)
 have ht(i:J): ‖Q₁ i‖ ≤ fees:= ((Y.voyage (n i)).X (Y.uv (k₀ i))).pull.tip s (p i).2
 have hx:= (Y.pilot_steps s (n j₀) (k₀ j₀)).2.2
 change (A₀ j₀).patch.Branches (A₀ j₀).kernel SU.group at hx
 rw [patch_real Y s n k₀ j₀] at hx
 have hL(i:J):Measurable (R₀ i):=((Y.voyage (n i)).ownership s).paid.bill
 let P':= (fullness Y (n j₀) (k₀ j₀) (p j₀).1).cap_grant
 obtain ⟨m'⟩:= P'.grant s (p j₀).2
 let f(i:J):= note (tent Y H) (g i).val (tagWord S v.val)
 have hf(i): InTest K true S false (f i):= v.property ▸ note_t K _ (g i).property (brand S v.val) -- rw alternative
 have hf'(i:J): Envelope (knot (d i s) (t₀) (g i).val):=by
    rw [← notation_note Y H]; exact (stationed Y H s S (n i) (hf i)).env
 let q₀(i:J)(z:PairsC):= aboveD Y H s (n i) (k₀ i) (f i) (replant (U₀) (d i (s+1)) z)
 let W(i:J):=apt (Y.ir (n i)) Λ.block (b) s
 let Gₛ:=bead (fun i:J=>d i s) (b) (fun i=>d i (s+1)) (patch_sizes Y s n)
 have q':Menu q₀:=by
    have g:=tickets U₀ Λ.R Λ.K.bind hx Λ.K.j (aliasLaw Λ) (Journey.legal Λ) (fun i:J=>d i s) (fun i=>d i (s+1)) (patch_sizes Y s n) (fun i=>R₀ i) hL (fun i=>((Xs i) (s+1)).J.M) (fun i=>Q₁ i) ht Chi.canonical Λ.J.d m'.legal.1 m'.legal.2 (fun i=>mime i) β (fun i=> (g i).val) (t₀) u x hf'
    refine g.congr fun i v=>?_
    unfold q₀ aboveD nextMark f
    rw [show (steps Λ.V (Y.ir _) _ _ s) = F₀ i from patch_real Y s n k₀ i,notation_note Y H] -- f let
    rfl
 let t(i:J)(A:FC (Single (d i (s+1)))):= paintOp U₀ (tent Y H) (μ i (s+1)) (h i) (terrain Y H (Y.ir (n i)) (s+1)) A (a i)
 obtain ⟨D,e,C⟩:= q'.budget
 have z':Menu (fun i z=>t i (q₀ i z)):=by
    refine ⟨q'.deal.along t ?_, D,e,fun i x=>(charged_cast ..).trans (C ..)⟩
    intro δ v; refine ⟨δ,v,fun i x y h=>?_⟩; rw [dist_eq_norm] at h ⊢; unfold t; rw [← paint_jump]; exact lt_of_le_of_lt (charged_cast ..) h
 refine z'.congr fun i z=> ?_
 let μ₀:=block Y H s (n i) (k₀ i) S (f i)
 have e':= delivery U₀ K _ (h i) (terrain Y H (Y.ir (n i)) (s+1)) (F:=μ₀) (booked Y H s (n i) (k₀ i) S _) (a i) z
 change t i (q₀ i z) = _
 unfold q₀
 rw [← reserved Y H s S _ _ (p i) (hf i) (h i)]; exact e'
end chemistry
end YM.CF.Buffered.Afterglow.Tower
#print axioms YM.CF.Buffered.Afterglow.Tower.output_deck
