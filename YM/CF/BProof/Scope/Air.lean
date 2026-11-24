import YM.CF.BProof.Scope.Lift

/-! Primary/Weak uncancelled supports. Loans. -/
set_option autoImplicit false
set_option synthInstance.maxSize 26000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BProof.Scope
open Function RG Wilson Lattice Filter MeasureTheory SU Grid Angular Angular.Yard Finset Prox Mapping House Release hot Gauss Weights Pricing Micro Trek
open Gates Gates.Stage Gates.Stage.Setup Contour Contour.Season Contour.Battery Contour.Tower Cube Cabinet Pods Posts Skye Seam
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
open Rhythm Tape Hearth Lat
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Hearth Tape Mark
attribute [local instance] opCStarAlgebra
variable {N₁ N₂:ℕ} {m m':Side}{j:ℕ} {a₁ b l r:ℝ}{D:Spin.Ready j a₁ b l r}{u:ℝ} (E:Essence D u)
variable {rₜ:ℕ} (Δ:Rhythm.Note E (Gates.gap L a) rₜ)(U: Orbit N → Pane N) (ν δ:ℝ)
variable {rB:ℕ}
variable {Y E T θ Δ U ν δ} (Z : School Y T θ E Δ U ν δ rB)
namespace Air
local notation "εx" => Rhythm.Lease.wearC S y
local notation "ΨN" => Pouch Y P T θ
local notation "ζ_"=>framesL Y P T θ
local notation "κ_"=>rawG Y P T θ
local notation "C'"=>Δ.clock
open Tulip Branch Stint Oasis Palot Garden Anthem Payment Veil Scree
variable (A: Core j a₁ b l r N)
variable (xw x'w:Pouch Y P T θ){I I':Type}[Fintype I][Fintype I']
local notation "ψ" => Z.pose P A
local notation "ψ0"=>Z.hom P A
variable (k:ℕ)(e:1≤k)(f:k<Deep.D Y.yard)
def atFall (Y:S.Setup L a (More N) d y)(k:ℕ)(μ:Support (More N)):= ∀ j:Y.yard.Index,¬(μ⊆Y.yard.band j ∧ ∀ i∈ μ, ¬Manus.Shallow Y.yard k i)
def through (Y:S.Setup L a (More N) d y)(k:ℕ)(μ:Support (More N)):=∃ i∈μ,Manus.Shallow Y.yard k i
lemma alive_foot (μ:Support (More N))(M:Manus N I)(i:I)(t:M.floor i=μ): i∈M.mist mH k ↔ atFall Y k μ:=by
 subst μ; simp only [Manus.mist,Manus.sung, mem_filter,mem_univ,true_and]; rfl
include e
lemma atFall_on {μ:Support (More N)}(v:μ.Nonempty)(g:atFall Y k μ)(p: Micro.Loc μ): through Y k μ:=by
 by_cases h:∃ j:Y.yard.Index,μ⊆ Y.yard.band j; · obtain ⟨j,z⟩:= h; by_contra h; exact g j ⟨z,fun i p=>fun v=>h ⟨i,p,v⟩⟩
 obtain ⟨x,v,j,z⟩:= Y.yard.gain μ v p (not_exists.mp h) -- tune
 exact ⟨x,v,j,Y.yard.vic_nearer j _ _ _ e z⟩
omit e
-- leaf supports independently, abstract. Useful exponent split.
def Εm (W:Manus N I)(y:World N)(i:I) : ℂ := if atFall Y k (W.floor i) then W.val i y else 0
lemma book_lost (W:Manus N I)(v:World N) : W.rest mH k v= ∑ i, Εm (Y:=Y) k W v i:=by
 unfold Εm Manus.rest Manus.mist; rw [sum_filter]; apply sum_congr rfl; intro i g; have he: (∀ j:Y.yard.Index,i∉W.sung mH j k)↔i∈ W.mist mH k:= by simp only [Manus.mist,mem_filter,true_and,mem_univ]
 exact if_congr (he.trans (alive_foot k _ W i rfl)) rfl rfl
abbrev Atmos (f:Support (More N)→Prop)(p:I→Support (More N))(z:I→ℝ)(i:I):= if f (p i) then z i else 0
lemma lim_toll (f:Support (More N)→Prop)(p:I→Support (More N))(z:I→ℝ){α C:ℝ}(h:Moment.Toll p z α C): Moment.Toll p (Atmos f p z) α C:=by
 apply h.shrink; intro i; unfold Atmos; split; exact h.nonneg ..; exact le_rfl; intro i; unfold Atmos; split; exact le_rfl; exact h.nonneg ..
variable {D':GramM N}{K α C h o η:ℝ} (Yp:Pay)
local notation "H_"=> Z.age P A
local notation "c_"=> Δ.stage.c
local notation "J_"=> Δ.stage.η
variable (V:Marks (Z.age P A) Yp Δ.stage.c rateH Δ.stage.η)(q:Cargo D' h o)(R':Oasis.Tube D' Yp h η o α C) (F:Pantry V q η)
-- δ h independent.Schedule
local notation "fG" => Veil.cityS D'
local notation "vG" => Veil.cityP V q η
-- Chain1
abbrev frosty (x:Pouch Y P T θ): Quiet N := (Z.world1 P A x).1
abbrev Dew (i:KeyP N)(t:Pouch Y P T θ):ℂ:=(F.loan i).val (frosty P Z A t)
abbrev frozen : KeyP N→ℝ:= Atmos (atFall Y k) fG vG
abbrev freeze(i: KeyP N)(x:Pouch Y P T θ):ℂ := if atFall Y k (fG i) then Dew P Z A Yp V q F i x else 0
-- chain
include R' e f
lemma thaw (ξ:ℝ)(uT:3*ξ≤α/4): Chain Y P T θ rB k Z.μwage fG (frozen P Z A k Yp V q (η:=η)) (freeze P Z A k Yp V q F) (Cargo.roomAge D'.p.B (o+o)+4*C) ξ:=by
 let W:= (city_pay V q R').weaken _ _ uT le_rfl; constructor
 · exact lim_toll _ fG vG W
 · intro i h; have hv:atFall Y k (fG i)∧ vG i≠ 0:= by unfold frozen Atmos at h; split at h; exact ⟨‹_›,h⟩; contradiction
   have hz:Micro.Loc (fG i):=groveloc (city_heat V q R' i hv.2); exact ⟨atFall_on k e (city_ne q i) hv.1 hz,hz,f⟩
 · intro i x; unfold freeze frozen Atmos; split; exact (F.loan i).tag.pays _; rw [norm_zero]
 · intro i; change Measurable fun x=> freeze P Z A k Yp V q F i x; unfold freeze; split; exact (F.loan i).meas.comp (measurable_fst.comp (Z.tracks_W P A)); exact measurable_const
 intro i h Λ p x y v; unfold freeze; split; exact (F.loan i).include_b ((Veil.paired (fG i)).1 (Z.recordW P A x y _ p v)).1; exact rfl
omit R' e f
-- Busy vanish unless through. cap. growth uses v separate
abbrev BH:= Palot.Y (More N)
local notation "Μ"=> Palot.Y (More N)
variable (z:ℂ)(zH:‖z‖≤η)
abbrev busyday (i: Palot.Y (More N))(w:Pouch Y P T θ):ℂ:=fBusy (Z.pose P A w) V D' (Z.flagT P w.val) (F_' Y P T θ w.val) (Brick.Act.fields mH g₀ w.val) z (School.rim_ (Y:=Y) k w.val) i
abbrev abroad :Μ→ℝ:= Atmos (through Y k) Subtype.val (fun i=>2*fPrice (κ:=η) V q i)
variable (Dη:thresh y ≤ D'.p.threshold)
include Dη q
lemma across(i:Palot.Y (More N))(p:¬through Y k i.val): busyday P Z A k Yp V z (D':=D') i xw=0:=by -- q arg? doesn't depend q
 apply Veil.busyQuiet V D' q z (School.rim_ (Y:=Y) k xw.val)
 · apply disjoint_left.mpr; intro b u v; obtain ⟨j,h,rfl⟩:= spotsNN _ v; exact p ⟨_,u,_,((Trek.erase_p ..).1 h).1⟩
 apply disjoint_left.mpr; intro b u l; obtain ⟨p',c⟩:= Rhythm.Lease.flag_here P Y T θ (tool Y xw.val) Z.lineT.raw Z.lineT.ok xw.property E.H C' Z.stageU.podium Dη b l; exact p ⟨b,u,Trek.tag mH b,⟨_,p',by unfold Circle.δ; simp [Cube.d_id]⟩⟩
-- charge
include R' zH f
lemma sunset (ξ:ℝ)(p:3*ξ≤ α/4): Chain Y P T θ rB k Z.μwage Subtype.val (abroad (η:=η) P Z A k Yp V q) (busyday P Z A k Yp V (D':=D') z) (2*(4*C)) ξ:=by -- D' for busyday
 let f:Μ→ℝ:= fPrice (κ:=η) V q; have W:= R'.known V q; let p':= (W.prices).weaken _ _ p le_rfl; constructor
 · exact lim_toll _ _ _ (p'.scale _ _ 2 zero_le_two)
 · intro i t; unfold abroad Atmos at t; split at t; exact ⟨‹_›, groveloc (W.logG i (fun h=> t (by dsimp only [fPrice]; rw [h,mul_zero]))), ‹k<Deep.D mH›⟩; contradiction
 · intro i x; unfold abroad Atmos; split; exact busyBill _ _ _ R' _ _ _ _ _ (fun j=> cbra_coin (Z.live_p P _) _ j) zH; rename_i v; rw [across P Z A x k Yp V q z Dη i v, norm_zero] -- tune
 · intro i; exact Veil.busyMeas V D' q z (Z.pose P A) _ _ _ _ (Z.tracks_P P A) ((Z.flagD_m P k).comp measurable_subtype_coe) ((draw_P ..).comp measurable_subtype_coe) (fun i=>(Z.flagT_m P i).comp measurable_subtype_coe) ((Brick.Act.fields_m ..).comp measurable_subtype_coe) i
 intro i _ Λ h x y vT; exact alive V D' q z i (Z.presentB P A x y i.val h vT)
end Air
end YM.CF.BProof.Scope
