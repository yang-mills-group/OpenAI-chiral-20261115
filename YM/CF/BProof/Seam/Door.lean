import YM.CF.BProof.Payment.Choice
import YM.CF.BProof.Seam.School
/-! readable scripts on Pouch. Restore Pose on projected fields and frame worlds. -/
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
open Rhythm Tape Hearth Lat
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator Hearth Tape Mark
attribute [local instance] opCStarAlgebra
variable {N₁ N₂:ℕ} {m m':Side}{j:ℕ} {a₁ b l r:ℝ}{D:Spin.Ready j a₁ b l r}{u:ℝ} (E:Essence D u)
variable {rₜ:ℕ} (Δ:Rhythm.Note E (Gates.gap L a) rₜ)(U: Orbit N → Pane N) (ν δ:ℝ)
variable {rB:ℕ}
variable {Y E T θ Δ U ν δ} (Z : School Y T θ E Δ U ν δ rB)
namespace School
local notation "εx" => Rhythm.Lease.wearC S y
local notation "ΨN" => Pouch Y P T θ
local notation "ζ_"=>framesL Y P T θ
local notation "κ_"=>rawG Y P T θ
local notation "C'"=>Δ.clock
include Z P
open Garden Palot Anthem Payment Veil
variable (A: Core j a₁ b l r N)
variable (xw x'w:Pouch Y P T θ)
local notation "ψ" => Z.pose P A
local notation "φ̂"=> Z.hom P A
abbrev world1(xw:Pouch Y P T θ): World N:=((κ_ xw.val, sion (Z.pose P A xw)), Z.stun P xw.val)
abbrev world0 (i:Fin 5): World N:=((1,sion (Z.hom P A i)), Z.homX i)
@[fun_prop] lemma tracks_W : Measurable (Z.world1 P A):= (((raw_m ..).comp measurable_subtype_coe).prodMk (carol.comp (Z.tracks_P P A))).prodMk ((Z.tracks_stun P).comp measurable_subtype_coe)
variable (u':ℕ)
section Cut
variable {I:Type}[Fintype I]
def score (Y:S.Setup L a (More N) d y){m:Side}(f: Ratio m (More N))(u:ℕ)(K:Manus N I)(F:Y.yard.Index→ Pane N→ℝ): Score Y.yard I:=⟨y,Y.hall,m,f,u,K,F⟩
variable (K:Manus N I)(F:Y.yard.Index→ Pane N→ℝ)
local notation "Θ_"=>score Y Z.f u' K F
end Cut
-- broad term for worlds. Score insensitive to marks (except halo). handy bindings reuse
abbrev rim_ (K:ℕ)(x:Pod Y):= Trek.eraseBit mH g₀ K (sick Y x)
def vest(x:Pod Y)(b:Seat N): Spin.Stamp:= if Trek.dark mH b then (Seam.wear Y P T θ Z.f x).K (Trek.hr mH b) b 2 else northW N b
abbrev flagT (x:Pod Y):= cbra (Z.vest P x) (Score.chamber mH univ)ᶜ
local notation "ζx"=> ζ_ xw.val
local notation "χ"=> κ_ xw.val
local notation "ζy"=> world1 P Z A
lemma live_p (i:Seat N): SealH (vest P Z x i):=by unfold vest; split; exact (Trek.nightsM mH _ _ _ _ _ _).1.1 2; exact north_seal _
-- note Z.framesL definition insensitive Y.hL. open gauge. 
variable {I:Type}[Fintype I](K:Manus N I)(F:Y.yard.Index→ Pane N→ℝ)
lemma same_d (x:Pod Y) : Z.flagT P x=desire (score Y Z.f u' K F) (rawG Y P T θ x) (ζ_ x):=rfl
lemma buys(h:Δ.clock.nearM≤u') : Pick (score Y Z.f u' K F) ζx χ (ψ xw) u (rim_ (Y:=Y) u' xw.val) (Z.stun P xw.val):= by
 exact Payment.ticket (score Y Z.f u' K F) ζx χ (ψ xw) (sick Y xw.val) (Z.lamp_ P _ xw.property) (tool Y xw.val).mood (Z.stageU.podium) (Z.lic_ P _ xw.property) (Instructions E P Y Δ Z.buyS).2.1 Z.pt Z.p0 rfl rfl h -- tune
@[fun_prop] lemma flagD_m : Measurable (School.rim_ (Y:=Y) u'):= (measurable_of_countable (f:=Trek.eraseBit mH g₀ u')).comp (sick_m Y)
@[fun_prop] lemma vest_m : Measurable (Z.vest P):=by apply measurable_pi_lambda; intro i; unfold vest; split; exact (book_m Z.f).key (Trek.hr mH i) i 2; exact measurable_const
local instance (I:Type)[Fintype I][DecidableEq I]: MeasurableSpace (Op I):=borel _
local instance (I:Type)[Fintype I][DecidableEq I]: BorelSpace (Op I):=⟨rfl⟩
@[fun_prop] lemma flagT_m (x:Site N) : Measurable fun s:Pod Y=> (Z.flagT P s).leaf x:=by unfold flagT cbra Plant.patch; dsimp only; split; exact measurable_const; exact ((plump_cont (chef x)).comp (Spin.pair_cont (N:=N))).measurable.comp (Z.vest_m P)
variable (μ:Support (More N)) {Λ:Finset (House.Block Y.yard Y.c')}
local notation "Fine"=> Lattice.halo Z.μwage μ
local notation "μz"=> Z.μwage
variable (D':Probe Y P T θ Λ (Lattice.halo Z.μwage μ))(ε:Esp Y rB Λ xw.val x'w.val)
lemma beanP{i:Seat N}(h:i∈μ): Lattice.halo Z.μwage {i} ⊆ Lattice.halo Z.μwage μ:= Lattice.Corona.halo_mono le_rfl (singleton_subset_iff.mpr h)
include D' ε
lemma region : (window N).agree μ (Z.world1 P A xw).1.2 (Z.world1 P A x'w).1.2:=by
 apply (Veil.equalize μ _ _).2; let ε' := esp_here Y xw.val x'w.val rB ε; refine ⟨?_,?_,?_⟩
 · exact (pine_eq ..).2 (agrees_mono (D'.operation Δ.clock x'w.val Z.stageU Z.lineT ε xw.property x'w.property) (Finset.coe_subset.mpr (Lattice.halo_subset ..))) -- Tune
 · apply (shoots_rule μ).2; intro i v; by_cases p: ∃ x:Site N,node x=i
   · obtain ⟨x,rfl⟩:=p; rw [spot_spec,spot_spec]; exact D'.present x'w.val ε' (Lattice.halo_subset _ _ v)
   apply iff_of_false (fun h=>p ?_) (fun h=>p ?_) <;> obtain ⟨j,h,k⟩:= spotsNN _ h<;> exact ⟨j,k⟩
 apply (curve_rule μ).2; intro i p; change Tape.drawQ _ (Z.capital P xw i)=Tape.drawQ _ (Z.capital P x'w i); apply Tape.eq_draw; exact D'.stockC Z.f Δ.clock Z.p Z.ft Z.pt (Z.warmZ P) x'w.val Z.stageU Z.lineT ε xw.property x'w.property i (Z.beanP P μ p) -- tune
lemma recordW : (world N).agree μ (ζy xw) (ζy x'w):=by
 apply (Veil.paired μ).2; have ε':=esp_here Y xw.val x'w.val rB ε; have hp:(quiet N).agree μ (ζy xw).1 (ζy x'w).1:= (Veil.paired μ).2 ⟨(pine_eq ..).2 (agrees_mono (D'.lawn xw.val x'w.val xw.property x'w.property ε') (Finset.coe_subset.mpr (Lattice.halo_subset ..))),Z.region P A xw x'w μ D' ε⟩; refine ⟨hp,(tent_eq μ).2 (fun i h=> ?_)⟩; exact D'.xerox Z.f Δ.clock Z.p Z.ft Z.pt (Z.warmZ P) x'w.val Z.stageU Z.lineT ε xw.property x'w.property i (Z.beanP P μ h)
lemma same_vest{i:Seat N}(p:i∈μ): vest P Z xw.val i= vest P Z x'w.val i:=by
 unfold vest; split; next h=>
    apply congrFun; exact (D'.spins Z.f (Z.warmZ P) Z.ft x'w.val xw.property x'w.property (esp_here Y xw.val x'w.val rB ε) (band_pick mH i h) ((Lattice.Corona.halo_mono (by unfold μwage MaxFeet silhouette; omega : 2*Z.f.count.val ≤ Z.μwage) (singleton_subset_iff.mpr p)))).2
 rfl
local notation "phaseM"=> Brick.Act.fields mH g₀
lemma presentB {u:ℕ} : Veil.Shade μ (rim_ u xw.val) (rim_ u x'w.val) (ψ xw) (ψ x'w) (F_' Y P T θ xw.val) (F_' Y P T θ x'w.val) (Z.flagT P xw.val) (Z.flagT P x'w.val) (phaseM xw.val) (phaseM x'w.val):=by
 have ε':=esp_here Y xw.val x'w.val rB ε; have ht:(quiet N).agree μ ((ζy xw).1) ((ζy x'w).1):=((Veil.paired μ).1 (Z.recordW P A xw x'w μ D' ε)).1; have hp(i:Seat N)(t:i∈μ):πX i∈Λ:= D'.home (Lattice.halo_subset μz μ t); refine ⟨ht,fun i h=> Brick.Act.tag_id mH g₀ i (hp i h) ε',fun i h=>Brick.Act.phase_y mH g₀ i (hp i h) ε',fun i h=> ⟨?_,Brick.Act.phase_z mH g₀ i (hp _ h) ε', D'.excuse x'w.val ε' (Lattice.halo_subset μz μ h) u⟩⟩
 unfold flagT cbra Plant.patch; dsimp only; split; exact rfl; exact Garden.leaf_eq (Z.same_vest P xw x'w μ D' ε h)
end School
end YM.CF.BProof.Seam
