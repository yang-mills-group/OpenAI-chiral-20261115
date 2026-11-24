import YM.CF.BProof.Seam.Fashion
import YM.CF.BProof.Trek.Spend
/-! Motion through actual scripts over Unsafe. Dependency footprint: budget Pose. -/
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
variable {u v':ℝ}{H:Herald u v'}{t:ℕ}(C:Sized t H.whole){m':Side}(p:Ratio m' (More N))(A:Orbit N→ Pane N)
abbrev silhouette(t:ℕ)(n m:ℕ) := (2*n+4*m+t)
abbrev MaxFeet := silhouette C.extentT f.count.val p.count.val
local notation "maxF" => MaxFeet f C p -- order tune
local notation "HFx" => Seam.wear Y P T θ f
abbrev XX_ := (HFx x).XX C Y.g (Cabinet.sick Y x) (Seam.paint Y P T θ x A) p
abbrev HH_ := (HFx x).HH C Y.g (Cabinet.sick Y x) (Seam.paint Y P T θ x A) p
abbrev F_'(x:Pod Y) := (rawG Y P T θ x,Brick.Act.ids mH g₀ x)
local notation "ĝ"=>F_' Y P T θ
@[fun_prop] lemma draw_P : Measurable (ĝ) := (raw_m ..).prodMk (Brick.Act.ids_m ..)
variable {Y P T θ A} 
lemma sick_m (Y:S.Setup L a (More N) d y) : Measurable (Cabinet.sick Y):=by
 -- exact vis via // find
 apply measurable_to_countable'; intro z; exact Brick.Act.sick_vis Y.yard Y.g y z
lemma book_m : Tonic (Seam.wear Y P T θ f):= production K_ f _ _ _ (raw_m ..) (frames_m ..) ((Pawn.mood_m ..).comp (Brick.Act.pawn_m ..)) -- tune
variable {x} {μ:Support (More N)}{Λ:Finset (House.Block Y.yard Y.c')}

@[fun_prop] lemma XX_m(Bv:Measurable A) : Measurable (fun x:Pod Y =>XX_ Y P T θ x f C p A):=by
 -- construction precedes guards
 let U:Pod Y→ Pane N := A ∘ (ĝ); apply mealM (F:=sick Y) _ («G»:=fun z x=> (HFx x).XX C g₀ z (U x) p); exact fun z=> (book_m f).Xbuild C g₀ U (Bv.comp (draw_P ..)) p z -- tune
 intro z; exact sick_m Y (measurableSet_singleton _)
@[fun_prop] lemma HH_m(Bv:Measurable A) (i:Seat N)(v:ℝ) : Measurable (fun x:Pod Y=>HH_ Y P T θ x f C p A i v):=by
 apply mealM (F:=sick Y) (fun z=> sick_m Y (measurableSet_singleton _)) («G»:=fun z x=> (HFx x).HH C g₀ z (A (ĝ x)) p i v); exact fun z=> (book_m f).Hbuild C g₀ _ (Bv.comp (draw_P ..)) p z i v -- tune

lemma HeatX(k:Seat N)(A Z:Set (Seat N))(h:∀ i,separation k i≤ C.extentT→ (i∈A ↔ i∈Z)) : C.live A k= C.live Z k:=by
 have p(A Z:Set (Seat N))(g:∀ i,separation k i≤ C.extentT→ (i∈A → i∈Z)) : Knob.aim A C.extentT k ≤ Knob.aim Z C.extentT k:=(Knob.stepZ ..).2 ⟨Knob.ltr ..,fun z p=> Nat.le_of_not_lt (fun l=>p (g z (l.le.trans (Knob.ltr ..)) (Knob.vital A C.extentT k z l)))⟩
 unfold Sized.live; rw [le_antisymm (p A Z fun i p=> (h i p).1) (p Z A fun i p=>(h i p).2)]
variable (T':Probe Y P T θ Λ μ)(F:4≤m.val)(F':4≤m'.val)(W:Hero.Width f Y.yard.long)(x':Pod Y){r:ℕ}(U:SiteUp Y H C r){ν δ:ℝ}{j:ℕ}(R': Line Y U T θ ν δ j A)
variable (ε:Esp Y r Λ x x')(e:Cabinet.Ready P Y T θ x)(l:Cabinet.Ready P Y T θ x')
namespace Probe
variable (φ: Spiced Y Λ x x')
include φ T'
lemma sameTag {y:Seat N}(g:y∈μ): (HFx x).code y=(HFx x').code y:=by
 obtain ⟨i,t,h,q⟩:= Trek.sideN mH (gE y); change planeN _ _ _ _=planeN _ _ _ _; rw [q, Trek.planeν mH h,Trek.planeν mH h]; refine (Brick.Act.agrees mH g₀ φ).mood i t _ h ?_; rw [← q,hiddenD]; exact T'.home g
lemma someSpice {v:Seat N}(g:v∈ μ){r:ℕ}(t:r≤8): distant mH g₀ (sick Y x) v r ↔ distant mH g₀ (sick Y x') v r := by
 unfold distant ClearB; rw [hiddenD, Finset.disjoint_right,Finset.disjoint_right]; refine forall_congr' fun b=> ?_; by_cases d:b∈ ray mH (πX v) r; rw [show b∈ sick Y x ↔ b∈sick Y x' from Brick.Act.sick_id mH g₀ y φ _ (T'.door v g (ray_in mH 8 t d))]; tauto
lemma present {v:Site N}(g:node v∈ μ): v∈Pins mH g₀ (sick Y x) ↔ v∈Pins mH g₀ (sick Y x'):= by rw [pins,pins,someSpice T' x' φ g (by decide : 6≤8)]
lemma excuse {v:Site N}(g:node v∈ μ)(r:ℕ): v ∈ Trek.eraseBit mH g₀ r (sick Y x) ↔ v∈Trek.eraseBit mH g₀ r (sick Y x'):=by rw [Trek.erase_p,Trek.erase_p, someSpice T' x' φ g (by decide : 6≤8)]
local notation "Ζx"=> ChillF mH g₀
local notation "Cx"=> ChillF mH g₀ (sick Y x) C.blockY
local notation "Cy"=> ChillF mH g₀ (sick Y x') C.blockY
lemma health (i:Seat N)(v:i∈μ):i∈Cx ↔ i∈Cy:=chill_seen Y x x' Λ i ((ray_in mH 8 (by decide : 2 ≤ 8)).trans (T'.door i v)) φ _

-- aim price, all read on same aids
lemma heat (υ:Seat N)(vμ:Lattice.halo (maxF) {υ} ⊆ μ) : C.live Cx υ=C.live Cy υ:=by
 apply HeatX; intro z h; apply health C T' x' φ z; apply vμ; have ht:C.extentT≤ MaxFeet f C p:= (by unfold MaxFeet silhouette; omega); exact Lattice.halo_spec.mpr ⟨υ,mem_singleton_self υ,h.trans ht⟩ 

include F e l W
lemma stepsA(z: Seat N)(p:Lattice.halo (2*f.count.val) {z}⊆ μ): (HFx x).over z=(HFx x').over z∧(HFx x).port C z=(HFx x').port C z:=by
 have he:=Lattice.halo_subset (2*f.count.val) {z} (mem_singleton_self z); have hv:=(sameTag f T' x' φ (p he)); by_cases h:dark mH z; swap; · unfold Script.port Script.over; rw [if_neg h,if_neg h,if_neg h,if_neg h,hv]; exact ⟨rfl,rfl⟩
 let i:= Trek.hr mH z; have hh:z∈Y.yard.band i:= band_pick mH z h; obtain ⟨ht,hu⟩:= spins f T' W F x' e l φ hh p; rw [Script.over_band _ _ _ hh,Script.over_band _ _ _ hh,Script.port_band _ _ _ _ hh,Script.port_band _ _ _ _ hh]; refine ⟨ht,?_⟩; unfold Script.curv; split; next u=>
    rw [hv,show (HFx x).frame i z=(HFx x').frame i z from congrArg Inv.inv (T'.eye x' e u.1 hh φ l (p he))]; -- OK
 exact hu
omit F e l W φ
-- loan radius
lemma cut_a (υ:Seat N)(vμ:Lattice.halo (maxF) {υ} ⊆ μ) (j:Seat N)(u:separation υ j ≤4*p.count.val): j∈μ:= vμ (Lattice.halo_spec.mpr ⟨υ,mem_singleton_self _,u.trans (by unfold MaxFeet silhouette; omega)⟩)
lemma cut_b (υ:Seat N)(vμ:Lattice.halo (maxF) {υ} ⊆ μ) (j:Seat N)(u:separation υ j≤ 4*p.count.val): Lattice.halo (2*f.count.val) {j}⊆ μ:=by
 intro x h; simp only [Lattice.halo_spec, exists_eq_left,mem_singleton] at h; apply vμ; exact Lattice.halo_spec.mpr ⟨_,mem_singleton_self _,(separation_triangle υ j x).trans ((Nat.add_le_add u h).trans (by unfold MaxFeet silhouette; omega))⟩
include F' φ
lemma pinP (υ:Seat N)(vμ:Lattice.halo (maxF) {υ} ⊆ μ) {D:Entity 4 m'}(e:D.Mem p υ)(q:Entity 4 m')(t:q.Under D): q∈Hero.pin p Cx ↔ q∈Hero.pin p Cy:=by
 refine exists_congr (fun z=>?_) -- tune unfold
 apply and_congr_right; intro r; apply forall_congr'; intro y; apply imp_congr_right; intro h; refine health C T' x' φ y (cut_a f C p T' υ vμ y ?_); let j:=q.first p; have ht:q.Mem p j:=q.mem_first p; exact (separation_triangle υ j y).trans ((Nat.add_le_add (Fence p D υ j e (t.sites p F' ht)) (Fence p (Platform z) j y (r.sites p F' ht) h)).trans (by omega))
omit φ F'
include U R' ε e l
lemma operation : Agrees (↑μ) (Seam.paint Y P T θ x A) (Seam.paint Y P T θ x' A):=by
 intro i a b; apply ray_support Y P T θ x x' e l U R' Λ ε i _ (T'.lawn x x' e l (esp_here Y x x' r ε) i a b); intro j k; apply (ray_in mH 8 (by decide : 2≤8)).trans (T'.door j _); simp only [Skye.ends,mem_insert,mem_singleton] at k; rcases k with h|h; exact h.symm ▸ a; exact h.symm ▸ b
include W F F'
lemma xerox (υ:Seat N)(vμ:Lattice.halo (maxF) {υ} ⊆ μ) : XX_ Y P T θ x f C p A υ=XX_ Y P T θ x' f C p A υ:=by
 let D:=Grid.Entity.chief p υ; have he:D.Mem p υ:= (Grid.Entity.zero_proper p F' υ).1; have hh:= esp_here Y x x' r ε
 have ht(z:Seat N)(h:D.Mem p z):separation υ z ≤4*p.count.val:=(Fence p D υ z he h).trans (by omega)
 let U'(x):=(A (ĝ x)); let f'(x):=(HFx x).guardX C g₀ (sick Y x); change expandX p (Hero.pin p Cx) (f' x) (U' x) υ = expandX p (Hero.pin p Cy) (f' x') (U' x') υ
 refine (expandX_eq p _ _ _ D F' _ (pinP f C p T' F' x' hh υ vμ he) (f' x') (U' x') (fun z h=>?_) (agrees_mono (operation C T' x' U R' ε e l) (fun z h=>cut_a f C p T' υ vμ z (ht z h))) he)
 unfold f' Script.guardX; have hv:=health C T' x' hh z (cut_a f C p T' υ vμ z (ht z h)); by_cases g:z∈Cx; rw [if_pos g,if_pos (hv.mp g)]; exact (stepsA f C T' F W x' e l hh z (cut_b f C p T' υ vμ z (ht z h))).1; rw [if_neg g,if_neg (fun t=> g (hv.mpr t))] -- tune
lemma stockC (υ:Seat N)(vμ:Lattice.halo (maxF) {υ} ⊆ μ) : HH_ Y P T θ x f C p A υ= HH_ Y P T θ x' f C p A υ:=by
 have hu:= esp_here Y x x' r ε; have he:= T'.heat f C p x' hu υ vμ; have ht:=T'.xerox f C p F F' W x' U R' ε e l υ vμ; have hv:= (T'.stepsA f C F W x' e l hu υ (cut_b f C p T' υ vμ υ (by simp))).2; unfold HH_ Script.HH; rw [he,hv]; unfold XX_ at ht; rw [ht]
end Probe
end YM.CF.BProof.Seam
