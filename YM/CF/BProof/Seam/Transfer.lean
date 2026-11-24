import YM.CF.BProof.Seam.Stage

/-! VolumeB-vac use exact Roof.transmission on an enlarged plate. -/
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
variable (T': T.Bounds c w R v)(k: θ∈Set.Icc (1/2) 2)
local notation "Raw_"=>rawG Y P T θ
abbrev paint (U:Orbit N→Pane N) := U ((rawG Y P T θ x),Brick.Act.ids mH g₀ x)
-- threshold ν fixed before y. actual ≤ repair.
variable {u v':ℝ}{H:Mark.Herald u v'}{t:ℕ}{C:Sized t H.whole}{r:ℕ}
structure Line (W:SiteUp Y H C r)(T:PathData G)(θ uL d:ℝ)(u:ℕ)(S:Orbit N→Pane N): Prop where
 raw : T.Bounds c w R v
 ok : θ∈Set.Icc (1/2) 2
 roof : Roof N uL d u S
 sees : thresh y ≤ uL
 pays : u ≤ C.blockY
 safe : 0 ≤ d
 height : d ≤ H.calm
variable {U : Orbit N→Pane N}(Q:Cores Y r)
variable (x':Pod Y)(e:Cabinet.Ready P Y T θ x)(p:Cabinet.Ready P Y T θ x')(l:Q∈ recital Y r x)(l':Q ∈ recital Y r x')
local notation "rawK"=> rawG Y P T θ
local notation "Δ0"=> Planet Y Q.val (dome H C) 40  -- parser token numeric delta?
variable {θ' d':ℝ}{j:ℕ} (W:SiteUp Y H C r)(T₀: Line Y W T θ θ' d' j U)
include e p
lemma prior_step (z:Bond (More N)){V:Finset (Block Y.yard Y.c')}(p':Spiced Y V x x')(v:House.ray mH (πX z.1) 1 ⊆ V) (t:ℕ)(h:t<2*Deep.D mH)(g: Y.yard.Vic (gE z.1) t (time z.1)): rawK x z=rawK x' z :=by
 apply Pawn.chops g₀ Y.hall _ _ V y T θ (Cabinet.parcelT P Y) (Gates.Stage.Setup.room P Y) (Brick.Act.agrees mH g₀ p') (proceeds P Y T θ _ e).2.2.1 (proceeds P Y T θ _ p).2.2.1 z.1 g h z rfl; exact House.ray_loan mH g₀ V 1 (by rw [chrono P Y]; have :=(agenda P Y).coverage; omega) (by rw [hiddenD]; exact v) -- tune
include W
lemma pane_raw (v:Spiced Y (plate Y r Q) x x') : Agrees (↑(Lattice.halo 8 Δ0)) (rawK x) (rawK x'):=by
 intro i q _; obtain ⟨hz,h⟩:= (zone_mem ..).1 (zone_up Y W Q.val (dome H C) 40 8 (by omega) (show i.1∈ Lattice.halo 8 Δ0 from q))
 apply prior_step Y P T θ x x' e p i v _ (dome H C+8) _ hz
 · intro b hb; obtain ⟨z,p,k⟩:= (Cabinet.halo_m ..).1 h; exact ray_plate Y ((Cabinet.halo_m ..).2 ⟨z,p,Cabinet.ray_net Y 1 _ k hb⟩) (by have := W.premium; omega)
 have := W.room_d; omega -- tune order by apply tactic
omit p
include T₀ l
lemma zone_mask : Lattice.halo (2*j+20) ((flags θ' (rawK x)) ∩ Δ0) ⊆ Δ0 :=by
 intro i v; have hl:= W.premium; obtain ⟨b,v,h⟩:=Lattice.halo_spec.mp v; obtain ⟨hz,v⟩:= mem_inter.mp v; obtain ⟨p,u⟩:= Rhythm.Lease.flag_here P Y T θ _ T₀.raw T₀.ok e H C W.podium T₀.sees b hz
 have hc:πX b ∈ Cabinet.halo Y (sick Y x) 1:= (nearhood Y).1 u; obtain ⟨z,s,k⟩:= (Cabinet.halo_spec ..).1 hc; obtain ⟨m,g,p'⟩:= (Cabinet.halo_m ..).1 ((zone_mem ..).1 v).2; have ht:= actualCore Y r Q l (enlargement Y x s) (ray_plate Y ((Cabinet.halo_m ..).2 ⟨m,g,ray_net Y _ _ p' k⟩) (by omega)); have u':2*j+20≤ dome H C:=by have := C.near; have := T₀.pays; unfold dome; omega
 refine planet_le Y _ _ _ _ _ (show 0+(2*j+20)≤dome H C from by omega) (by decide : 1+1 ≤ 40) (zone_up Y W _ 0 1 (2*j+20) (by omega) (Lattice.halo_spec.mpr ⟨b,(zone_mem ..).2 ⟨⟨_,p,by unfold Circle.δ;simp only [Cube.d_id]; exact le_rfl⟩,(Cabinet.halo_spec ..).2 ⟨z,ht,k⟩⟩,h⟩))
include l p l'
lemma transmission (v:Spiced Y (plate Y r Q) x x')(i:Bond (More N))(z:Seat N)(w:z∈Skye.ends i)(hz:z∈Planet Y Q.val C.blockY 2): paint Y P T θ x U i=paint Y P T θ x' U i:=by
 let E:=Δ0; have hp:Agrees (↑(Lattice.halo 8 Δ0)) (rawK x) (rawK x'):=pane_raw Y P T θ x Q x' e p W v; have hP:= zone_mask Y P T θ x Q e l W T₀; have hv':=zone_mask Y P T θ x' Q p l' W T₀; have g:=into_zone Y W Q i T₀.pays z w hz; have hh: Set.EqOn (Brick.Act.ids mH g₀ x) (Brick.Act.ids mH g₀ x') (↑E) :=fun i k=> Brick.Act.tag_id mH g₀ i (ray_plate Y ((zone_mem ..).1 (show i∈ E from k)).2 (by have := W.premium; omega)) v
 have he:= T₀.roof.transmission (rawK x) (rawK x') _ _ Δ0 (Skye.ends i) (RG.flags_agree θ' _ _ _ (agrees_mono hp (Finset.coe_subset.mpr (Micro.inspected_sub ..)))) (keepsL _ _ _ _ hP g) (keepsL _ _ _ _ hv' g) (agrees_mono hp (Finset.coe_subset.mpr (Lattice.halo_subset ..))) hh
 exact he i (by simp [Skye.ends]) (by simp [Skye.ends])
omit W T₀ e l p l'
variable (Φs:Finset (House.Block Y.yard Y.c'))
abbrev RtA:= Esp Y r Φs x x'
lemma chill_seen (i:Seat N)(g: House.ray mH (πX i) 2⊆ Φs)(p:Spiced Y Φs x x')(k:ℕ) : i∈ ChillF mH g₀ (sick Y x) k ↔ i∈ ChillF mH g₀ (sick Y x') k:=by
 refine or_congr_right ?_ -- mathlib or???
 unfold distant ClearB; rw [Finset.disjoint_left, Finset.disjoint_left,hiddenD]; refine forall_congr' fun b=>?_ ; by_cases d:b∈ ray mH (πX i) 2; swap; · tauto -- tune defeq
 rw [show b∈sick Y x ↔ b∈sick Y x' from Brick.Act.sick_id mH g₀ y p _ (g d)]
-- visible core with that witness for Unsafe.
local notation "CC"=> ChillF mH g₀ (sick Y x) C.blockY
include W
lemma beholds (u:Esp Y r Φs x x'){j:Seat N}(p:j∉ CC)(g:House.ray mH (πX j) 2⊆Φs): ∃ Q:Cores Y r,Q∈recital Y r x ∧ Q∈ recital Y r x' ∧ Spiced Y (plate Y r Q) x x'∧ j∈ Planet Y Q.val C.blockY 2:=by
 obtain ⟨p,q⟩:=Trek.nearB mH g₀ _ _ _ p; obtain ⟨b,l,h⟩:= not_disjoint_iff.mp (show ¬ Disjoint (sick Y x) (ray mH (πX j) 2) from q); obtain ⟨Q,t,k⟩:=atOwn Y r (enlargement Y x l); have hv:Q∈touchT Y r Φs x:= mem_filter.mpr ⟨t,not_disjoint_iff.mpr ⟨b,(plan wB r).sub Q k,g h⟩⟩; exact ⟨Q,t,esp_bit Y x x' r u Q hv, esp_paid Y x x' r u Q hv, (zone_mem ..).2 ⟨p,(Cabinet.halo_spec ..).2 ⟨b,k,h⟩⟩⟩ -- tune hygiene
include T₀ e
abbrev LitUp(x:Pod Y) := Trek.Lamp C Y.g (sick Y x) d' (rawK x) (paint Y P T θ x U)
lemma beam_: Trek.Lamp C Y.g (sick Y x) d' (rawK x) (paint Y P T θ x U):= Rhythm.Lease.lineLamp P Y T θ _ T₀.raw T₀.ok e H C W.podium T₀.sees T₀.pays d' T₀.safe T₀.height U T₀.roof (Brick.Act.ids mH g₀ x)
include p
lemma ray_support (Φ:Esp Y r Φs x x')(i:Bond (More N))(g:∀ j∈Skye.ends i, ray mH (πX j) 2 ⊆ Φs)(h: rawK x i=rawK x' i): paint Y P T θ x U i= paint Y P T θ x' U i:=by
 by_cases q:∀ j∈ Skye.ends i,j∈CC; swap
 · push Not at q; obtain ⟨j,l,t⟩:=q; obtain ⟨Q,a,b,v,h⟩:=beholds Y x x' W Φs Φ t (g _ l); exact transmission Y P T θ x Q x' e p a b W T₀ v i j l h
 have hq:∀ j∈ Skye.ends i,j∈ ChillF mH g₀ (sick Y x') C.blockY:= fun j l=> (chill_seen Y x x' Φs j (g _ l) (esp_here Y x x' r Φ) _).1 (q j l)
 apply Eq.trans ((beam_ Y P T θ x e W T₀).outside i (q _ (by simp [Skye.ends])) (q _ (by simp [Skye.ends]))).symm; rw [h]; exact (beam_ Y P T θ x' p W T₀).outside i (hq _ (by simp [Skye.ends])) (hq _ (by simp [Skye.ends]))
end YM.CF.BProof.Seam
