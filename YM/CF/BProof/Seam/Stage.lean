import YM.CF.BProof.Cabinet.Revere
import YM.CF.BProof.Rhythm.Kiosk

/-! Geometric permissions; same-gap read transitions. Extra room bought at any further
L_c raise/delays. -/
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
abbrev Speed := T.Bounds c w R v
abbrev rawG := area P Y T θ (Cabinet.tool Y x)
@[fun_prop] lemma raw_m : Measurable (rawG Y P T θ):=(Pawn.put_m ..).comp (Brick.Act.pawn_m ..)
lemma hiddenD (f: Site (More N)): hide Y.yard Y.g (gE f, space f)=πX f:=rfl
-- ambiguity space
lemma bit_first(i:Seat N): House.one mH (πX i)= Trek.tag mH i:=rfl
variable {u v':ℝ}(H:Mark.Herald u v'){t:ℕ}(C:Sized t H.whole) (r:ℕ)
-- includes Loom radius rₜ bound C.blockY. ∆ depth from gap endpoints. µ halo for flag support 20 extra
abbrev dome := 4*C.nearM+60
structure SiteUp : Prop where
 podium : Trek.Pad mH H C Y.g.count.val -- ambiguous
 room_d : dome H C+20<Deep.D mH
 room_c : dome H C+20≤ Y.g.count.val
 premium : 200 ≤ r
variable {H C r} -- tune
variable (W:SiteUp Y H C r)
lemma nearhood {A:Finset (House.Block Y.yard Y.c')}{r:ℕ}{i:Seat N}: ¬Trek.distant mH g₀ A i r↔ πX i∈ Cabinet.halo Y A r:=by rw [Cabinet.halo_spec,distant,ClearB,hiddenD]; exact not_disjoint_iff
lemma germ {r:ℕ} {i j:Seat N}(p:gE i=gE j)(v:separation i j≤r*Y.g.count.val): πX j ∈ ray mH (πX i) r :=by rw [House.ray_spec]; refine ⟨?_,p.symm⟩; rw [← hiddenD, ← hiddenD,p]; exact Trek.hide_close mH g₀ (gE j) ((Trek.spaceClose ..).trans v)
include W
lemma insizes(k:ℕ)(p:k≤dome H C+20): 2*k+1<Y.yard.long ∧ k≤Y.g.count.val∧ k<Deep.D mH:=by have :=W.room_d; have :=W.room_c; have := Deep.D_le mH; omega
-- geographic argument includes everywhere over Q (all gap slices); flag stays by depth and plate. uniform constants.
def Planet (A: Finset (Block Y.yard Y.c'))(k u:ℕ) := Finset.univ.filter fun x:Seat N=> Y.yard.Vic (gE x) k (time x)∧ πX x ∈ Cabinet.halo Y A u -- tune
omit W
@[simp] lemma zone_mem (A:Finset (Block Y.yard Y.c')){i:Seat N}(k u:ℕ): i∈ Planet Y A k u↔ Y.yard.Vic (gE i) k (time i) ∧ πX i∈Cabinet.halo Y A u:= by simp only [Planet,mem_filter,mem_univ,true_and]
lemma planet_le (A:Finset (Block Y.yard Y.c'))(k u L t:ℕ)(g:k≤L)(h:u≤t): Planet Y A k u ⊆ Planet Y A L t := by intro i h'; obtain ⟨p,v⟩:= (zone_mem ..).1 h'; exact (zone_mem ..).2 ⟨Y.yard.vic_nearer _ _ _ _ g p,Cabinet.nearer Y _ _ Subset.rfl h v⟩
lemma ray_plate{Q:Cores Y r}{b:House.Block Y.yard Y.c'}{k:ℕ}(h:b∈ Cabinet.halo Y Q.val k)(p:k≤r): b∈ plate Y r Q:= by rw [plate, Tower.whole]; exact Grid.collar_le Subset.rfl p (Cabinet.halo_close Y _ h)
include W
lemma zone_up (A:Finset (Block Y.yard Y.c'))(k v μ:ℕ)(p:k+μ≤dome H C+20) : Lattice.halo μ (Planet Y A k v) ⊆ Planet Y A (k+μ) (v+1):=by
 intro i q; obtain ⟨j,g,o⟩:=Lattice.halo_spec.mp q; obtain ⟨u,t⟩:=(zone_mem ..).1 g; have ht:= Trek.rlink mH o (insizes Y W _ p).1 u; rw [zone_mem,ht]; refine ⟨Trek.along_t mH j i (gE j) u o,?_⟩; obtain ⟨b,l,g⟩:=(halo_m ..).1 t; refine (halo_m ..).2 ⟨b,l,ray_net Y _ _ g (germ Y ht.symm (by rw [one_mul];exact o.trans (insizes Y W μ (le_trans (by omega) p)).2.1))⟩ -- tune
lemma into_zone(Q:Cores Y r)(i:Bond (More N)){u:ℕ}(t:u≤ C.blockY)(j:Seat N)(g:j∈Skye.ends i)(p:j∈Planet Y Q.val C.blockY 2): Lattice.halo u (Skye.ends i)⊆ Planet Y Q.val (dome H C) 40:=by
 intro b v; have hp:=Trek.immediate i.1 i.2; have hx:= C.near; let m:= C.blockY; have hl:m+(u+1)≤dome H C:= by unfold m dome; omega
 apply planet_le Y _ _ _ _ _ hl (by decide : 2+1 ≤ 40) (zone_up Y W Q.val _ 2 (u+1) (le_trans hl (by omega)) ?_); obtain ⟨x,l,k⟩:=Lattice.halo_spec.mp v; apply Lattice.halo_spec.mpr; have hf: separation j x≤1:=by -- ends namespace?
    simp only [Skye.ends,mem_insert,mem_singleton] at *; rcases l with rfl|rfl <;> rcases g with g|g <;> rw [g] <;> first | exact hp|simp only [separation_self,Nat.zero_le] | exact (separation_comm ..).trans_le hp -- tune
 refine ⟨_,p,(separation_triangle j x b).trans (by omega)⟩
end YM.CF.BProof.Seam
