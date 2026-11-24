import Bay.Era
import Bay.Crenel
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell

open Py Py.Rate LocalLimit Preparation Buffered.Afterglow.Tower.VacuumSelection
open Zephyr.Chern
open BPress (PL NPL)
local notation "fluxV"=>Zephyr.Chern.stream
local notation "VΩ"=>Buffered.Afterglow.Tower.VacuumSelection.Spine

open Push.Uniform
open Pitching.Focus QuadClock Preparation.Yoke BScale
open Mew Vow.TreasuryFog
open scoped YM.CF.Mew

open Roots


lemma ageFar (P:VΩ)(s:ℕ):Tendsto (fun i:ℕ=>(age P.run i s).val)
 atTop atTop:=by
 let J:=P.par.R.L
 have hz:1<J.val:=(by decide: 1 < (3:ℕ)).trans_le P.par.R.coarse
 have j(i:ℕ) : J.val ^ (P.run.stage i) ≤ (age P.run i s).val:=by
    unfold age Preparation.Ctor Vale.cell CSide Preparation.Course.ir
        YM.CF.Py.Rate.rung Vale.mesh More
    push_cast
    iterate 3 apply le_trans _ (Nat.le_mul_of_pos_right _ (by positivity))
    exact Nat.le_mul_of_pos_left _ (by positivity)
 exact tendsto_atTop_mono j ((tendsto_pow_atTop_atTop_of_one_lt hz).comp P.run.infrared.tendsto_atTop)

abbrev recoat (L:ℕ)(C:ℝ→ℝ)(x:ℝ):=padFee L * C x
lemma recoatRate {C:ℝ→ℝ}(L:ℕ)(p:NPL C):NPL (recoat L C):= chill_iff.mp ((chill_iff.mpr p).leanB (Lor.BoreP.still _))

-- fees for normal openings now with padding.
abbrev icedCost (P:VΩ)(M L:ℕ)(F D:ℝ→ℝ):=
  xPool P M F (recoat L D)

variable {w:Berth} {F C D:ℝ→ℝ}
namespace Berth
abbrev Thermal (w:Berth)(M L:ℕ)(F C D:ℝ→ℝ)(r:blazeK w.side):Prop:=
 Firm w M F (recoat L C) (recoat L D) r ∧
 slabOK w.side L w.p.B∧ w.SlipCount M

end Berth

structure Season (P:VΩ)(M L:ℕ)(F C D:ℝ→ℝ):Prop where
   rate : PinNPL P (icedCost P M L F D)
   ready : Dry P (fun w=>w.Rails → ∃r,w.Thermal M L F C D r)
lemma ripening {P:VΩ}(h:Ice P F)(M L:ℕ)(u:NPL C)(v:NPL D):
 Season P M L F C D := by
 have t:=h.castle M (recoatRate L u) (recoatRate L v)
 refine ⟨poolOf (recoatRate L v) t,?_⟩
 filter_upwards [t.prepares,(Work.E01.radiusB_tendsto.comp (turnover P.par)).eventually_ge_atTop (36*M)] with s k o
 filter_upwards [k,(ageFar P s).eventually_gt_atTop
   (plankN L * weeB (Vale.hat P.par.R.L P.par.x s))] with i hi g
 intro j p q
 let w:=takeUp P s i j
 obtain ⟨r,H⟩:=Berth.readyFirm (hi j p q)
 refine ⟨r,H,?_,?_⟩
 · constructor
   · rw [q.size]
     exact g
   exact (by norm_num:0< (5:ℕ)).trans_le H.wide
 · unfold Berth.SlipCount;rw[q.size];exact o

lemma cooling {P:VΩ}(V:ℝ→ℝ)(v:PinNPL P V)
 (b:ℝ)(e:0<b):Dry P (fun w=> V w.x ≤ b * w.Q):=by
 filter_upwards [(turnover P.par).eventually ((chill_iff.mpr v).spine_a.eventually
  (ge_mem_nhds e)),(turnover P.par).eventually (Till.warm_gt P.par.R)] with s ζ w
 exact Eventually.of_forall (fun i k _=>(div_le_iff₀ w).mp ζ)

-- universal layouts now prepared up to this fee.
namespace Berth
variable (w:Berth) {M L:ℕ} {r:blazeK w.side}
variable {I:Type}[LinearOrder I][Fintype I]
variable (σ:I→Seat w.side) (m:I→ Sour.Bag w.side)

abbrev slab (L:ℕ)(i:I):Support (More w.side):= (plank L w.p.B (σ i)).val -- explicit w? check
abbrev melt (L:ℕ)(i:I):Sour.Bag w.side:=stick L (σ i) w.p.B (m i)
abbrev Cached (L:ℕ)(A B:I→Aura w.side→ℝ)(C D:ℝ→ℝ): Prop:=
 w.Estate (w.slab σ L) (w.melt σ m L) A B (recoat L C) (recoat L D)


abbrev loanY(o:Seat w.side)(V:Sour.Bag w.side)(C D:ℝ→ℝ): Prop:=
 Barrage w.p w.q {o} w.H V (rScale w.p) (C w.x) (D w.x*w.Q)

lemma rootLodge {A:Support (More w.side)}{V:Sour.Bag w.side} {o:Seat w.side}
 (u:Barrage w.p w.q A w.H V (rScale w.p) (C w.x) (D w.x*w.Q))(j:o∈A):
 w.loanY o V C D:=by
 obtain ⟨Z,K,Q,R,z,g⟩:=u.price
 exact ⟨Z,K,Q,fun i v=>R i (fun p=> v (singleton_subset_iff.mpr (p j))),z,g⟩

variable {w σ m}
 (g:w.Thermal M L F C D r)
include g
lemma cacheMine (p:∀ i,w.loanY (σ i) (m i) C D):∃A B,w.Cached σ m L A B C D:=by
 apply sow
 intro i

 have a:w.p.B≥1:=g.2.1.2
 have b:1 ≤ (w.p.B:ℝ):=Nat.one_le_cast.mpr a
 have c:0 ≤ rScale w.p:=by unfold rScale;positivity
 have d:rScale w.p ≤ 9:=by unfold rScale; linarith only [div_le_self (by norm_num:0 ≤ (8:ℝ)) b]
 have u:= sticks L (σ i) (m i) c d a (mem_singleton_self _) (p i)
 rwa[mul_assoc (padFee L) _ w.Q]

omit g in
lemma hearth (L:ℕ)(i:I):σ i∈w.slab σ L i:=
 Lattice.halo_spec.mpr ⟨σ i,mem_singleton_self _,separation_self _ ▸ Nat.zero_le _⟩

variable (mulσ:Multiplicity σ M)(lw:LatticeWide σ w.p.B)
 {E B:I→Aura w.side→ℝ}
include mulσ lw

-- degree: torus gauge count. 
abbrev lampCap (w:Berth):ℕ:=Fintype.card (Seat w.side)

lemma stickerPrice (d:w.Cached σ m L E B C D)
 (s:ℕ)(τ:Ids w.side):
 let U:=w.flareE d σ s τ
 let V:=w.flareF d σ s
 Receives w.p L σ U V w.H (icedCost w.P M L F D w.x)∧
 ∀ i, νTip U i= kilnTip d.bill σ τ i ∧
    emberTip V i=νΦK (rootF w.R (flare d.bill) s) {i}:=by
 apply flared g.1 d σ mulσ lw (hearth _) g.2.2 _ s τ
 intro i y e
 obtain ⟨Y,rfl⟩:=sticksOut _ _ _ _ _ e
 exact plankOut _ g.2.1

end Berth
end YM.CF.Bay
