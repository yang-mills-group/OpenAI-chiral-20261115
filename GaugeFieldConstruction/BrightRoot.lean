import GaugeFieldConstruction.Sotto
import GaugeFieldConstruction.Soapstone
set_option autoImplicit false
set_option maxRecDepth 5500
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 320000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.XGarden
open Function Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG WilsonStartup Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical
open Buffered Buffered.Region FlightFlux Fluxim Work Tensor
open Fock Tulip Lat Spire Phase Cube Scroll Paige Vault Phase Spire Branch
open Push.SectorMeasure
attribute [local instance] opCStarAlgebra
variable {n:Side}
namespace MastTin
open Shield Echo Ledger Jet Salt Pastry Hake Urn Levier Hive Nacre Rush Peaks
local notation "GS"=>SU.group
open Next.SectorChange.Motion Ione
open TableF.Lenten TableF.Lenten.Housing TableF.Lenten.Layout
open Haro
open scoped YM.CF.Mew
namespace ArtCart
open Buffered Lifted Girt Skye Window Vale
variable {x y:Cover}{d:ℕ}{k:Side}
open TableF TableF.Lenten Layout Flot Moto Tap Bank ModuleB Haro Hove Fren Work.F03 Taxi Ember Fir HushP
variable {F H:Paper n}{p:BudgetPoint}{c v h r:ℝ}(M: Male){o:Seat n}
open Spectrix Simmer Next.Rank.Spindle
open Gleam Gleam.Guide Fock.Flux
open Py.Rate.LocalLimit.Papal Py.Rate.LocalLimit.Papal.FrameP
-- θ.Ship manifestation $pR`. Tick frame transport from **fixed** Reifier to any actual $l$.
variable (x n k)
variable {cT:Side}
abbrev Θk (cT:Side)(x:Cover): Seat cT:= wrap (More cT) x
abbrev StampSet(cT:Side)(x:Cover):= Frills (Θk cT x)
abbrev LiftSeat {cT:Side}(i:StampSet cT x): Cover:= prospect x (i.1.val.1)
abbrev LiftK {cT:Side} (x:Cover)(k:Side)(i:StampSet cT x):Face (Per (More k)):= (wrap (More k) (LiftSeat (cT:=cT) x i),i.1.val.2)
abbrev coupon {cT:Side}(x:Cover)(k:Side)(i:StampSet cT x): Gleam.Guide.Tick (More k) SU.group := ⟨(LiftK (cT:=cT) x k i).1,stab ((LiftK (cT:=cT) x k i).2,none),i.2⟩
lemma seat_e (i:StampSet cT x): i.1.val.1∈knotX x 24 cT:= (Finset.mem_filter.mp i.1.property).2 (Work.E01.base_touched _)
lemma deck_R (hX:300<cT.val) (i:StampSet cT x): deckQ (LiftSeat (cT:=cT) x i) i.1.val.2 ⊆ cartO x 24:=by
 let z:=LiftSeat (cT:=cT) x i; let v:=i.1.val; let q:=v.2; have he:= (prospect_R ..).2 (seat_e x i); have hp: touched v= (deckQ z q).image (wrap (More cT)):=by rw [← touchK, show wrap (More cT) z=v.1 from prospect_eta ..]; -- tune
 let W:= cartO x 24; have hv: (deckQ z q).image (wrap (More cT)) ⊆ W.image (wrap (More cT)):=by
    rw [←hp, show W.image _= (Pach (Θk cT x)) from cart_T (x:=x) (d:=24) (lt_trans (by decide) hX)]; exact (Finset.mem_filter.mp i.1.property).2
 intro j h; obtain ⟨a,u,t⟩:= Finset.mem_image.mp (hv (Finset.mem_image_of_mem (wrap _) h)); have hQ:= hX; exact cart_I 26 (show 26<cT.val from by omega) (cart_M (x:=x) (d:=26) (c:=24) u (by omega)) (deck_Q he _ h) t ▸ u -- tune hp direction rec
lemma Ω_seed (hX:300<cT.val) (i:StampSet cT x)(V:Pane k)(U: Pane cT)(h:Agrees (cartO x 24) (onC k V) (onC cT U)): (coupon (cT:=cT) x k i).raw V= Panorama (Θk cT x) U i:=by
 let P:= i.1.val; let z:=LiftSeat (cT:=cT) x i; let p:=P.2; have he: faceValue V (LiftK (cT:=cT) x k i)=faceValue U P:=by
    rw [LiftK,←onE,←show (wrap (More cT) z,p)=P from Prod.ext (prospect_eta ..) rfl, ←onE]; apply loopQ z p _; exact fun i u v=> h i (deck_R _ hX _ u) (deck_R _ hX _ v)
 change optic_Q (LiftK (cT:=cT) x k i) V i.2= optic_Q P U i.2; rw [optic_cost,optic_cost,he]
-- for P2 Adaptive read. constant pad for all arrangements.Version SoftBudget alternative union disjoint. Charges.
open Regis Regis.Head
abbrev stitch:= ∑ s:Signed,∑ p:PlaqAxes, (skewSlot SU.group (stab (p,none)) s).length
lemma stitch_l(s:Signed)(p:PlaqAxes):(skewSlot SU.group (stab (p,none)) s).length ≤ stitch:= (single_le_sum (f:=fun p:PlaqAxes=>(skewSlot SU.group (stab (p,none)) s).length) (fun _ _=>Nat.zero_le _) (mem_univ p)).trans (single_le_sum (f:=fun s:Signed=> ∑ p:PlaqAxes,(skewSlot SU.group (stab (p,none)) s).length) (fun _ _=>Nat.zero_le _) (mem_univ s))
abbrev temper:= 28+stitch -- Mark housing. new
lemma acclaim (S:Support (More k))(v:300<k.val)(u:knotX x temper k⊆S)(i:StampSet cT x): (coupon (cT:=cT) x k i).Compass S stitch:=by
 let f:=LiftK (cT:=cT) x k i; let A:= coupon (cT:=cT) x k i; let z:= f.1; let w:=wrap (More k) x; have he:z∈knotX x 24 k:=by
    rw [←cart_T (show 24<k.val from by omega)]; exact mem_image_of_mem _ ((prospect_R ..).2 (seat_e x i))
 have hp:separation w z≤24:=by simpa [knotX,halo_spec] using he
 constructor
 · apply u; exact halo_spec.mpr ⟨_,mem_singleton_self _,(hp.trans (by unfold temper; omega))⟩
 intro s; have hz:= stitch_l s f.2; refine ⟨hz,?_⟩
 let b:= (A.faceZ s).1; let Q:= affine s (0:Site (More k)); have hx:separation (Q z) b ≤ stitch:= (Work.E04.slot_separation (skewSlot SU.group A.axis s) (Q z)).trans hz
 let t:=s⁻¹.act b; have hf: Q t=b:=by simp [Q,t,affine]
 rw [← hf] at hx; have ht:separation z t≤ stitch:=by simpa [Q,affine] using hx
 exact mem_image.mpr ⟨t,u (halo_spec.mpr ⟨w,mem_singleton_self _,(separation_triangle w z t).trans ((add_le_add hp ht).trans (by unfold temper; omega))⟩),hf⟩
lemma can_D (S:Support (More k))(p:knotX x temper k⊆S): knotX x 24 k⊆ S:=by intro i u; obtain ⟨v,h,e⟩:=halo_spec.mp u; exact p (halo_spec.mpr ⟨v,h,e.trans (by unfold temper; omega)⟩)
lemma support_H (S:Support (More k))(v:300<k.val)(p:knotX x temper k⊆S){U:Pane k}(g:pingS h S U):pingV x 24 h (onC k U):=by rw [ping_W x 24 (by omega)]; exact fun i u=> g i (fun l=> u (disjoint_of_subset_left (can_D x k S p) l)) -- dots tune
-- build chest transplant su
lemma LensQ(hX:300<cT.val) (S:Support (More k))(v:300<k.val)(p:knotX x temper k⊆ S){U:Pane k}(u: chordK S U c): chordK (knotX x 24 cT) (knob cT x k U) c:=by
 rintro ⟨i,j⟩ h g; rw [knob_E]; let l:=(prospect x i); let Y:= cartO x 24; have hx:l∈Y:=(prospect_R _).2 h; have he := hX; have hy:l+step j∈Y:= by rw [← (show prospect x (i+step j)=l+step j from prospect_Q (show 24+1<cT.val from by omega) i j h)]; exact (prospect_R _).2 g
 let z:=wrap (More k) l; have hk(y:Cover)(V:y∈Y): wrap (More k) y∈S:=can_D x _ _ p ((cart_T (x:=x) (show 24<k.val from by omega)) ▸ mem_image_of_mem _ V)
 exact u _ (hk l hx) ((by have he:=hk _ hy; rwa [map_add,wrap_step] at he): (wrap (More k) l)+step j ∈ S) -- tune
lemma artery(hX:300<cT.val) {F:Paper cT} (L: Rules SU.group)(S:Support (More k))(U: Pane k)(v:300<k.val)(p:knotX x temper k⊆ S)(G:Genre)(g: MatPays F G (Θk cT x) r h)(hv:∀ i,LocalOn (Pach (Θk cT x)) (F i)) (hR:chordK S U c)(hc:0≤ c)(q:c≤ L.c)(e:2*c ≤ h)(hr:0≤ r):
   ∀ i:Wa cT, ‖F i (knob cT x k U)- crownx G F i (Θk cT x) (fun i:StampSet cT x=> (coupon (cT:=cT) x k i).raw U)‖ ≤ r*(2*c)^(G.orderB+1):=by
 intro i; let W:= knob cT x k U; let Z:= Θk cT x; have Hp:= LensQ (cT:=cT) x k hX S v p hR
 rw [show (fun i:StampSet cT x=> (coupon (cT:=cT) x k i).raw U)= Panorama Z W from funext fun i=> Ω_seed x k hX i U W (fun j p v=> (lamp_agree (x:=x) (n:=cT) U (lt_trans (by decide:24<300) hX) j p v).symm)]; let P(e:Edge (Site (More cT))):Prop:= e.1∈Pach Z∧e.1+Lattice.step e.2∈ Pach Z
 let Q:tangD cT:= fun i=>if P i then SU.group.plog (SU.group.mat (W i)) else 0; have hz(j)(f:P j): SU.group.chord (W j)≤ c:= Hp j f.1 f.2
 have hs: ‖Q‖ ≤ 2*c:=(pi_norm_le_iff_of_nonneg (by positivity:0≤ 2*c)).mpr fun i=>by
    unfold Q; split
    next p=> exact (L.sleeve _ ((hz i p).trans q)).trans (mul_le_mul_of_nonneg_left (hz i p) (by positivity))
    rw [norm_zero]; positivity
 have he: Agrees (Pach Z) W (increment 1 Q):=by
    intro i p t; unfold RG.increment Q; rw [if_pos (show P i from ⟨p,t⟩), L.records _ ((hz i ⟨p,t⟩).trans q),Pi.one_apply,mul_one]
 change ‖Tribute Z F G i W‖ ≤_; rw [orbit_run i F G hv W _ he]; apply (g.creds.Defect i Q (hs.trans e)).trans; gcongr
end ArtCart
end MastTin
end YM.CF.XGarden
end
