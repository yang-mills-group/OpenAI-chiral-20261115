import YM.CF.Taxi.Sun
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option maxHeartbeats 860000
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Taxi
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open AnalyticBridge.Annulus1AD Ac Esti
open Atala Forge Cloak Rill Hive Fock Stilo Palot Scion
open Cube Lat Tenant Tulip
open Pastry Hake Levier Urn Peaks Fock Laic Branch Drapes
attribute [local instance] opCStarAlgebra
open Rush Scroll Paige Vault Phase Acorn Spire
attribute [local instance] opCStarAlgebra
open Tarn Cay Slate Esti Cour Hest Arena Reine Kennel Facet Broc Pec Push.SectorMeasure.Oriented
open Jet Yaw Nor Prism Font Push.AbsoluteSums Wray
variable{n:Side} {P: BudgetPoint}{x y a b h c d:ℝ}{k m:ℕ}
local notation "DN"=>tangD n
local notation "E'"=>SU.group
variable {X D Y Z:Support (More n)}{U:Pane n}
local notation "Ink" n=> Hake.Raid (Dwell n)
open Next.Foundations Push.Local AnalyticBridge.VerifiedReset RG.PathData Next.Scheduling UVNext.PricedKernels Work.F03 WilsonStartup Vow
open AnalyticBridge.GaussianFieldAlignment.Tensor AnalyticBridge.GaussianFieldAlignment.Locations AnalyticBridge.GaussianFieldAlignment.Channels
variable {p:Clip}(R: PathData SU.group)(V:Pane n)
variable (i:AnalyticBridge.VerifiedReset.Seat (More n))(b:AnalyticBridge.VerifiedReset.Low)
local notation "M_"=>Low.home R b P (0:Site (More n))
local notation "K_"=> AnalyticBridge.VerifiedReset.Seat.view i
local notation "Vi"=> AnalyticBridge.VerifiedReset.Seat.spread i
abbrev αX (i:AnalyticBridge.VerifiedReset.Seat (More n)):= turnSites i.1 i.2
abbrev seatY(i:AnalyticBridge.VerifiedReset.Seat (More n))(x: Pane n):= lifting (scatter i.1 i.2 x) (StepData.sendBonds i.1 i.2)
lemma seats(x:Support (More n)):Vi x=x.map (αX i).toEmbedding:= by rw [map_eq_image]; rfl
lemma seatsV(k:ℕ)(x:Support (More n)): Vi (halo k x)=halo k (Vi x):=Eq.symm (Push.Local.halo_map (αX i) (fun _ _=>turn_sep ..) k x)
local notation "Vo"=> K_ V
private lemma voiceU (e:Pressure.Bond (More n)):e∈unrest D P.B↔ sendEdge i.1 i.2 e∈unrest (Vi D) P.B:= by
 simp only [unrest, mem_filter, mem_univ,true_and]; rw [←seatsV, show Skye.ends (sendEdge i.1 i.2 e)= Vi (Skye.ends e) from ?_,seats,seats]; exact (Finset.disjoint_map _).symm; exact pin_map ..
lemma virtY (f: Pressure.Bond (More n))(z:tangD n): seatY i V (wakeB (unrest (Vi D) P.B) z) f=wakeB (unrest D P.B) (seatY i V z) f:=by rw [steadyB]; unfold seatY; rw [lifting_apply,steadyB]; split_ifs with g p p; exact (lifting_apply ..).symm; exact False.elim (p ((voiceU i f).2 g)); exact False.elim (g ((voiceU i f).1 p)); exact map_zero _ -- tune flag orientation
lemma volT(z:tangD n): pressQ P D Vo (seatY i V z)= K_ (pressQ P (Vi D) V z):=by
 unfold pressQ gyrate Function.comp Seat.view; rw [←insert_turn, ← map_smul (seatY i V)]; exact congrArg _ (funext fun y=> ((virtY V i y _).symm)) -- tune wrong order
variable (T:Ids n)
lemma pingI (Z:Support (More n)) : pingS P.threshold Z (AnalyticBridge.VerifiedReset.Seat.view i V) ↔ pingS P.threshold (Vi Z) V:=by
 let R:= shiftFaces i.1 i.2; have hp(a:Pressure.Cell (More n)): Pressure.toll (AnalyticBridge.VerifiedReset.Seat.view i V) a=Pressure.toll V (R a):= Face.send_price V a i.1 i.2 _ SU.group.chord_inv fun u w=>SU.group.chord_conj w u
 have he(a: Face (Per (More n))): Disjoint Z (touched a)↔ Disjoint (Vi Z) (touched (R a)):=by rw [seats,show touched (R a)=Vi _ from (Work.H03.touched_send i.1 i.2 a),seats]; exact (Finset.disjoint_map _).symm
 constructor
 · intro p a g; obtain ⟨a,rfl⟩:=R.surjective a; change Pressure.toll _ _<_; rw [←hp]; exact p _ ((he a).mp.mt g)
 intro p a g; change Pressure.toll _ _<_; rw [hp]; exact p _ ((he a).mpr.mt g)
lemma playF(x:tangD n): ‖seatY i V x‖ ≤ ‖x‖:=(pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun j=> by unfold seatY; rw [lifting_apply, LinearIsometry.norm_map]; exact norm_le_pi_norm ..
-- purchase $q=Y moves Masks.A p. no Π.COUNT. scalar ink.MO Att.
def herV (R:PathData SU.group)(p: Clip)(P:BudgetPoint)(i:AnalyticBridge.VerifiedReset.Seat (More n))(b:AnalyticBridge.VerifiedReset.Low)(Y:Support (More n))(U:Pane n): Cipher n:= loanW R p P (0:Site (More n)) b (Y.map (αX i).symm.toEmbedding) (i.view U, T) -- T external variable parameters? includes implicitly from section.
private lemma pearlK {S:Type}[NormedAddCommGroup S][NormedSpace ℝ S] (f:tangD n→ S)(L:Real)(z:tangD n)(p:Allows P.order f (seatY i V z) L): Allows P.order (fun q=> f (seatY i V q)) z (composeCost P.order L (‖z‖+1)):=by
 let Z:= (seatY i V).toContinuousLinearMap; have ht:0 ≤ ‖z‖:= norm_nonneg _; have hp:‖Z‖ ≤ 1:=by apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one; intro x; rw [one_mul]; exact playF V i x
 exact p.comp (f:=Z) (allows_linear (hp.trans (le_add_of_nonneg_left ht)) ((playF V i _).trans (le_add_of_nonneg_right zero_le_one)))
local notation "V'"=> (herV (p:=p)) -- unused
variable (Γ:ℝ)(p_:DayT P.order Γ)(ht:0≤Γ)(v:Decent p P)
-- packed α fee no c.i multiplier even after spin.Z.D.Law. Scalar Temp saturation. Loan identity emit all
lemma clay (D:Support (More n)): Vi (D.map (αX i).symm.toEmbedding)= D:=by rw [seats]; ext; simp
local notation "Yp"=> Y.map (αX i).symm.toEmbedding
include p_ ht v
abbrev bill_l (p: Clip)(Γ:ℝ)(P:BudgetPoint):ℝ:= (P.order+1:ℝ)*composeCost P.order ((P.order.factorial:ℝ)*1) 1 * glory_v R b p Γ P
private lemma cover_p : ThemeR (Vi M_) (oV (herV T R p P i b Y)):=by
 let K' :=meansB R (Y:=Yp) (0:Site (More n)) b Γ (h:=0) p_ ht v; let V:=loanW R p P (0:Site (More n)) b Yp
 let C (W:Pane n):ℝ:= b.live R p P 0 W - (if (0:Site (More n)) ∈ Yp then 0 else b.mark R p * b.proxy R 0 W)
 let A(W:Pane n):= Pastry.hollow (n:=Dwell n) (↑(C W))
 have he (W): V (W,T)=A W:=by unfold V A C loanW warmK; split_ifs; exact (sub_zero ..).trans (by simp); apply Subtype.ext; change ((_ :ℂ) • 1 - (_ :ℂ) • 1:FC (Dwell n))=_ • 1; rw [←sub_smul]; simp
 let Φ(W: Pane n):= V (W,T)
 let F:Pane n→Cipher n:=Φ ∘ K_
 have ha : GaugeInvariant Φ:=by intro g U; rw [show Φ _=V (Lattice.gauge g U,T) from rfl,he,show Φ U= V (U,T) from rfl,he]; unfold A C; rw [b.live_gauge R p 0 g U,b.proxy_gauge R 0 g U]
 have hl:Measurable F:= (K'.keeps.comp (show Measurable fun U:Pane n=>(U,T) from measurable_id.prodMk measurable_const)).comp (show Measurable (AnalyticBridge.VerifiedReset.Seat.view i (G:=SU.group)) from ?_); swap; · apply Continuous.measurable; change Continuous (Lattice.pull _ _); unfold Lattice.pull; apply continuous_pi; intro j; unfold Step.read; split <;> fun_prop
 -- Layout F may be scalar, Show fit.V All and commute
 have hu: ThemeR (Vi M_) (oV F):= by
    refine ⟨fun x y h g=> K'.same (K_ x.1,T) (K_ y.1,T) (agrees_pull i.1 i.2 h) (fun _ _=>rfl), fun jv=> ?_,(show Measurable (oV F) from hl.comp (f:=Prod.fst (β:=Ids n)) measurable_fst),fun W g=>?_⟩
    · let T':=K_ jv.1; change Flour _ (V (T',T)).val; rw [he]; exact Flour.grainE.smul _
    let T': InkD n:=Φ ∘ pull i.1 i.2; change F (Lattice.gauge g W.1)= paintR false false (tradew n g) (F W.1)
    rw [show F (Lattice.gauge g W.1)=F W.1 from Push.Local.invariant_pull ha i.1 i.2 g W.1,show F W.1 =A (K_ W.1) from he _]; apply Subtype.ext; exact Eq.symm ((twist_scalar _ _ _).trans (by rw [map_one]; rfl))
 exact hu
theorem vein_f : Medal P (Vi M_) Y (oV (herV T R p P i b Y)) h (bill_l R b p Γ P):=by
 let K' :=meansB R (Y:=Yp) (0:Site (More n)) b Γ (h:=h) p_ ht v; let V:=loanW R p P (0:Site (More n)) b Yp; have hx(W:Pane n)(T T':Ids n): V (W,T)= V (W,T'):=rfl
 let Φ(W: Pane n):= V (W,T); let hu:=cover_p (Y:=Y) R i b T Γ p_ ht v
 obtain ⟨q,hq,e,w⟩:= K'.pays; let B (x):= composeCost P.order ((P.order.factorial:ℝ)*x) 1; have hb:0 ≤ B 1:=by unfold B composeCost; positivity
 let U:ℝ:=P.order+1; refine ⟨hu,(fun i=>U*B (q i)),fun i=>mul_nonneg (show 0 ≤ U by unfold U; positivity) ?_,fun x h Z p=> ?_,?_ ⟩ -- tune
 · unfold B composeCost; exact mul_nonneg (mul_nonneg (by positivity) (mul_nonneg (by positivity) (hq i))) (pow_nonneg (by norm_num) _)
 · refine Rue.paidP _ _ fun a=>?_ ; let D:= Z.map (αX i).symm.toEmbedding; let A':Pane n:= K_ x.1; have hp:Yp ⊆ D:=map_subset_map.mpr p; have ht: pingS P.threshold (M_\Yp) A':= (pingI x.1 i _).2 ?_ -- tune have ?_
   swap; · rw [show Vi (M_\Yp)=(Vi M_)\Y from ?_]; exact h; rw [show Vi (M_\Yp)= Vi M_\Vi Yp from (by simp only [seats,Finset.map_sdiff]), clay]
   let f(u:DN):= crumb (Φ (pressQ P D A' u)).val a; have hk:= pearlK x.1 i f (P.order.factorial*q a) 0 ((map_zero (seatY i x.1)).symm ▸ ((e (A',T) ht hp).haveP a).pay); simp only [norm_zero,zero_add] at hk
   apply hk.germ (Eventually.of_forall fun z=>?_); change crumb (Φ (pressQ P D (K_ x.1) ((seatY i x.1) z))).val a=_; rw [volT]; change crumb (V ((K_ (pressQ P (Vi D) x.1 z)),T)).val a= _; rw [show Vi D=Z from clay i Z]; rfl
 change joinV _ _ ≤ _; unfold joinV; rw [show (∑ i:Finset (Dwell n), _)=(U*B 1)*joinV (stake h) q from (by unfold joinV; rw [mul_sum]; refine sum_congr rfl fun i _=> ?_; unfold B U composeCost; dsimp only; ring)]; exact mul_le_mul_of_nonneg_left w (mul_nonneg (by unfold U; positivity) hb)
end YM.CF.Taxi
