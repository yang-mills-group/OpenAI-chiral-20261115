import YM.CF.Esti.Acts
import YM.CF.Vol.Celt
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Psalm.Baton
import YM.CF.Palot.End
import YM.CF.Appel.Sat
import YM.Next.FLUCTUATIONS.Grants
import YM.PhysicalNext.V9_JOINT_ENDPOINT_LOAD.Folio.Wind
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.Esti
open Siete
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset MeasureTheory RG PhysicalNext.JointLoad Heir Next.Foundations AnalyticBridge.SectorAffine AnalyticBridge.SectorAffine.Offset Precision Tree Push.SectorMeasure AnalyticBridge.LocalGaussianLaws
open CF.Appel CF.Newt CF.Char CF.Neige CF.Summit Next Next.Fluctuations Next.SectorChange Next.SectorChange.Rows Next.SectorChange.Wisps Next.SectorChange.Schur MultiNext.SignedSource Lyre Banjo Analysis Pressure AnalyticBridge.MarginalMultiplier3b1d PatchReads SectorNext.Remainder SectorNext.Remainder.Scales Planned.AtomRegular Extra.Iteration Extra.Iteration.Scales
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open AnalyticBridge.Annulus1AD
open Ac
variable {c f:Side}(S:StepData c f){r v:ℕ}
open CF.Jet
local notation "G"=> SU.group
variable {S}{n:ℕ}{θ a b m x t w K C d:ℝ}
variable {K': Teller G}{A B:Stores S}{T:Tube G S}{V:Config G c}{U:Config G f}{k:S.Choices}{q:Chi}{E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][Nonempty E]{x':E}
open AnalyticBridge.Annulus1AD Push.SectorMeasure.Oriented Pressure.Tube
abbrev spanO (T:Tube G S)(x:ℝ):Prop:=∀ i:ℕ,fiery G x S.patch.L * Real.exp (i/T.high.relaxation) < 2→ i≤ radiusB x
lemma order_r (K:Teller G)(P:Patch):∀ᶠ x:ℝ in atTop,∀ {c f:Side}(S:StepData c f)(T:Tube G S), P=S.patch→K.Funds S T→ spanO T x:=by
 let d:=SU.group.slopeConstant*Real.log P.L.val; filter_upwards [Work.E04.eventually_room d K.top.clip.relaxation K.top.clip.radius_pos] with x hx c f S T h k i ht
 rw [k.high,←h] at ht; have he:=hx.2 i ht; omega
abbrev traceZ (x: Support c):Finset (Cell c):= univ.filter fun i=>i.1∈ x -- orientation known
abbrev prism (q:Chi)(k:S.Choices)(A:Stores S)(x a:ℝ)(U:Config G f)(s:Signed)(i:Bond c):= let z:= Inure A x q k a (sendEdge s 0 i) U; if s.flip i.2 then star z else z
abbrev layS (q:Chi)(k:S.Choices)(A:Stores S)(x a:ℝ)(U:Config G f)(V:Config G c)(s:Signed)(i:Bond c):=SU.group.mat (pull s 0 V i)*star (prism q k A x a U s i)
lemma pupil (s:Signed)(b:Bond c) (h: Inure A x q k a (sendEdge s 0 b) U=SU.group.mat (S.prediction U k (sendEdge s 0 b)))(hs:S.patch.Branches S.kernel G): layS q k A x a U V s b=wit (pull s 0 V) (S.prediction (pull s 0 U) (choice s k)) b:=by
 unfold wit; rw [(carry s hs k U).2]; change _=_; unfold layS prism; dsimp only; rw [h,SU.group.mat_mul, SU.group.mat_inv,Motion.turn_read (U:= (S.prediction U k)) s]; split <;> simp_all
abbrev caseP (T:Tube G S)(x:ℝ)(A:Stores S)(k:S.Choices)(q:Chi)(a:ℝ) (U:Config G f)(V:Config G c) (s:Signed)(p:Affine.Window S):ℝ:=ore T (Stores.till x) (fiery G x S.patch.L) (temp x) (turnStore s A).costs (traceZ (turnStore s A).flags) (pull s 0 V) (pull s 0 U) (layS q k A x a U V s) p
lemma keen(o:Site c)(x:Bond c)(S:Support c)(h:o∈S)(p:o∈pinPos x):x∈nearNoise S:=mem_filter.mpr ⟨mem_univ _,fun t=> Finset.disjoint_left.mp t p h⟩
lemma freshly (s:Signed)(b:Bond c)(hp:b∈nearNoise ((turnStore s A).dome r)): sendEdge s 0 b∈ nearNoise (A.dome r):=by
 obtain ⟨i,h,p⟩:=Finset.not_disjoint_iff.mp (mem_filter.mp hp).2; exact keen _ _ _ ((dome_turn ..).mp p) (pinPos_turn s b▸ Finset.mem_image_of_mem _ h) -- tune
variable {m v':ℕ}
lemma keeps_f (T:Tube G S)(U:E→ Config G f)(V:Config G c)(r N:ℕ)(h:Volo S n a b C θ)(hc:FuelG _ U x' n C)(s:Signed)(p:spanO T x)(ht:A.flags=RG.flags (temp x) V)(hv:shovel S.patch+10≤ radiusB x)(he:0<fiery G x S.patch.L)(hp:0<temp x)(ha:fiery G x S.patch.L≤a/2)(hw:r+5*radiusB x≤ N)(hs:S.patch.Branches S.kernel G)(l:total A x q (U x') (B.dome N)≠0): caseP T x A k q a (U x') V s (anchorage (turnStore s B) r)= (anchorage (turnStore s B) r).work T x (pull s 0 (U x')) (choice s k) (pull s 0 V):=by
 let X:=turnStore s A; let u:= pull s 0 (U x'); let D:= turnStore s B; let w:=pull s 0 V; let d:=radiusB x; let R:=r+2*d
 have tt: Stores.till x ≤ d:=by unfold Stores.till d; omega
 apply exact_o _ _ _ hp he -- params generate 4
 · intro i h; rw [traceZ]; exact mem_filter.mpr ⟨mem_univ _,(flag_turn ..).mpr (ht.symm ▸ (exact_turn ..).mp ((RG.flags_spec ..).mpr ⟨i, Work.E01.base_touched _,h⟩))⟩ -- tune
 · intro i hp; have hp : S.ratio.parent i.1∈D.dome r:=(mem_filter.mp hp).2; set t:=fiery G x S.patch.L
   have hz(j:Cell f)(v: t < Pressure.toll u j)(hj:separation i.1 j.1 ≤ d):j∈ X.costs:=by
      have hx : S.ratio.parent j.1∈ D.dome N:=by obtain ⟨j',u,t⟩:=halo_spec.mp hp; exact halo_spec.mpr ⟨j',u, (separation_triangle j' (S.ratio.parent i.1) _).trans (by have h:=Work.E04.parent_separation S.ratio i.1 j.1; unfold d at *; omega)⟩
      let j':= Face.send s 0 j; have hh: j' ∈ nearFace S (B.dome N):= Finset.mem_filter.mpr ⟨mem_univ _,fun l=> disjoint_left.mp l (show s.act (S.ratio.parent j.1) ∈ startPos S j' from startPos_turn s j ▸ mem_image_of_mem _ (mem_image_of_mem _ (Work.E01.base_touched j))) ((dome_turn ..).mp hx)⟩
      by_contra h; have h' : j'∉A.costs:=mt (costs_turn s A j).mpr h
      have hK:tokenF A q x (U x') j' ≠0:=fun u=>l (Finset.prod_eq_zero hh u); have hp: Pressure.toll (U x') j' < 2*(t/4):=(profile_charged _ _ _ (by change 0<t/4; positivity) _ hK (SU.group.chord_nonneg _)).2 h'
      rw [show Pressure.toll u j=Pressure.toll (U x') j' from Face.send_price (U x') j s 0 SU.group.chord SU.group.chord_inv fun k g => SU.group.chord_conj g k] at v; linarith only [hp,v,he] -- tune
   unfold spanO at p; refine ⟨persR _ _ _ _ _ he.le (fun j h=> hz j ?_ ?_), or_iff_not_imp_right.mpr (fun g=>hz i (lt_of_not_ge g) (by simp))⟩
   · exact lt_of_le_of_lt (le_mul_of_one_le_right he.le (Real.one_le_exp (by have hx:=T.high.radius_pos; positivity))) h
   exact p _ (h.trans_le (SU.group.chord_le_two _))
 · intro i hp; refine pupil s i ?_ hs; exact (capita A q k U x' hc B (B.dome N) (Finset.Subset.refl _) (show r+shovel S.patch≤N by omega) hv he ha h l _ (freshly _ _ (keen i.1 i _ (mem_filter.mp hp).2 (mem_insert_self ..)))).1
 intro i hp j u; refine pupil s j ?_ hs; apply (capita A q k U x' hc B (B.dome N) (Finset.Subset.refl _) (l:=(show R+shovel S.patch ≤ N by unfold R d; omega)) hv he ha h l _ ?_).1; apply freshly; refine keen j.1 _ _ ?_ (mem_insert_self ..)
 obtain ⟨z,v,ht⟩:=halo_spec.mp (show i.1∈ D.dome r from (mem_filter.mp hp).2); exact halo_spec.mpr ⟨z,v,(separation_triangle z i.1 _).trans (by rw [separation_comm j.1] at u; omega)⟩
end YM.CF.Esti
